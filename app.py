from flask import Flask, render_template, request, send_file, abort, jsonify, Response
from pathlib import Path
import os
import re
import io
import zipfile
import mimetypes
import subprocess
import hashlib
import json
import time
import threading

app = Flask(__name__)

BASE_DIR = Path(__file__).resolve().parent
STORAGE = (BASE_DIR / "storage").resolve()
CACHE = (BASE_DIR / ".cache").resolve()
HLS_CACHE = CACHE / "hls"

CACHE.mkdir(exist_ok=True)
HLS_CACHE.mkdir(exist_ok=True)
STORAGE.mkdir(exist_ok=True)

VIDEO_EXTS = {
    ".mp4", ".m4v", ".mkv", ".webm", ".mov", ".avi", ".wmv",
    ".flv", ".ts", ".m2ts", ".mts", ".mpeg", ".mpg", ".3gp",
    ".ogv"
}

AUDIO_EXTS = {
    ".mp3", ".flac", ".wav", ".ogg", ".oga", ".opus", ".m4a",
    ".aac", ".wma", ".alac"
}

IMAGE_EXTS = {
    ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".svg", ".avif"
}

ARCHIVE_EXTS = {
    ".zip", ".rar", ".7z", ".tar", ".gz", ".bz2", ".xz",
    ".tar.gz", ".tar.xz"
}

BROWSER_VIDEO_EXTS = {
    ".mp4", ".webm", ".m4v", ".ogv"
}

VIDEO_MIMETYPES = {
    ".mp4": "video/mp4",
    ".m4v": "video/mp4",
    ".webm": "video/webm",
    ".ogv": "video/ogg",
    ".mkv": "video/x-matroska",
    ".mov": "video/quicktime",
    ".avi": "video/x-msvideo",
    ".ts": "video/mp2t",
    ".m2ts": "video/mp2t",
    ".mts": "video/mp2t",
    ".mpeg": "video/mpeg",
    ".mpg": "video/mpeg"
}

TRANSCODE_PROFILES = {
    "1080": {
        "height": 1080,
        "video_bitrate": "5000k",
        "audio_bitrate": "192k"
    },
    "720": {
        "height": 720,
        "video_bitrate": "3000k",
        "audio_bitrate": "160k"
    },
    "480": {
        "height": 480,
        "video_bitrate": "1500k",
        "audio_bitrate": "128k"
    }
}

SEASON_EP_RE = re.compile(
    r"(?i)"
    r"(?:"
    r"s(?:eason)?[\s._-]*(\d{1,3})[\s._-]*"
    r"(?:e|ep|episode)[\s._-]*(\d{1,4})"
    r"|"
    r"s[\s._-]*(\d{1,3})[\s._-]*"
    r"e[\s._-]*(\d{1,4})"
    r"|"
    r"(\d{1,3})x(\d{1,4})"
    r")"
)

EP_RE = re.compile(
    r"(?i)(?:^|[\s._\-[\]()])"
    r"(?:ep|episode)[\s._-]*(\d{1,4})"
    r"(?:$|[\s._\-[\]()])"
)

NUMBER_PREFIX_RE = re.compile(
    r"^\s*(\d{1,5})(?:[\s._-]+|$)"
)

NUMBER_SUFFIX_RE = re.compile(
    r"(?:^|[\s._-]+)(\d{1,5})\s*$"
)

_ffmpeg_cache = None
_ffmpeg_lock = threading.Lock()
_hls_jobs = {}
_hls_jobs_lock = threading.Lock()


def safe_path(rel_path=""):
    rel_path = rel_path or ""
    rel_path = rel_path.replace("\\", "/").strip("/")

    candidate = (STORAGE / rel_path).resolve()

    try:
        candidate.relative_to(STORAGE)
    except ValueError:
        abort(404)

    return candidate


def clean_name(name):
    return name.startswith(".")


def classify(path):
    if path.is_dir():
        return "dir"

    ext = path.suffix.lower()

    if ext in VIDEO_EXTS:
        return "video"

    if ext in AUDIO_EXTS:
        return "audio"

    if ext in IMAGE_EXTS:
        return "image"

    if ext in ARCHIVE_EXTS or path.name.lower().endswith(
        (".tar.gz", ".tar.xz")
    ):
        return "archive"

    return "file"


def human_size(size):
    size = float(size)
    units = ["B", "KB", "MB", "GB", "TB", "PB"]

    for unit in units:
        if size < 1024 or unit == units[-1]:
            if unit == "B":
                return f"{int(size)} B"
            return f"{size:.1f} {unit}"
        size /= 1024

    return "0 B"


def folder_stats(folder):
    files = 0
    directories = 0
    total_size = 0

    try:
        for root, dirs, filenames in os.walk(folder):
            dirs[:] = [
                d for d in dirs
                if not d.startswith(".")
            ]

            visible_files = [
                f for f in filenames
                if not f.startswith(".")
            ]

            directories += len(dirs)
            files += len(visible_files)

            for filename in visible_files:
                path = Path(root) / filename

                try:
                    if path.is_file():
                        total_size += path.stat().st_size
                except (OSError, PermissionError):
                    continue

    except (OSError, PermissionError):
        pass

    return {
        "files": files,
        "directories": directories,
        "size": total_size,
        "size_text": human_size(total_size)
    }


def folder_size(folder):
    return folder_stats(folder)["size"]


def get_size(path):
    try:
        if path.is_file():
            return path.stat().st_size

        if path.is_dir():
            return folder_size(path)

    except (OSError, PermissionError):
        pass

    return 0


def media_number(name):
    stem = Path(name).stem

    match = SEASON_EP_RE.search(stem)

    if match:
        values = [
            int(value)
            for value in match.groups()
            if value is not None
        ]

        if len(values) >= 2:
            season = values[-2]
            episode = values[-1]

            return (
                0,
                season,
                episode,
                stem.lower()
            )

    match = EP_RE.search(stem)

    if match:
        return (
            1,
            0,
            int(match.group(1)),
            stem.lower()
        )

    prefix = NUMBER_PREFIX_RE.search(stem)

    if prefix:
        return (
            2,
            int(prefix.group(1)),
            0,
            stem.lower()
        )

    suffix = NUMBER_SUFFIX_RE.search(stem)

    if suffix:
        return (
            3,
            int(suffix.group(1)),
            0,
            stem.lower()
        )

    return (
        9,
        999999,
        999999,
        stem.lower()
    )


def item_info(path):
    kind = classify(path)
    size = get_size(path)
    relative = path.relative_to(STORAGE).as_posix()

    if path.is_dir():
        browse_url = "/browse/" + relative
        download_url = None
        preview_url = None
        zip_url = "/zip/" + relative
    else:
        browse_url = None
        download_url = "/download/" + relative

        preview_url = (
            "/stream/" + relative
            if kind in {"video", "audio", "image"}
            else None
        )

        zip_url = None

    order = media_number(path.name)

    return {
        "name": path.name,
        "fullpath": relative,
        "type": "dir" if path.is_dir() else "file",
        "kind": kind,
        "size": size,
        "size_text": human_size(size),
        "browse_url": browse_url,
        "download_url": download_url,
        "preview_url": preview_url,
        "zip_url": zip_url,
        "season": (
            order[1]
            if order[0] == 0
            else None
        ),
        "episode": (
            order[2]
            if order[0] in {0, 1}
            else None
        ),
        "order_key": order
    }


def list_items(folder):
    try:
        children = list(folder.iterdir())
    except (OSError, PermissionError):
        return []

    return [
        child
        for child in children
        if not child.name.startswith(".")
    ]


def smart_sort(paths):
    def key(path):
        if path.is_dir():
            return (
                0,
                999999,
                999999,
                path.name.lower()
            )

        order = media_number(path.name)

        return (
            1,
            *order
        )

    return sorted(paths, key=key)


def make_crumbs(rel_path):
    crumbs = []
    current = ""

    for part in Path(rel_path).parts:
        current = f"{current}/{part}".strip("/")

        crumbs.append({
            "name": part,
            "path": current
        })

    return crumbs


def ffmpeg_available():
    global _ffmpeg_cache

    if _ffmpeg_cache is not None:
        return _ffmpeg_cache

    with _ffmpeg_lock:
        if _ffmpeg_cache is not None:
            return _ffmpeg_cache

        try:
            result = subprocess.run(
                ["ffmpeg", "-version"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=5
            )

            _ffmpeg_cache = result.returncode == 0

        except Exception:
            _ffmpeg_cache = False

    return _ffmpeg_cache


def ffprobe_available():
    try:
        result = subprocess.run(
            ["ffprobe", "-version"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=5
        )

        return result.returncode == 0

    except Exception:
        return False


def cache_name(path, suffix=""):
    stat = path.stat()

    raw = (
        f"{path}:{stat.st_size}:"
        f"{stat.st_mtime_ns}:{suffix}"
    ).encode()

    return hashlib.sha256(raw).hexdigest()


def ffprobe_video(path):
    if not ffprobe_available():
        return {}

    try:
        result = subprocess.run(
            [
                "ffprobe",
                "-v", "error",
                "-select_streams", "v:0",
                "-show_entries",
                "stream=codec_name,width,height,r_frame_rate",
                "-of", "json",
                str(path)
            ],
            capture_output=True,
            text=True,
            timeout=20
        )

        if result.returncode != 0:
            return {}

        data = json.loads(result.stdout)
        streams = data.get("streams", [])

        if not streams:
            return {}

        stream = streams[0]

        width = stream.get("width")
        height = stream.get("height")
        codec = stream.get("codec_name")
        fps = stream.get("r_frame_rate")

        return {
            "codec": codec,
            "width": width,
            "height": height,
            "fps": fps
        }

    except Exception:
        return {}


def ffprobe_codecs(path):
    if not ffprobe_available():
        return []

    try:
        result = subprocess.run(
            [
                "ffprobe",
                "-v", "error",
                "-show_entries",
                "stream=codec_type,codec_name",
                "-of", "json",
                str(path)
            ],
            capture_output=True,
            text=True,
            timeout=20
        )

        if result.returncode != 0:
            return []

        data = json.loads(result.stdout)
        return data.get("streams", [])

    except Exception:
        return []


def get_video_tracks(path):
    """Extract audio and subtitle track information from video file."""
    if not ffprobe_available():
        return {"audio": [], "subtitles": []}

    try:
        result = subprocess.run(
            [
                "ffprobe",
                "-v", "error",
                "-show_entries",
                "stream=index,codec_type,codec_name,channels,channel_layout,disposition"
                ":stream_tags=language,title,handler_name",
                "-of", "json",
                str(path)
            ],
            capture_output=True,
            text=True,
            timeout=20
        )

        if result.returncode != 0:
            return {"audio": [], "subtitles": []}

        data = json.loads(result.stdout)
        streams = data.get("streams", [])

        audio_tracks = []
        subtitle_tracks = []
        default_audio_index = None

        for stream in streams:
            codec_type = stream.get("codec_type")
            codec_name = stream.get("codec_name", "unknown")
            tags = stream.get("tags", {})
            language = tags.get("language", "und").lower()
            title = tags.get("title", "")
            handler_name = tags.get("handler_name", "")
            disposition = stream.get("disposition", {})
            language_names = {
                "en": "English",
                "eng": "English",
                "ja": "Japanese",
                "jpn": "Japanese",
                "es": "Spanish",
                "spa": "Spanish",
                "fr": "French",
                "fra": "French",
                "de": "German",
                "deu": "German",
                "it": "Italian",
                "ita": "Italian",
                "ko": "Korean",
                "kor": "Korean",
            }
            language_label = language_names.get(
                language,
                "Language not tagged" if language in {"", "und"} else language.upper()
            )

            if codec_type == "audio":
                track_number = len(audio_tracks) + 1
                channels = stream.get("channels")
                channel_layout = stream.get("channel_layout", "")
                channel_text = (
                    f" - {channel_layout}"
                    if channel_layout
                    else f" - {channels}ch" if channels else ""
                )
                title_text = f" - {title or handler_name}" if title or handler_name else ""
                status_text = " - Default" if disposition.get("default") else ""
                audio_label = (
                    f"Audio {track_number} - "
                    f"{language_label} - {codec_name}"
                    f"{channel_text}{title_text}{status_text}"
                )
                audio_tracks.append({
                    "index": track_number - 1,
                    "stream_index": stream.get("index"),
                    "codec": codec_name,
                    "language": language,
                    "language_label": language_label,
                    "title": title,
                    "default": bool(disposition.get("default")),
                    "label": audio_label
                })

                language_key = language.lower().replace("_", "-")
                title_key = title.lower()
                if (
                    default_audio_index is None
                    and (
                        language_key in {"en", "eng", "en-us", "en-gb"}
                        or "english" in title_key
                    )
                ):
                    default_audio_index = track_number - 1
                elif (
                    default_audio_index is None
                    and disposition.get("default")
                ):
                    default_audio_index = track_number - 1

            elif codec_type == "subtitle":
                track_number = len(subtitle_tracks) + 1
                title_text = f" - {title or handler_name}" if title or handler_name else ""
                status_text = " - Forced" if disposition.get("forced") else ""
                if disposition.get("hearing_impaired"):
                    status_text += " - SDH"
                subtitle_label = (
                    f"Subtitle {track_number} - "
                    f"{language_label} - {codec_name}{title_text}{status_text}"
                )
                subtitle_tracks.append({
                    "index": track_number - 1,
                    "stream_index": stream.get("index"),
                    "codec": codec_name,
                    "language": language,
                    "language_label": language_label,
                    "title": title,
                    "forced": bool(disposition.get("forced")),
                    "label": subtitle_label
                })

        return {
            "audio": audio_tracks,
            "subtitles": subtitle_tracks,
            "default_audio_index": default_audio_index
        }

    except Exception:
        return {"audio": [], "subtitles": []}


def has_browser_codecs(path):
    streams = ffprobe_codecs(path)
    video_codecs = {
        stream.get("codec_name", "").lower()
        for stream in streams
        if stream.get("codec_type") == "video"
    }
    audio_codecs = {
        stream.get("codec_name", "").lower()
        for stream in streams
        if stream.get("codec_type") == "audio"
    }

    return (
        video_codecs <= {"h264", "avc1"}
        and audio_codecs <= {"aac", "mp3"}
        and bool(video_codecs)
    )


def has_browser_video_codec(path):
    return any(
        stream.get("codec_type") == "video"
        and stream.get("codec_name", "").lower() in {"h264", "avc1"}
        for stream in ffprobe_codecs(path)
    )


def stream_fragmented_mp4(path, audio_stream=None):
    command = [
        "ffmpeg",
        "-v", "error",
        "-i", str(path),
        "-map", "0:v:0",
        "-map", f"0:{audio_stream}" if audio_stream is not None else "0:a:0",
        "-c:v", "copy",
        "-c:a", "aac", "-profile:a", "aac_low", "-ac", "2",
        "-b:a", "192k",
        "-movflags", "frag_keyframe+empty_moov+default_base_moof",
        "-f", "mp4",
        "pipe:1"
    ]

    try:
        process = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL
        )

        def chunks():
            try:
                while True:
                    chunk = process.stdout.read(1024 * 1024)
                    if not chunk:
                        break
                    yield chunk
            finally:
                if process.poll() is None:
                    process.terminate()
                process.wait()

        return Response(
            chunks(),
            mimetype="video/mp4",
            headers={
                "Content-Disposition": "inline",
                "Cache-Control": "no-cache",
                "X-Accel-Buffering": "no"
            }
        )

    except OSError:
        return None


def is_browser_friendly_video(path):
    ext = path.suffix.lower()

    if ext == ".webm":
        return True

    if ext not in {".mp4", ".m4v", ".mov"}:
        return False

    return has_browser_codecs(path)


def remux_mp4(path, audio_stream=None):
    suffix = f"remux-audio-{audio_stream}" if audio_stream is not None else "remux"
    key = cache_name(path, suffix)
    output = CACHE / f"{key}.mp4"

    if output.exists() and output.stat().st_size > 0:
        return output

    temp = CACHE / f"{key}.tmp.mp4"

    command = [
        "ffmpeg",
        "-y",
        "-i", str(path),
        "-map", "0:v:0",
        "-map", f"0:{audio_stream}" if audio_stream is not None else "0:a?",
        "-c", "copy",
        "-movflags", "+faststart",
        str(temp)
    ]

    try:
        result = subprocess.run(
            command,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            timeout=3600
        )

        if result.returncode != 0:
            temp.unlink(missing_ok=True)
            return None

        temp.replace(output)
        return output

    except Exception:
        temp.unlink(missing_ok=True)
        return None


def transcode_mp4(path, profile, audio_stream=None):
    if profile != "original" and profile not in TRANSCODE_PROFILES:
        return None

    settings = TRANSCODE_PROFILES.get(profile)

    suffix = f"mp4-{profile}-audio-{audio_stream}-v3" if audio_stream is not None else f"mp4-{profile}-v3"
    key = cache_name(path, suffix)
    output = CACHE / f"{key}-{profile}p.mp4"

    if output.exists() and output.stat().st_size > 0:
        return output

    temp = CACHE / f"{key}-{profile}p.tmp.mp4"

    copy_video = profile == "original" and has_browser_video_codec(path)
    command = [
        "ffmpeg",
        "-y",
        "-i", str(path),
        "-map", "0:v:0",
        "-map", f"0:{audio_stream}" if audio_stream is not None else "0:a?",
        "-c:v", "copy" if copy_video else "libx264",
        "-c:a", "aac",
        "-b:a", settings["audio_bitrate"] if settings else "192k",
        "-movflags", "+faststart",
        str(temp)
    ]

    if not copy_video:
        command[10:10] = [
            "-preset", "veryfast",
            "-crf", "23"
        ]

    if settings:
        command[10:10] = [
            "-vf",
            (
                f"scale=-2:{settings['height']}:"
                f"force_original_aspect_ratio=decrease"
            ),
            "-maxrate", settings["video_bitrate"],
            "-bufsize", settings["video_bitrate"]
        ]

    try:
        result = subprocess.run(
            command,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            timeout=7200
        )

        if result.returncode != 0:
            temp.unlink(missing_ok=True)
            return None

        temp.replace(output)
        return output

    except Exception:
        temp.unlink(missing_ok=True)
        return None


def browser_video(path, audio_stream=None):
    if is_browser_friendly_video(path):
        return path

    if not ffmpeg_available():
        return None

    if has_browser_codecs(path) and audio_stream is None:
        return remux_mp4(path)

    # Copy compatible video and convert only incompatible audio when possible.
    return transcode_mp4(path, "original", audio_stream)


def hls_directory(path, profile, audio_stream=None):
    if profile not in TRANSCODE_PROFILES and profile != "original":
        profile = "720"

    suffix = f"hls-v2-{profile}-audio-{audio_stream}" if audio_stream is not None else f"hls-v2-{profile}"
    key = cache_name(path, suffix)
    directory = HLS_CACHE / f"{key}-{profile}"

    directory.mkdir(
        parents=True,
        exist_ok=True
    )

    playlist = directory / "index.m3u8"

    if playlist.exists() and playlist.stat().st_size > 0:
        return directory

    temp_playlist = playlist

    settings = TRANSCODE_PROFILES.get(profile, TRANSCODE_PROFILES["1080"])
    copy_video = profile == "original" and has_browser_video_codec(path)

    command = [
        "ffmpeg", "-y", "-probesize", "10M", "-analyzeduration", "1M",
        "-i", str(path),
        "-map", "0:v:0",
        "-map", f"0:{audio_stream}" if audio_stream is not None else "0:a:0",
        "-c:v", "copy" if copy_video else "libx264",
        "-c:a", "aac", "-profile:a", "aac_low", "-ac", "2",
        "-b:a", settings["audio_bitrate"],
        "-f", "hls", "-hls_time", "2",
        "-hls_playlist_type", "event",
        "-hls_flags", "independent_segments+append_list",
        "-hls_segment_type", "fmp4",
        "-hls_fmp4_init_filename", "init.mp4",
        "-hls_segment_filename", str(directory / "segment_%05d.m4s"),
        str(temp_playlist)
    ]

    if not copy_video:
        command[10:10] = [
            "-vf",
            (
                f"scale=-2:{settings['height']}:"
                f"force_original_aspect_ratio=decrease"
            ),
            "-preset", "veryfast", "-crf", "23",
            "-maxrate", settings["video_bitrate"],
            "-bufsize", settings["video_bitrate"]
        ]

    try:
        result = subprocess.run(
            command,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            timeout=7200
        )

        if result.returncode != 0:
            temp_playlist.unlink(missing_ok=True)
            return None

        return directory

    except Exception:
        temp_playlist.unlink(missing_ok=True)
        return None


def start_hls_job(path, profile, audio_stream=None):
    suffix = f"hls-v2-{profile}-audio-{audio_stream}" if audio_stream is not None else f"hls-v2-{profile}"
    key = cache_name(path, suffix)
    job_key = f"{key}-{profile}"

    with _hls_jobs_lock:
        if job_key in _hls_jobs:
            return
        _hls_jobs[job_key] = True

    def generate():
        try:
            hls_directory(path, profile, audio_stream)
        finally:
            with _hls_jobs_lock:
                _hls_jobs.pop(job_key, None)

    threading.Thread(target=generate, daemon=True).start()


@app.route("/api/browser-friendly/<path:req_path>")
def check_browser_friendly(req_path):
    path = safe_path(req_path)
    
    if not path.exists() or not path.is_file():
        return jsonify({"friendly": False, "format": None})
    
    ext = path.suffix.lower()
    
    # Check if format is browser-playable natively
    friendly = ext in BROWSER_VIDEO_EXTS
    
    return jsonify({
        "friendly": friendly,
        "format": ext,
        "requires_remux": not friendly and ext in VIDEO_EXTS
    })


@app.route("/favicon.ico")
def favicon():
    from flask import make_response
    svg = b'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100"><text y="75" font-size="75">\xf0\x9f\x8e\xac</text></svg>'
    response = make_response(svg)
    response.headers["Content-Type"] = "image/svg+xml"
    response.headers["Cache-Control"] = "public, max-age=86400"
    return response


@app.template_filter("filesize")
def filesize_filter(value):
    return human_size(value)


@app.route("/")
def home():
    stats = folder_stats(STORAGE)

    folders = []

    for path in list_items(STORAGE):
        if path.is_dir():
            folders.append(item_info(path))

    folders.sort(
        key=lambda item: media_number(item["name"])
    )

    return render_template(
        "index.html",
        dashboard=True,
        items=[],
        folders=folders,
        path="",
        crumbs=[],
        q="",
        kind="all",
        sort="episode",
        order="asc",
        stats=stats,
        error=None
    )


@app.route("/browse/")
@app.route("/browse/<path:req_path>")
def index(req_path=""):
    folder = safe_path(req_path)

    if not folder.exists() or not folder.is_dir():
        abort(404)

    q = request.args.get("q", "").strip()
    kind_filter = request.args.get("kind", "all")
    sort = request.args.get("sort", "episode")
    order = request.args.get("order", "asc")

    paths = list_items(folder)

    if q:
        query = q.lower()

        paths = [
            path
            for path in paths
            if query in path.name.lower()
        ]

    if kind_filter != "all":
        if kind_filter == "dir":
            paths = [
                path
                for path in paths
                if path.is_dir()
            ]

        elif kind_filter == "file":
            paths = [
                path
                for path in paths
                if path.is_file()
            ]

        elif kind_filter in {
            "video",
            "audio",
            "image",
            "archive"
        }:
            paths = [
                path
                for path in paths
                if (
                    path.is_file()
                    and classify(path) == kind_filter
                )
            ]

    if sort == "name":
        paths.sort(
            key=lambda path: path.name.lower()
        )

    elif sort == "size":
        paths.sort(
            key=get_size
        )

    elif sort == "type":
        paths.sort(
            key=lambda path: (
                classify(path),
                path.name.lower()
            )
        )

    elif sort == "episode":
        paths = smart_sort(paths)

    elif sort == "season":
        paths.sort(
            key=lambda path: (
                media_number(path.name)[1],
                media_number(path.name)[2],
                path.name.lower()
            )
        )

    elif sort == "extension":
        paths.sort(
            key=lambda path: (
                path.suffix.lower(),
                path.name.lower()
            )
        )

    if order == "desc":
        paths.reverse()

    items = []

    for index, path in enumerate(paths):
        item = item_info(path)
        item["order_index"] = index
        items.append(item)

    stats = folder_stats(folder)

    return render_template(
        "index.html",
        dashboard=False,
        items=items,
        folders=[],
        path=req_path,
        crumbs=make_crumbs(req_path),
        q=q,
        kind=kind_filter,
        sort=sort,
        order=order,
        stats=stats,
        error=None
    )


@app.route("/download/<path:req_path>")
def download(req_path):
    path = safe_path(req_path)

    if (
        not path.exists()
        or not path.is_file()
        or path.name.startswith(".")
    ):
        abort(404)

    return send_file(
        path,
        as_attachment=True,
        download_name=path.name,
        conditional=True,
        max_age=0
    )


@app.route("/stream/<path:req_path>")
def stream(req_path):
    path = safe_path(req_path)

    if (
        not path.exists()
        or not path.is_file()
        or path.name.startswith(".")
    ):
        abort(404)

    kind = classify(path)

    profile = request.args.get("profile", "original").lower()
    audio_stream = request.args.get("audio", type=int)

    if kind == "video":

        if (
            profile == "original"
            and not is_browser_friendly_video(path)
            and has_browser_video_codec(path)
        ):
            streamed = stream_fragmented_mp4(path, audio_stream)
            if streamed is not None:
                return streamed

        if profile in TRANSCODE_PROFILES:
            converted = transcode_mp4(
                path,
                profile,
                audio_stream
            )

            if not converted:
                return jsonify({
                    "error": "Video conversion failed"
                }), 503

            path = converted

        else:
            playable = browser_video(path, audio_stream)
            if not playable:
                return jsonify({
                    "error": "Video conversion failed"
                }), 503

            path = playable

    mimetype = mimetypes.guess_type(
        path.name
    )[0]

    if not mimetype:
        ext = path.suffix.lower()

        if ext in VIDEO_MIMETYPES:
            mimetype = VIDEO_MIMETYPES[ext]

        elif kind == "video":
            mimetype = "video/mp4"

        elif kind == "audio":
            mimetype = "audio/mpeg"

        elif kind == "image":
            mimetype = "application/octet-stream"

        else:
            mimetype = "application/octet-stream"

    return send_file(
        path,
        mimetype=mimetype,
        conditional=True,
        max_age=0
    )


@app.route("/subtitle/<path:req_path>/<int:stream_index>.vtt")
def subtitle(req_path, stream_index):
    path = safe_path(req_path)

    if (
        not path.exists()
        or not path.is_file()
        or classify(path) != "video"
    ):
        abort(404)

    tracks = get_video_tracks(path)["subtitles"]
    if not any(track["stream_index"] == stream_index for track in tracks):
        abort(404)

    result = subprocess.run(
        [
            "ffmpeg", "-v", "error", "-i", str(path),
            "-map", f"0:{stream_index}", "-f", "webvtt", "pipe:1"
        ],
        capture_output=True,
        timeout=120
    )

    if result.returncode != 0:
        abort(500)

    return Response(
        result.stdout,
        mimetype="text/vtt",
        headers={"Cache-Control": "public, max-age=3600"}
    )


@app.route("/hls/<path:req_path>/")
def hls_playlist(req_path):
    path = safe_path(req_path)

    if (
        not path.exists()
        or not path.is_file()
        or path.name.startswith(".")
        or classify(path) != "video"
    ):
        abort(404)

    profile = request.args.get(
        "profile",
        "720"
    ).lower()
    audio_stream = request.args.get("audio", type=int)

    if audio_stream is None:
        track_data = get_video_tracks(path)
        default_index = track_data.get("default_audio_index")
        audio_tracks = track_data.get("audio", [])
        if default_index is not None and default_index < len(audio_tracks):
            audio_stream = audio_tracks[default_index]["stream_index"]

    start_hls_job(path, profile, audio_stream)
    suffix = f"hls-v2-{profile}-audio-{audio_stream}" if audio_stream is not None else f"hls-v2-{profile}"
    key = cache_name(path, suffix)
    directory = HLS_CACHE / f"{key}-{profile}"

    if directory is None:
        abort(500)

    playlist = directory / "index.m3u8"

    if not playlist.exists():
        return jsonify({"status": "preparing"}), 202

    playlist_text = playlist.read_text(encoding="utf-8")
    segment_query = f"profile={profile}"
    if audio_stream is not None:
        segment_query += f"&audio={audio_stream}"

    playlist_lines = []
    for line in playlist_text.splitlines():
        if line and not line.startswith("#"):
            separator = "&" if "?" in line else "?"
            line = f"{line}{separator}{segment_query}"
        playlist_lines.append(line)

    return Response(
        "\n".join(playlist_lines) + "\n",
        mimetype="application/vnd.apple.mpegurl",
        headers={"Cache-Control": "no-cache"}
    )


@app.route("/hls/<path:req_path>/<filename>")
def hls_segment(req_path, filename):
    path = safe_path(req_path)

    if (
        not path.exists()
        or not path.is_file()
        or path.name.startswith(".")
        or classify(path) != "video"
    ):
        abort(404)

    profile = request.args.get(
        "profile",
        "720"
    ).lower()
    audio_stream = request.args.get("audio", type=int)

    directory = hls_directory(path, profile, audio_stream)

    if directory is None:
        abort(500)

    requested = Path(filename).name

    if requested != filename:
        abort(404)

    segment = directory / requested

    if (
        not segment.exists()
        or not segment.is_file()
    ):
        abort(404)

    return send_file(
        segment,
        mimetype=(
            "video/mp2t"
            if segment.suffix.lower() == ".ts"
            else "video/mp4"
            if segment.suffix.lower() in {".mp4", ".m4s"}
            else "application/vnd.apple.mpegurl"
        ),
        conditional=True,
        max_age=3600
    )


@app.route("/open/<path:req_path>")
def open_file(req_path):
    path = safe_path(req_path)

    if (
        not path.exists()
        or path.name.startswith(".")
    ):
        abort(404)

    if path.is_dir():
        return index(req_path)

    kind = classify(path)

    if kind in {
        "video",
        "audio",
        "image"
    }:
        return stream(req_path)

    return download(req_path)


@app.route("/zip/<path:req_path>")
def zip_folder(req_path):
    folder = safe_path(req_path)

    if (
        not folder.exists()
        or not folder.is_dir()
        or folder.name.startswith(".")
    ):
        abort(404)

    memory = io.BytesIO()

    with zipfile.ZipFile(
        memory,
        "w",
        compression=zipfile.ZIP_DEFLATED,
        compresslevel=6
    ) as archive:

        for root, dirs, files in os.walk(folder):
            dirs[:] = [
                directory
                for directory in dirs
                if not directory.startswith(".")
            ]

            files = [
                filename
                for filename in files
                if not filename.startswith(".")
            ]

            root_path = Path(root)

            for filename in files:
                source = root_path / filename

                try:
                    relative = source.relative_to(
                        folder
                    ).as_posix()

                    archive.write(
                        source,
                        relative
                    )

                except (
                    OSError,
                    ValueError
                ):
                    continue

    memory.seek(0)

    safe_name = folder.name or "storage"

    return send_file(
        memory,
        mimetype="application/zip",
        as_attachment=True,
        download_name=f"{safe_name}.zip",
        max_age=0
    )


@app.route("/api/info/<path:req_path>")
def api_info(req_path):
    path = safe_path(req_path)

    if (
        not path.exists()
        or path.name.startswith(".")
    ):
        abort(404)

    size = get_size(path)

    return jsonify({
        "name": path.name,
        "type": (
            "directory"
            if path.is_dir()
            else "file"
        ),
        "kind": classify(path),
        "size": size,
        "size_text": human_size(size)
    })


@app.route("/api/tracks/<path:req_path>")
def api_tracks(req_path):
    """Get audio and subtitle tracks for a video file."""
    path = safe_path(req_path)

    if (
        not path.exists()
        or not path.is_file()
        or path.name.startswith(".")
        or classify(path) != "video"
    ):
        abort(404)

    tracks = get_video_tracks(path)

    return jsonify(tracks)


@app.errorhandler(404)
def not_found(error):
    return render_template(
        "index.html",
        dashboard=False,
        items=[],
        folders=[],
        path="",
        crumbs=[],
        q="",
        kind="all",
        sort="episode",
        order="asc",
        stats={
            "files": 0,
            "directories": 0,
            "size": 0,
            "size_text": "0 B"
        },
        error="File or folder not found."
    ), 404


if __name__ == "__main__":
    app.run(
        host="0.0.0.0",
        port=5001,
        threaded=True
    )
