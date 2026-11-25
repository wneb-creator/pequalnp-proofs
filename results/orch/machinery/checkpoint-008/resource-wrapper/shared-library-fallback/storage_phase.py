"""Reviewed storage extension candidate; activation requires independent review.

The caller must establish the reviewed native-only handoff and mapper quiescence.
This prototype adds exact, hash-pinned library files and explicitly selected
manifest-backed core files to the original lossless transaction machinery.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys

BASE = Path(__file__).resolve().parent
SOURCE_SHA256 = "a43b13fa9556910376ae08131bbc8228b8318be81ab986f74a9ddf4427f1feb2"
source = BASE / "storage_phase_base.py"
if hashlib.sha256(source.read_bytes()).hexdigest() != SOURCE_SHA256:
    raise RuntimeError("reviewed base storage source changed")
spec = importlib.util.spec_from_file_location("fallback_reviewed_base", source)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def canonical(path):
    result = Path(os.path.abspath(path))
    if str(result) != str(path):
        raise RuntimeError("whitelist path is not an absolute normalized path")
    return result


def content_pin(row):
    if not isinstance(row.get("size"), int) or row["size"] <= 0:
        raise RuntimeError("invalid pinned file size")
    if not re.fullmatch(r"[0-9a-f]{64}", row.get("sha256", "")):
        raise RuntimeError("invalid pinned file hash")
    if not isinstance(row.get("mode"), int) or not 0 <= row["mode"] <= 0o7777:
        raise RuntimeError("invalid pinned file mode")
    if not isinstance(row.get("mtime_ns"), int):
        raise RuntimeError("invalid pinned file timestamp")


def no_live_lean_processes():
    result = subprocess.run(["ps", "-eo", "pid,stat,comm"],
                            capture_output=True, text=True, check=True)
    for line in result.stdout.splitlines()[1:]:
        fields = line.split()
        if fields[-1] in ("lake", "lean", "checklemma") and not fields[1].startswith("Z"):
            raise RuntimeError("a Lean, Lake, or verifier process is still alive")


def no_file_mappers(identities):
    targets = {(os.major(dev), os.minor(dev), inode) for dev, inode in identities}
    result = subprocess.run(["ps", "-eo", "pid,uid"],
                            capture_output=True, text=True, check=True)
    for line in result.stdout.splitlines()[1:]:
        pid, uid = map(int, line.split())
        if uid != os.getuid():
            continue
        try:
            mappings = (Path("/proc") / str(pid) / "maps").read_text()
        except FileNotFoundError:
            continue
        for entry in mappings.splitlines():
            fields = entry.split(maxsplit=5)
            major, minor = (int(x, 16) for x in fields[3].split(":"))
            if (major, minor, int(fields[4])) in targets:
                raise RuntimeError(f"storage artifact remains mapped by owned process {pid}")


class Storage(base.Storage):
    def __init__(self, config):
        if config.get("fallback_schema") != 1:
            raise RuntimeError("unsupported fallback configuration schema")
        super().__init__(config)
        self.toolchain = canonical(self.toolchain)
        self.libraries = {}
        allowed = {self.toolchain / "lib/lean" / name
                   for name in ("libleanshared.so", "libLake_shared.so")}
        for original in config.get("shared_library_whitelist", []):
            row = dict(original)
            path = canonical(row["path"])
            content_pin(row)
            if path not in allowed or str(path) in self.libraries:
                raise RuntimeError("shared library is outside the exact whitelist")
            self.libraries[str(path)] = row
        if self.libraries and set(map(Path, self.libraries)) != allowed:
            raise RuntimeError("shared-library fallback requires exactly both libraries")
        self.core = {}
        identities = set()
        for original in config.get("retained_core_whitelist", []):
            row = dict(original)
            path = canonical(row["path"])
            content_pin(row)
            if (not path.is_relative_to(self.toolchain / "lib/lean") or
                    not any(path.name.endswith(s) for s in
                            (".olean", ".olean.private", ".olean.server", ".ir"))):
                raise RuntimeError("retained core path is outside runtime artifact whitelist")
            for key in ("pid", "fd", "fd_dev", "fd_ino"):
                if not isinstance(row.get(key), int) or row[key] < 0:
                    raise RuntimeError("invalid pinned backing identity")
            if not isinstance(row.get("symlink_mtime_ns"), int):
                raise RuntimeError("retained core symlink timestamp is missing")
            target = f"/proc/{row['pid']}/fd/{row['fd']}"
            if row.get("target") != target:
                raise RuntimeError("invalid pinned backing target")
            identity = (row["fd_dev"], row["fd_ino"])
            if str(path) in self.core or identity in identities:
                raise RuntimeError("duplicate retained core path or backing")
            identities.add(identity)
            self.core[str(path)] = row
        self.validate_core_source()
        self.validate_exclusions()

    def validate_core_source(self):
        entry = self.c.get("retained_core_source_manifest")
        if not isinstance(entry, dict):
            raise RuntimeError("retained-core source manifest pin is missing")
        raw = canonical(entry["path"]).read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry["sha256"]:
            raise RuntimeError("retained-core source manifest changed")
        data = json.loads(raw)
        if not isinstance(data, dict) or not isinstance(data.get("files"), list):
            raise RuntimeError("invalid retained-core source manifest")
        records = {}
        for row in data["files"]:
            path = str(canonical(row["path"]))
            if path in records:
                raise RuntimeError("duplicate retained-core source path")
            records[path] = row
        for path, row in self.core.items():
            source = records.get(path)
            if source is None or any(source.get(key) != value for key, value in row.items()):
                raise RuntimeError("retained-core whitelist differs from reviewed source")

    def validate_exclusions(self):
        paths, identities = set(), set()
        for entry in self.c.get("excluded_core_manifests", []):
            path = canonical(entry["path"])
            raw = path.read_bytes()
            if hashlib.sha256(raw).hexdigest() != entry["sha256"]:
                raise RuntimeError("excluded-core manifest changed")
            data = json.loads(raw)
            if not isinstance(data, dict) or not isinstance(data.get("files"), list):
                raise RuntimeError("invalid excluded-core manifest")
            for row in data["files"]:
                paths.add(str(canonical(row["path"])))
                dev = row.get("fd_dev", row.get("device"))
                ino = row.get("fd_ino", row.get("inode"))
                if not isinstance(dev, int) or not isinstance(ino, int):
                    raise RuntimeError("excluded backing identity is missing")
                identities.add((dev, ino))
        for path, row in self.core.items():
            if path in paths or (row["fd_dev"], row["fd_ino"]) in identities:
                raise RuntimeError("retained and excluded core files overlap")
        self.excluded_paths, self.excluded_identities = paths, identities

    def shared_pin(self, row):
        canonical(row["path"])
        pin = self.libraries.get(row["path"])
        if pin is not None:
            for key in ("size", "sha256", "mode", "mtime_ns"):
                if row.get(key) != pin[key]:
                    raise RuntimeError("shared-library transaction pin changed")

    def check_library(self, path):
        pin = self.libraries[str(path)]
        if path.is_symlink() or not path.is_file():
            raise RuntimeError("pinned shared library is not an existing regular file")
        st = path.stat()
        if (st.st_size != pin["size"] or stat.S_IMODE(st.st_mode) != pin["mode"] or
                st.st_mtime_ns != pin["mtime_ns"] or base.file_digest(path) != pin["sha256"]):
            raise RuntimeError("pinned shared-library bytes or metadata changed")

    def eligible(self, path):
        return str(Path(os.path.abspath(path))) in self.libraries or super().eligible(path)

    def candidates(self):
        found = set(super().candidates())
        for name in self.libraries:
            path = Path(name)
            self.check_library(path)
            found.add(path)
        return sorted(found)

    def prepare(self):
        records = super().prepare()
        for name in self.libraries:
            self.check_library(Path(name))
            st = Path(name).stat()
            records[name].update(file_dev=st.st_dev, file_ino=st.st_ino)
        base.atomic_json(self.prepared, {"files": records})
        return records

    def runtime_path(self, path):
        path = Path(os.path.abspath(path))
        if path.is_relative_to(self.toolchain / "lib/lean"):
            return str(path) in self.core
        return super().runtime_path(path)

    def own_fd(self, row):
        canonical(row["path"])
        pin = self.core.get(row["path"])
        if pin is not None:
            for key in ("pid", "fd", "target", "size", "sha256", "mode", "mtime_ns", "fd_dev", "fd_ino", "symlink_mtime_ns"):
                if row.get(key) != pin[key]:
                    raise RuntimeError("retained core transaction pin changed")
        return super().own_fd(row)

    def ram_plan(self):
        self.validate_core_source()
        self.validate_exclusions()
        total, possible, seen_targets, seen_core = 0, [], {}, set()
        for name in self.c["ram_manifests"]:
            manifest = json.loads(Path(name).read_text())
            pid = manifest["pid"]
            for item in manifest["files"]:
                path = canonical(item["path"])
                target = f"/proc/{pid}/fd/{item['fd']}"
                pin = self.core.get(str(path))
                if pin is not None:
                    if (pid != pin["pid"] or item["fd"] != pin["fd"] or
                            item["bytes"] != pin["size"] or item["sha256"] != pin["sha256"]):
                        raise RuntimeError("selected core file disagrees with backing manifest")
                    seen_core.add(str(path))
                if target in seen_targets:
                    prior_path = seen_targets[target]
                    if str(path) != prior_path and (pin is not None or prior_path in self.core):
                        raise RuntimeError("selected core backing aliases another runtime path")
                    continue
                seen_targets[target] = str(path)
                st = os.stat(target)
                total += st.st_size
                is_private = path.is_relative_to(self.mathlib / ".lake/build") and path.name.endswith(".olean.private")
                if not is_private and pin is None:
                    continue
                identity = (st.st_dev, st.st_ino)
                if str(path) in self.excluded_paths or identity in self.excluded_identities:
                    raise RuntimeError("evacuation candidate overlaps excluded core backing")
                if not path.is_symlink() or os.readlink(path) != target or st.st_size != item["bytes"]:
                    raise RuntimeError("unexpected runtime artifact state")
                row = {"path": str(path), "pid": pid, "fd": item["fd"], "target": target,
                       "size": item["bytes"], "sha256": item["sha256"],
                       "mode": stat.S_IMODE(st.st_mode), "mtime_ns": st.st_mtime_ns,
                       "fd_dev": st.st_dev, "fd_ino": st.st_ino}
                if pin is not None:
                    row["symlink_mtime_ns"] = pin["symlink_mtime_ns"]
                    if path.lstat().st_mtime_ns != pin["symlink_mtime_ns"]:
                        raise RuntimeError("selected core symlink timestamp changed")
                    self.own_fd(row)
                    if base.file_digest(path) != pin["sha256"]:
                        raise RuntimeError("selected core backing bytes changed")
                possible.append(row)
        if seen_core != set(self.core):
            raise RuntimeError("selected core file missing from backing manifests")
        needed = max(0, total - self.c["ram_limit_bytes"])
        selected, evacuated = [], 0
        for row in sorted(possible, key=lambda row: row["size"], reverse=True):
            if evacuated >= needed:
                break
            selected.append(row)
            evacuated += row["size"]
        if evacuated < needed:
            raise RuntimeError("insufficient explicitly eligible backings for RAM target")
        return selected, total, evacuated

    def offload(self, row):
        self.shared_pin(row)
        if row["path"] in self.libraries:
            path = Path(row["path"])
            if path.exists() or path.is_symlink():
                st = path.stat()
                if (st.st_dev, st.st_ino) != (row.get("file_dev"), row.get("file_ino")):
                    raise RuntimeError("shared-library identity changed after planning")
                no_live_lean_processes()
                no_file_mappers({(st.st_dev, st.st_ino)})
        return super().offload(row)

    def restore_build(self, row):
        self.shared_pin(row)
        return super().restore_build(row)

    def evacuate(self, row):
        if row["path"] in self.core:
            self.own_fd(row)
            if Path(row["path"]).lstat().st_mtime_ns != row["symlink_mtime_ns"]:
                raise RuntimeError("core symlink timestamp changed before evacuation")
            no_live_lean_processes()
            no_file_mappers({(row["fd_dev"], row["fd_ino"])})
        return super().evacuate(row)

    def restore_ram(self, row):
        is_core = row["path"] in self.core
        if is_core:
            self.own_fd(row)
            targets = {(row["fd_dev"], row["fd_ino"])}
            path = Path(row["path"])
            if path.exists():
                st = path.stat()
                targets.add((st.st_dev, st.st_ino))
            no_live_lean_processes()
            no_file_mappers(targets)
        super().restore_ram(row)
        if is_core:
            path = Path(row["path"])
            if not path.is_symlink() or os.readlink(path) != row["target"]:
                raise RuntimeError("restored core link differs")
            os.utime(path, ns=(row["symlink_mtime_ns"],) * 2, follow_symlinks=False)
            parent = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(parent)
            finally:
                os.close(parent)
            if path.lstat().st_mtime_ns != row["symlink_mtime_ns"]:
                raise RuntimeError("restored core symlink timestamp differs")

    def enter(self):
        no_live_lean_processes()
        targets = {(row["fd_dev"], row["fd_ino"]) for row in self.core.values()}
        for name in self.libraries:
            self.check_library(Path(name))
            st = Path(name).stat()
            targets.add((st.st_dev, st.st_ino))
        no_file_mappers(targets)
        return super().enter()

    def restore(self):
        no_live_lean_processes()
        return super().restore()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True)
    parser.add_argument("--config-sha256", required=True)
    parser.add_argument("action", choices=("prepare", "enter", "restore"))
    args = parser.parse_args()
    try:
        path = canonical(args.config)
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != args.config_sha256:
            raise RuntimeError("reviewed fallback configuration changed")
        config = json.loads(raw)
        state = canonical(config["state_dir"])
        state.mkdir(parents=True, exist_ok=True)
        lock_path = canonical(config.get("phase_lock", str(state / "phase.lock")))
        with lock_path.open("a") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            getattr(Storage(config), args.action)()
    except Exception as error:
        base.report("failed", action=args.action, error=str(error))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
