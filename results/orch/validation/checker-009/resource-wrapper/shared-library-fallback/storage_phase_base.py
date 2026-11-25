#!/usr/bin/env python3
"""Transactional storage phases; every diagnostic goes to stderr."""
import argparse
import ctypes
import ctypes.util
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import sys

BASE = Path(__file__).resolve().parent


def report(event, **fields):
    print(json.dumps({"storage_phase": event, **fields}), file=sys.stderr, flush=True)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".new")
    with temporary.open("w") as stream:
        json.dump(value, stream, separators=(",", ":"))
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


class Codec:
    def __init__(self):
        self.lib = ctypes.CDLL(ctypes.util.find_library("zstd"))
        for name in ("ZSTD_compress", "ZSTD_decompress"):
            function = getattr(self.lib, name)
            function.restype = ctypes.c_size_t
        self.lib.ZSTD_compress.argtypes = [ctypes.c_void_p, ctypes.c_size_t,
            ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
        self.lib.ZSTD_decompress.argtypes = [ctypes.c_void_p, ctypes.c_size_t,
            ctypes.c_void_p, ctypes.c_size_t]
        self.lib.ZSTD_compressBound.argtypes = [ctypes.c_size_t]
        self.lib.ZSTD_compressBound.restype = ctypes.c_size_t
        self.lib.ZSTD_isError.argtypes = [ctypes.c_size_t]
        self.lib.ZSTD_isError.restype = ctypes.c_uint

    def compress(self, raw):
        output = ctypes.create_string_buffer(self.lib.ZSTD_compressBound(len(raw)))
        source = ctypes.create_string_buffer(raw)
        size = self.lib.ZSTD_compress(output, len(output), source, len(raw), 3)
        if self.lib.ZSTD_isError(size):
            raise RuntimeError("zstd compression failed")
        return output.raw[:size]

    def decompress(self, compressed, size):
        output = ctypes.create_string_buffer(max(size, 1))
        source = ctypes.create_string_buffer(compressed)
        actual = self.lib.ZSTD_decompress(output, size, source, len(compressed))
        if self.lib.ZSTD_isError(actual) or actual != size:
            raise RuntimeError("invalid compressed backup")
        return output.raw[:size]


class Storage:
    def __init__(self, config):
        self.c = config
        self.state = Path(config["state_dir"])
        self.state.mkdir(parents=True, exist_ok=True)
        self.journal = self.state / "transaction.json"
        self.prepared = self.state / "prepared.json"
        self.extra_pack = self.state / "extra.zstpack"
        self.codec = Codec()
        self.reserve = config["disk_reserve_bytes"]
        self.packages = Path(config["packages_root"])
        self.project_build = Path(config["project_build_root"])
        self.mathlib = self.packages / "mathlib"
        self.toolchain = Path(config["toolchain_root"])

    def free(self):
        return shutil.disk_usage(self.state).free

    def room(self, amount, restoring=False):
        reserve = 0 if restoring else self.reserve
        if self.free() < amount + reserve:
            raise RuntimeError(f"insufficient disk headroom: need {amount} bytes plus reserve")

    def eligible(self, path):
        path = Path(os.path.abspath(path))
        if path == self.mathlib / "Mathlib.lean":
            return True
        if path.is_relative_to(self.mathlib / "Mathlib") and path.suffix == ".lean":
            return True
        build_type = path.suffix in (".c", ".ilean", ".hash", ".trace") or path.name.endswith(".setup.json")
        if not build_type:
            return False
        if path.is_relative_to(self.project_build):
            return True
        if path.is_relative_to(self.packages):
            parts = path.relative_to(self.packages).parts
            return len(parts) >= 4 and parts[1:3] == (".lake", "build")
        return False

    def runtime_path(self, path):
        path = Path(os.path.abspath(path))
        return path.is_relative_to(self.toolchain / "lib" / "lean") or (
            path.is_relative_to(self.packages) and ".lake/build/" in path.as_posix())

    def candidates(self):
        roots = [self.project_build, self.mathlib / "Mathlib"]
        if self.packages.exists():
            roots += [p / ".lake" / "build" for p in self.packages.iterdir()
                      if p.is_dir() and not p.is_symlink()]
        found = set()
        for root in roots:
            if not root.exists():
                continue
            for directory, subdirs, names in os.walk(root, followlinks=False):
                subdirs[:] = [n for n in subdirs if not Path(directory, n).is_symlink()]
                for name in names:
                    path = Path(directory, name)
                    if self.eligible(path) and path.is_file() and not path.is_symlink():
                        found.add(path)
        root_source = self.mathlib / "Mathlib.lean"
        if root_source.is_file() and not root_source.is_symlink():
            found.add(root_source)
        return sorted(found)

    def baseline(self):
        index = {}
        with open(self.c["editor_index"]) as stream:
            for line in stream:
                fields = line.rstrip("\n").split("\t")
                if len(fields) != 6:
                    raise RuntimeError("invalid editor backup index")
                index[fields[0]] = (int(fields[4]), int(fields[5]))
        records = {}
        with open(self.c["editor_manifest"]) as stream:
            for line in stream:
                row = json.loads(line)
                if not self.eligible(row["path"]):
                    raise RuntimeError("editor backup path is not build-only")
                offset, compressed = index[row["virtual"]]
                records[row["path"]] = {"path": row["path"], "size": row["size"],
                    "mode": row["mode"], "mtime_ns": row["mtime_ns"],
                    "sha256": row["sha256"], "pack": self.c["editor_pack"],
                    "offset": offset, "compressed": compressed}
        return records

    def backup_bytes(self, row):
        with open(row["pack"], "rb") as stream:
            stream.seek(row["offset"])
            compressed = stream.read(row["compressed"])
        if len(compressed) != row["compressed"]:
            raise RuntimeError("truncated compressed backup")
        raw = self.codec.decompress(compressed, row["size"])
        if digest(raw) != row["sha256"]:
            raise RuntimeError(f"backup hash mismatch: {row['path']}")
        return raw

    def prepare(self):
        records = self.baseline()
        if self.prepared.exists():
            records.update(json.loads(self.prepared.read_text())["files"])
        added = 0
        with self.extra_pack.open("ab") as pack:
            for path in self.candidates():
                before = path.stat()
                raw = path.read_bytes()
                after = path.stat()
                if (before.st_size, before.st_mtime_ns, before.st_ino) != (
                        after.st_size, after.st_mtime_ns, after.st_ino):
                    raise RuntimeError(f"file changed during backup: {path}")
                sha = digest(raw)
                row = records.get(str(path))
                if (row is None or row["sha256"] != sha or row["size"] != len(raw)
                        or "pack" not in row):
                    compressed = self.codec.compress(raw)
                    row = {"path": str(path), "size": len(raw), "sha256": sha,
                           "pending_compressed": len(compressed)}
                    if self.free() >= len(compressed) + self.reserve:
                        offset = pack.tell()
                        pack.write(compressed)
                        pack.flush()
                        row.update(pack=str(self.extra_pack), offset=offset,
                                   compressed=len(compressed))
                        row.pop("pending_compressed", None)
                        added += len(compressed)
                else:
                    row = dict(row)
                row.update(mode=stat.S_IMODE(before.st_mode), mtime_ns=before.st_mtime_ns)
                records[str(path)] = row
            pack.flush()
            os.fsync(pack.fileno())
        atomic_json(self.prepared, {"files": records})
        report("prepared", files=len(records), compressed_added=added,
               pending_backups=sum("pack" not in row for row in records.values()),
               disk_free=self.free())
        return records

    def finish_backups(self, plan):
        appended = 0
        with self.extra_pack.open("ab") as pack:
            for row in plan["build"]:
                if "pack" in row:
                    continue
                path = Path(row["path"])
                if path.is_symlink() or not path.is_file():
                    raise RuntimeError(f"pending backup original missing: {path}")
                st = path.stat()
                raw = path.read_bytes()
                if (len(raw) != row["size"] or digest(raw) != row["sha256"] or
                        st.st_mtime_ns != row["mtime_ns"] or stat.S_IMODE(st.st_mode) != row["mode"]):
                    raise RuntimeError(f"pending backup original changed: {path}")
                compressed = self.codec.compress(raw)
                appended += len(compressed)
                if (len(compressed) != row.get("pending_compressed") or
                        appended > plan["pending_backup_budget"]):
                    raise RuntimeError("pending backups would exceed final restoration headroom")
                self.room(len(compressed))
                offset = pack.tell()
                pack.write(compressed)
                pack.flush()
                row.update(pack=str(self.extra_pack), offset=offset, compressed=len(compressed))
                row.pop("pending_compressed", None)
            pack.flush()
            os.fsync(pack.fileno())
        # No pending original is removed until its durable backup is in this journal.
        atomic_json(self.journal, plan)
        records = json.loads(self.prepared.read_text())["files"]
        records.update({row["path"]: row for row in plan["build"]})
        atomic_json(self.prepared, {"files": records})

    def cleanup_temporary(self, path):
        temporary = path.with_name(path.name + ".storage-phase-new")
        if temporary.is_symlink():
            raise RuntimeError(f"unexpected symlink at transaction temporary: {temporary}")
        if temporary.exists():
            if not temporary.is_file():
                raise RuntimeError(f"unexpected nonfile transaction temporary: {temporary}")
            temporary.unlink()

    def own_fd(self, row):
        target = row["target"]
        expected = f"/proc/{row['pid']}/fd/{row['fd']}"
        if target != expected or not self.runtime_path(row["path"]):
            raise RuntimeError("unrecognized runtime backing path")
        st = os.stat(target)
        if (st.st_dev, st.st_ino) != (row["fd_dev"], row["fd_ino"]):
            raise RuntimeError(f"runtime holder identity changed: {row['path']}")
        return target

    def ram_plan(self):
        total = 0
        possible = []
        seen = set()
        for name in self.c["ram_manifests"]:
            manifest = json.loads(Path(name).read_text())
            pid = manifest["pid"]
            for item in manifest["files"]:
                target = f"/proc/{pid}/fd/{item['fd']}"
                if target in seen:
                    continue
                seen.add(target)
                st = os.stat(target)
                total += st.st_size
                path = Path(item["path"])
                if (path.is_relative_to(self.mathlib / ".lake" / "build") and
                        path.name.endswith(".olean.private")):
                    if not path.is_symlink() or os.readlink(path) != target:
                        raise RuntimeError(f"unexpected runtime path state: {path}")
                    if st.st_size != item["bytes"]:
                        raise RuntimeError(f"runtime backing size mismatch: {path}")
                    possible.append({"path": str(path), "pid": pid, "fd": item["fd"],
                        "target": target, "size": item["bytes"], "sha256": item["sha256"],
                        "mode": stat.S_IMODE(st.st_mode), "mtime_ns": st.st_mtime_ns,
                        "fd_dev": st.st_dev, "fd_ino": st.st_ino})
        needed = max(0, total - self.c["ram_limit_bytes"])
        selected = []
        evacuated = 0
        for row in sorted(possible, key=lambda row: row["size"], reverse=True):
            if evacuated >= needed:
                break
            selected.append(row)
            evacuated += row["size"]
        if evacuated < needed:
            raise RuntimeError("not enough eligible Mathlib private backings to reach RAM target")
        return selected, total, evacuated

    def write_regular(self, path, raw, mode, mtime_ns, restoring=False):
        self.room(len(raw), restoring=restoring)
        temporary = path.with_name(path.name + ".storage-phase-new")
        if temporary.exists() or temporary.is_symlink():
            raise RuntimeError(f"unresolved temporary file exists: {temporary}")
        try:
            with temporary.open("xb") as stream:
                stream.write(raw)
                stream.flush()
                os.fchmod(stream.fileno(), mode)
                os.utime(stream.fileno(), ns=(mtime_ns, mtime_ns))
                os.fsync(stream.fileno())
            os.replace(temporary, path)
            parent_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(parent_fd)
            finally:
                os.close(parent_fd)
        finally:
            if temporary.exists():
                temporary.unlink()

    def offload(self, row):
        path = Path(row["path"])
        if not self.eligible(path) or path.is_symlink():
            raise RuntimeError(f"refusing non-build-only path: {path}")
        if not path.exists():
            return
        st = path.stat()
        if (st.st_size != row["size"] or stat.S_IMODE(st.st_mode) != row["mode"] or
                st.st_mtime_ns != row["mtime_ns"] or file_digest(path) != row["sha256"]):
            raise RuntimeError(f"build-only file changed after planning: {path}")
        self.backup_bytes(row)
        path.unlink()

    def evacuate(self, row):
        path = Path(row["path"])
        target = self.own_fd(row)
        if not path.is_symlink() or os.readlink(path) != target:
            raise RuntimeError(f"runtime path is not the original holder link: {path}")
        raw = path.read_bytes()
        if len(raw) != row["size"] or digest(raw) != row["sha256"]:
            raise RuntimeError(f"runtime source hash mismatch: {path}")
        self.write_regular(path, raw, row["mode"], row["mtime_ns"])
        if path.is_symlink() or file_digest(path) != row["sha256"]:
            raise RuntimeError(f"evacuation destination hash mismatch: {path}")
        fd = os.open(self.own_fd(row), os.O_RDWR)
        try:
            os.ftruncate(fd, 0)
        finally:
            os.close(fd)

    def restore_ram(self, row):
        path = Path(row["path"])
        target = self.own_fd(row)
        if path.is_symlink():
            if os.readlink(path) != target or path.stat().st_size != row["size"]:
                raise RuntimeError(f"runtime symlink changed or has missing bytes: {path}")
            if file_digest(path) != row["sha256"]:
                raise RuntimeError(f"runtime symlink hash mismatch: {path}")
            os.chmod(target, row["mode"])
            os.utime(target, ns=(row["mtime_ns"], row["mtime_ns"]))
            self.cleanup_temporary(path)
            return
        if not path.is_file() or path.stat().st_size != row["size"]:
            raise RuntimeError(f"runtime surviving disk copy missing: {path}")
        raw = path.read_bytes()
        if digest(raw) != row["sha256"]:
            raise RuntimeError(f"runtime disk copy hash mismatch: {path}")
        fd = os.open(target, os.O_RDWR)
        try:
            view = memoryview(raw)
            offset = 0
            while offset < len(view):
                written = os.pwrite(fd, view[offset:], offset)
                if written <= 0:
                    raise RuntimeError("short write restoring runtime backing")
                offset += written
            os.ftruncate(fd, len(raw))
            os.fchmod(fd, row["mode"])
            os.utime(fd, ns=(row["mtime_ns"], row["mtime_ns"]))
        finally:
            os.close(fd)
        if file_digest(target) != row["sha256"]:
            raise RuntimeError(f"restored runtime backing hash mismatch: {path}")
        temporary = path.with_name(path.name + ".storage-phase-link")
        if temporary.exists() or temporary.is_symlink():
            temporary.unlink()
        os.symlink(target, temporary)
        os.replace(temporary, path)
        self.cleanup_temporary(path)

    def restore_build(self, row):
        path = Path(row["path"])
        if not self.eligible(path):
            raise RuntimeError(f"refusing non-build-only restoration: {path}")
        if path.is_symlink():
            raise RuntimeError(f"unexpected symlink at build-only path: {path}")
        if path.exists():
            if path.stat().st_size != row["size"] or file_digest(path) != row["sha256"]:
                raise RuntimeError(f"refusing to overwrite changed build-only file: {path}")
            os.chmod(path, row["mode"])
            os.utime(path, ns=(row["mtime_ns"], row["mtime_ns"]))
            self.cleanup_temporary(path)
            return
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = self.backup_bytes(row)
        self.cleanup_temporary(path)
        self.write_regular(path, raw, row["mode"], row["mtime_ns"], restoring=True)
        if file_digest(path) != row["sha256"]:
            raise RuntimeError(f"restored build-only hash mismatch: {path}")

    def enter(self):
        if self.journal.exists():
            previous = json.loads(self.journal.read_text())
            if previous.get("status") != "restored":
                raise RuntimeError("an unfinished storage transaction requires restore")
        records = self.prepare()
        build = [records[str(path)] for path in self.candidates()]
        ram, total, evacuated = self.ram_plan()
        plan = {"status": "planned", "build": build, "ram": ram,
                "pinned_before": total, "evacuated_bytes": evacuated}
        journal_estimate = len(json.dumps(plan, separators=(",", ":")).encode()) + 4096
        # Keep room for the journal and atomic journal/manifest rewrites after recovery.
        pending_budget = self.free() - 3 * journal_estimate - 16 * 1024 * 1024
        pending_expected = sum(row.get("pending_compressed", 0) for row in build if "pack" not in row)
        if pending_budget < pending_expected:
            raise RuntimeError("insufficient final restoration headroom for journal and pending backups")
        plan["pending_backup_budget"] = pending_budget
        plan["pending_backup_expected"] = pending_expected
        atomic_json(self.journal, plan)
        report("planned", build_files=len(build), build_bytes=sum(x["size"] for x in build),
               ram_files=len(ram), pinned_before=total, evacuation_bytes=evacuated)
        for row in build:
            if "pack" in row:
                self.offload(row)
        self.finish_backups(plan)
        for row in build:
            self.offload(row)
        for row in ram:
            self.evacuate(row)
        plan["status"] = "entered"
        atomic_json(self.journal, plan)
        report("entered", pinned_after=total - evacuated, disk_free=self.free())

    def restore(self):
        if not self.journal.exists():
            report("restore_no_transaction")
            return
        plan = json.loads(self.journal.read_text())
        if plan.get("status") == "restored":
            report("already_restored")
            return
        errors = []
        for kind, operation in (("ram", self.restore_ram), ("build", self.restore_build)):
            for row in plan[kind]:
                try:
                    operation(row)
                except Exception as error:
                    errors.append(f"{row['path']}: {error}")
                    report("restore_error", path=row["path"], error=str(error))
        if errors:
            raise RuntimeError(f"storage restoration incomplete for {len(errors)} paths")
        plan["status"] = "restored"
        atomic_json(self.journal, plan)
        report("restored", ram_files=len(plan["ram"]), build_files=len(plan["build"]),
               disk_free=self.free())

    def init_restore(self):
        records = self.baseline()
        for row in records.values():
            self.restore_build(row)
        report("baseline_restored", files=len(records), disk_free=self.free())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", default=str(BASE / "storage_config.json"))
    parser.add_argument("action", choices=("prepare", "enter", "restore", "init-restore"))
    args = parser.parse_args()
    try:
        config = json.loads(Path(args.config).read_text())
        state = Path(config["state_dir"])
        state.mkdir(parents=True, exist_ok=True)
        with (state / "phase.lock").open("a") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            storage = Storage(config)
            getattr(storage, args.action.replace("-", "_"))()
    except Exception as error:
        report("failed", action=args.action, error=str(error))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
