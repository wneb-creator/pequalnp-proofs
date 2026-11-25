"""Tiny isolated fixtures only: never opens installed runtime artifacts."""
import copy
import hashlib
import importlib.util
import json
import mmap
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("fallback", BASE / "storage_phase.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def pin(path):
    st = path.stat()
    return {"path": str(path), "size": st.st_size,
            "sha256": m.base.file_digest(path), "mode": stat.S_IMODE(st.st_mode),
            "mtime_ns": st.st_mtime_ns}


def fails(action, text):
    try:
        action()
    except RuntimeError as error:
        assert text in str(error), (text, str(error))
    else:
        raise AssertionError("expected refusal: " + text)


with tempfile.TemporaryDirectory(prefix="fixture-", dir=BASE) as directory:
    root = Path(directory)
    tool = root / "toolchain"
    lib = tool / "lib/lean"
    lib.mkdir(parents=True)
    packages = root / "packages"
    project = root / "project-build"
    project.mkdir()
    state = root / "state"
    state.mkdir()
    libraries = []
    for i, name in enumerate(("libleanshared.so", "libLake_shared.so")):
        path = lib / name
        path.write_bytes((name.encode() + bytes(range(32))) * 20)
        os.chmod(path, 0o644)
        os.utime(path, ns=(1700000000000000000 + i,) * 2)
        libraries.append(pin(path))
    for name in ("index.tsv", "editor.jsonl", "editor.zstpack"):
        (root / name).write_bytes(b"")
    fds, manifest_files, core = [], [], []
    paths = [lib / "Lean/Retained.olean.private",
             packages / "mathlib/.lake/build/lib/lean/Mathlib/Tiny.olean.private"]
    try:
        for i, path in enumerate(paths):
            path.parent.mkdir(parents=True, exist_ok=True)
            raw = (b"tiny retained runtime fixture" + bytes(range(32))) * (30 + i)
            fd = os.memfd_create("pnp45_fallback_test", os.MFD_CLOEXEC)
            fds.append(fd)
            os.write(fd, raw)
            os.fchmod(fd, 0o600)
            os.utime(fd, ns=(1700000000000000100 + i,) * 2)
            target = f"/proc/{os.getpid()}/fd/{fd}"
            path.symlink_to(target)
            row = pin(path)
            st = os.fstat(fd)
            row.update(pid=os.getpid(), fd=fd, target=target, fd_dev=st.st_dev, fd_ino=st.st_ino)
            row["symlink_mtime_ns"] = path.lstat().st_mtime_ns
            manifest_files.append({"path": str(path), "fd": fd,
                                   "bytes": len(raw), "sha256": row["sha256"]})
            if i == 0:
                core.append(row)
        manifest = root / "ram.json"
        manifest.write_text(json.dumps({"pid": os.getpid(), "files": manifest_files}))
        core_source = root / "core-source.json"
        core_source.write_text(json.dumps({"files": core}))
        config = {"fallback_schema": 1, "state_dir": str(state),
                  "packages_root": str(packages), "project_build_root": str(project),
                  "toolchain_root": str(tool), "editor_index": str(root / "index.tsv"),
                  "editor_manifest": str(root / "editor.jsonl"),
                  "editor_pack": str(root / "editor.zstpack"),
                  "ram_manifests": [str(manifest)], "disk_reserve_bytes": 0,
                  "ram_limit_bytes": 0, "shared_library_whitelist": libraries,
                  "retained_core_whitelist": core, "excluded_core_manifests": [],
                  "retained_core_source_manifest": {"path": str(core_source), "sha256": m.base.file_digest(core_source)}}
        phase = m.Storage(config)
        assert all(phase.eligible(row["path"]) for row in libraries)
        assert not phase.eligible(lib / "libOther.so")
        assert not phase.eligible(root / "proof.lean")
        assert phase.runtime_path(paths[0])
        assert not phase.runtime_path(lib / "Lean/Unselected.olean.private")
        print("PASS exact library and retained-core path allowlists")

        records = phase.prepare()
        phase.enter()
        assert all(not Path(row["path"]).exists() for row in libraries)
        assert all(not path.is_symlink() and path.is_file() for path in paths)
        assert all(os.fstat(fd).st_size == 0 for fd in fds)
        phase.restore()
        phase.restore()
        for row in libraries + core:
            restored = pin(Path(row["path"]))
            assert all(restored[key] == row[key] for key in restored)
        assert all(path.is_symlink() for path in paths)
        assert paths[0].lstat().st_mtime_ns == core[0]["symlink_mtime_ns"]
        print("PASS lossless full cycle and idempotent restore")

        altered = copy.deepcopy(config)
        altered["shared_library_whitelist"][0]["path"] = str(lib / "libOther.so")
        fails(lambda: m.Storage(altered), "outside the exact whitelist")
        altered = copy.deepcopy(config)
        altered["shared_library_whitelist"].pop()
        fails(lambda: m.Storage(altered), "exactly both libraries")
        print("PASS unapproved library and incomplete whitelist refused")

        original = Path(libraries[0]["path"]).read_bytes()
        Path(libraries[0]["path"]).write_bytes(b"changed")
        fails(phase.prepare, "shared-library bytes or metadata changed")
        assert Path(libraries[0]["path"]).read_bytes() == b"changed"
        Path(libraries[0]["path"]).write_bytes(original)
        os.utime(libraries[0]["path"], ns=(libraries[0]["mtime_ns"],) * 2)
        print("PASS changed library bytes refused without removal")

        altered = copy.deepcopy(config)
        altered["retained_core_whitelist"][0]["sha256"] = "0" * 64
        fails(lambda: m.Storage(altered), "differs from reviewed source")
        altered = copy.deepcopy(config)
        altered["retained_core_whitelist"][0]["fd_ino"] += 1
        fails(lambda: m.Storage(altered), "differs from reviewed source")
        print("PASS core content and backing identity pins enforced")

        saved_source = core_source.read_bytes()
        core_source.write_text(json.dumps({"files": []}))
        fails(phase.ram_plan, "source manifest changed")
        core_source.write_bytes(saved_source)
        print("PASS retained-core source manifest hash enforced")

        excluded = root / "excluded.json"
        excluded.write_text(json.dumps({"files": core}))
        altered = copy.deepcopy(config)
        altered["excluded_core_manifests"] = [{"path": str(excluded), "sha256": m.base.file_digest(excluded)}]
        fails(lambda: m.Storage(altered), "overlap")
        other = dict(core[0], path=str(lib / "Different.olean.private"))
        excluded.write_text(json.dumps({"files": [other]}))
        altered["excluded_core_manifests"][0]["sha256"] = m.base.file_digest(excluded)
        fails(lambda: m.Storage(altered), "overlap")
        excluded.write_text(json.dumps({"files": []}))
        fails(lambda: m.Storage(altered), "manifest changed")
        print("PASS excluded-core path, backing alias, and manifest hash guards")

        copied = copy.deepcopy(manifest_files)
        manifest.write_text(json.dumps({"pid": os.getpid(), "files": copied[1:]}))
        fails(phase.ram_plan, "missing from backing manifests")
        manifest.write_text(json.dumps({"pid": os.getpid(), "files": manifest_files}))
        print("PASS selected core must occur in supplied backing manifests")

        alias = dict(manifest_files[0], path=str(lib / "Aliased.olean.private"))
        manifest.write_text(json.dumps({"pid": os.getpid(), "files": [alias] + manifest_files}))
        fails(phase.ram_plan, "aliases another runtime path")
        manifest.write_text(json.dumps({"pid": os.getpid(), "files": manifest_files}))
        print("PASS retained core backing cannot alias another runtime path")

        records = phase.prepare()
        ram, total, evacuated = phase.ram_plan()
        plan = {"status": "planned", "build": [records[row["path"]] for row in libraries],
                "ram": ram, "pinned_before": total, "evacuated_bytes": evacuated}
        m.base.atomic_json(phase.journal, plan)
        phase.offload(plan["build"][0])
        phase.evacuate(plan["ram"][0])
        phase.restore()
        assert all(Path(row["path"]).is_file() for row in libraries)
        assert all(path.is_symlink() for path in paths)
        print("PASS partial-enter restoration through original machinery")

        records = phase.prepare()
        row = records[libraries[0]["path"]]
        raw = phase.extra_pack.read_bytes()
        damaged = bytearray(raw)
        damaged[row["offset"]] ^= 255
        phase.extra_pack.write_bytes(damaged)
        fails(lambda: phase.offload(row), "compressed backup")
        assert Path(row["path"]).is_file()
        phase.extra_pack.write_bytes(raw)
        print("PASS corrupt backup blocks deletion of shared library")

        records = phase.prepare()
        with Path(libraries[0]["path"]).open("rb") as stream:
            with mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ):
                fails(lambda: phase.offload(records[libraries[0]["path"]]), "remains mapped")
        assert Path(libraries[0]["path"]).is_file()
        ram, _, _ = phase.ram_plan()
        core_row = next(row for row in ram if row["path"] == core[0]["path"])
        with mmap.mmap(fds[0], 0, access=mmap.ACCESS_READ):
            fails(lambda: phase.evacuate(core_row), "remains mapped")
        assert paths[0].is_symlink() and os.fstat(fds[0]).st_size == core[0]["size"]
        print("PASS actual owned mmap blocks shared-library unlink and core truncation")

        planned = records[libraries[0]["path"]]
        library = Path(planned["path"])
        replacement = library.with_suffix(".replacement")
        replacement.write_bytes(library.read_bytes())
        os.chmod(replacement, planned["mode"])
        os.utime(replacement, ns=(planned["mtime_ns"],) * 2)
        os.replace(replacement, library)
        fails(lambda: phase.offload(planned), "identity changed after planning")
        assert library.exists()
        print("PASS same-byte library inode replacement is refused after planning")

        config_path = root / "config.json"
        config_path.write_text(json.dumps(config))
        config_hash = m.base.file_digest(config_path)
        command = [sys.executable, str(BASE / "storage_phase.py"),
                   "--config", str(config_path), "--config-sha256", config_hash, "prepare"]
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        assert result.returncode == 0, result.stderr
        command[command.index("--config-sha256") + 1] = "0" * 64
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        assert result.returncode == 1 and "configuration changed" in result.stderr
        print("PASS standalone CLI validates reviewed configuration hash")

        assert hashlib.sha256((BASE.parent / "storage_phase.py").read_bytes()).hexdigest() == m.SOURCE_SHA256
        print("PASS original production storage source unchanged")
    finally:
        for fd in fds:
            os.close(fd)
