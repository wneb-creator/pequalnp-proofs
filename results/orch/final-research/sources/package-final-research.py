import argparse
import datetime
import gzip
import hashlib
import json
import shutil
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument("--repo", type=Path, required=True)
p.add_argument("--scratch", type=Path, required=True)
p.add_argument("--destination", type=Path, required=True)
a = p.parse_args()
out = a.destination
out.mkdir(parents=True, exist_ok=True)
entries = []


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def preserve(src, name, compressed=False):
    assert src.is_file(), src
    dst = out / name
    dst.parent.mkdir(parents=True, exist_ok=True)
    original_sha = sha(src)
    if compressed:
        with src.open("rb") as inp, dst.open("wb") as raw:
            with gzip.GzipFile(filename="", mode="wb", fileobj=raw,
                               compresslevel=9, mtime=0) as zipped:
                shutil.copyfileobj(inp, zipped, length=1024 * 1024)
        restored = hashlib.sha256()
        restored_bytes = 0
        with gzip.open(dst, "rb") as inp:
            for block in iter(lambda: inp.read(1024 * 1024), b""):
                restored.update(block)
                restored_bytes += len(block)
        assert restored.hexdigest() == original_sha
        assert restored_bytes == src.stat().st_size
    else:
        shutil.copyfile(src, dst)
        assert sha(dst) == original_sha
    record = {"path": str(dst.relative_to(out)), "source": str(src),
              "bytes": dst.stat().st_size, "sha256": sha(dst)}
    if compressed:
        record.update(compression="gzip", uncompressed_bytes=src.stat().st_size,
                      uncompressed_sha256=original_sha,
                      decompressed_hash_verified=True)
    entries.append(record)


for name in ["dual_cnf_sat.py", "clean_cover_potential.py", "bounded_solver.py",
             "signed_code_sat.py", "plane_signed_code.py"]:
    preserve(a.repo / "results/orch" / name, "sources/" + name)
preserve(a.repo / "results/orch/or-potential-followup.md", "OR-POTENTIAL-NOTES.md")
preserve(Path(__file__), "sources/package-final-research.py")

for name in ["c4free-6-7-reps.json", "c4free-bip-7-7-reps.json",
             "structural-max-independent.json"]:
    preserve(a.scratch / name, "inputs/" + name)

prefixes = [f"dual6-7-i{i}-and5" for i in range(4)] + ["dual7-7-bip-and5"]
for prefix in prefixes:
    preserve(a.scratch / (prefix + ".cnf"), "inputs/" + prefix + ".cnf.gz", True)
    preserve(a.scratch / (prefix + ".meta.json"), "inputs/" + prefix + ".meta.json")
    for suffix in ["-encode.log", "-solve.log"]:
        preserve(a.scratch / (prefix + suffix), "logs/" + prefix + suffix)

for name in ["dual6-7-remaining-driver.log", "clean-cover-potential-6.log",
             "plane-signed-generic-encode.log", "plane-signed-generic-solve.log",
             "plane-signed-generic-180s.log", "plane-signed-generic-180s.json",
             "plane-signed-generic-180s-driver.log",
             "plane-signed-generic-180s-plain.log", "plane-signed-generic-180s-plain.json",
             "plane-signed-generic-180s-plain-driver.log"]:
    preserve(a.scratch / name, "logs/" + name)
preserve(a.scratch / "plane-signed-generic.cnf", "inputs/plane-signed-generic.cnf.gz", True)

scope = """# Final research preservation bundle

This bundle preserves completed research for job pequalnp-pilot-60 and
gap L-meta-2602. It contains no proof of the posted theorem and no Lean
certificate for the SAT outcomes. No solver was rerun while packaging.

Outcomes:

- All four six-vertex C4-free seven-edge graph types were UNSAT with five
  AND gates in the normalized free-OR model for their vertex-cover CNFs.
  By duality these searches found no five-OR circuits for the quadratic
  graph functions. Full truth inputs were encoded, not merely edge pairs.
- The seven-vertex bipartite seven-edge type was also UNSAT at five ANDs.
- The clean-cover sampler checked148236 transitions in24706 trials over
  forty seconds without finding a local violation. Explicit larger/local
  counterexamples nevertheless refute the proposed potential; see notes.
- The original generic plane signed-code run was UNKNOWN at45seconds.
  Two intended180-second extensions retained a hard300MiB address-space
  cap. The default run aborted after13.20seconds and the --plain fallback
  after15.01seconds, both with std::bad_alloc/SIGABRT and UNKNOWN. No model
  or UNSAT certificate was obtained. The cap was never raised.

Preservation:

- logs/ contains complete stdout/stderr logs and run metadata.
- inputs/ contains graph/row data, exact small CNFs and the exact generic
  plane CNF, losslessly gzip-compressed. Each compressed input was streamed
  back through SHA256 and byte-count verification before packaging ended.
- sources/ contains the exact generators, dependencies, bounded runner,
  and the packaging script. Solver binaries are not copied; the manifest
  records the installed CaDiCaL binary hash and the logs identify its version.
- manifest.json maps every payload file to its original source and hash.
  SHA256SUMS covers every bundle file except itself. Original scratch
  files remain untouched.

The packaged scripts may be run from sources/ because their sibling imports
are included. The exact commands and original paths are preserved in logs,
metadata, and the source argument parsers. Reproduction should decompress a
CNF into scratch before passing it to CaDiCaL. This bundle does not authorize
additional solver execution or a larger resource cap.

The circuit counterexamples to proposed local potentials are also preserved
by the structural agent in results/orch/tau-*.json and research-support/.
Those examples refute intermediate proof strategies, not L-meta-2602.
"""
(out / "SCOPE.md").write_text(scope)
entries.append({"path": "SCOPE.md", "source": "generated scope/outcome summary",
                "bytes": (out / "SCOPE.md").stat().st_size,
                "sha256": sha(out / "SCOPE.md")})
solver = a.scratch / "toolchain/lean-4.36.0-linux/bin/cadical"
manifest = {"job": "pequalnp-pilot-60", "gap": "L-meta-2602",
            "packaged_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "solver_path": str(solver), "solver_sha256": sha(solver),
            "solver_rerun_during_packaging": False,
            "payload_file_count": len(entries),
            "payload_bytes": sum(e["bytes"] for e in entries),
            "files": sorted(entries, key=lambda e: e["path"])}
(out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
files = sorted(p for p in out.rglob("*") if p.is_file() and p.name != "SHA256SUMS")
(out / "SHA256SUMS").write_text("".join(sha(p) + "  " + str(p.relative_to(out)) + "\n"
                                     for p in files))
print(json.dumps({"destination": str(out), "files": len(files) + 1,
                  "bytes": sum(p.stat().st_size for p in files)
                  + (out / "SHA256SUMS").stat().st_size,
                  "generic_cnf_sha256": sha(a.scratch / "plane-signed-generic.cnf"),
                  "gzip_decompression_hash_checks": "PASS"}))
