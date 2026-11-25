"""Recheck the archived C5 cases with the installed Lean toolchain."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", type=Path, default=HERE.parents[3])
parser.add_argument("--output", type=Path, default=HERE / "rechecked")
parser.add_argument("--lake", default="lake")
parser.add_argument("--values", type=int, nargs="*")
args = parser.parse_args()
coverage = json.loads((HERE / "coverage.json").read_text())
values = coverage["first_or_values"] if args.values is None else args.values
assert len(coverage["first_or_values"]) == 102
assert all(value in coverage["first_or_values"] for value in values)
base = (HERE / "first_0.lean").read_text().split("set_option maxRecDepth")[0]
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
(output / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
metrics = output / "metrics.jsonl"
metrics.write_text("")
for value in values:
    name = f"first_{value}"
    source_text = base + (
        "set_option maxRecDepth 10000 in\n"
        "set_option maxHeartbeats 20000000 in\n"
        f"theorem {name} : checkFirst {value} = true := by\n"
        "  decide +kernel\n\n"
        "end PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate\n\n"
        f"#print axioms PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate.{name}\n"
    )
    source = output / f"{name}.lean"
    source.write_text(source_text)
    start = time.monotonic()
    with (output / f"{name}.stdout").open("w") as out, (output / f"{name}.stderr").open("w") as err:
        process = subprocess.Popen(
            [args.lake, "env", "lean", str(source)],
            cwd=args.repo.resolve() / "lean", stdout=out, stderr=err,
        )
        _, status, usage = os.wait4(process.pid, 0)
        code = os.waitstatus_to_exitcode(status)
        process.returncode = code
    record = {
        "value": value, "exit_code": code,
        "wall_seconds": time.monotonic() - start,
        "max_rss_kb": usage.ru_maxrss,
        "source_sha256": hashlib.sha256(source_text.encode()).hexdigest(),
    }
    with metrics.open("a") as log:
        log.write(json.dumps(record) + "\n")
    print(json.dumps(record), flush=True)
    if code != 0:
        raise SystemExit(1)
