import ast
import json
import re
import sys
from pathlib import Path

log, prefix = Path(sys.argv[1]), Path(sys.argv[2])
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
samples = None
reports = []

def check(gates):
    assert len(gates) == 18
    assert sum(op == 2 for op, _, _ in gates) <= 1
    errors = []
    weighted = 0
    false_positive = 0
    for mask in range(1024):
        wires = [bool(mask >> v & 1) for v in range(10)]
        wires.append(not wires[0])
        for i, (op, a, b) in enumerate(gates):
            assert op in (0, 1, 2)
            assert 0 <= a < 11 + i and 0 <= b < 11 + i
            wires.append((wires[a] and wires[b]) if op == 0 else
                         (wires[a] or wires[b]) if op == 1 else not wires[a])
        target = any(mask >> a & 1 and mask >> b & 1 for a, b in edges)
        if wires[-1] != target:
            errors.append(mask)
            false_positive += wires[-1]
            if mask in samples:
                weighted += 4 if wires[-1] else 1
    return dict(sample_count=len(samples), sampled_score=weighted,
                false_positive=false_positive,
                false_negative=len(errors)-false_positive, errors=errors)

for line in log.read_text().splitlines():
    if line.startswith("SAMPLES "):
        samples = json.loads(line.removeprefix("SAMPLES "))
        assert len(samples) == len(set(samples))
        assert all(0 <= x < 1024 for x in samples)
    elif line.startswith("best "):
        match = re.fullmatch(r"best (\d+) trial (\d+) gates (\[.*\])", line)
        assert match and samples is not None
        gates = ast.literal_eval(match[3])
        report = check(gates)
        assert report["sampled_score"] == int(match[1])
        report["trial"] = int(match[2])
        reports.append(report)
        prefix.with_name(prefix.name + "-best.json").write_text(json.dumps(
            dict(inputs=11, free_input="not x0", output=28, gates=gates,
                 validation=report), indent=2) + "\n")
    elif line.startswith("FULL_WITNESS "):
        candidate = json.loads(line.removeprefix("FULL_WITNESS "))
        report = check(candidate["gates"])
        assert not report["errors"]
        candidate["validation"] = report
        prefix.with_name(prefix.name + "-verified-witness.json").write_text(
            json.dumps(candidate, indent=2) + "\n")

prefix.with_name(prefix.name + "-validation.json").write_text(json.dumps(reports, indent=2) + "\n")
print(json.dumps(reports))
