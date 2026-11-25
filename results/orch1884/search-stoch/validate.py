import ast
import json
import re
import sys
from pathlib import Path

log = Path(sys.argv[1])
prefix = Path(sys.argv[2])
rows = None if len(sys.argv) < 4 else json.loads(Path(sys.argv[3]).read_text())["rows"]
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
reports = []
for line in log.read_text().splitlines():
    if not line.startswith("best "):
        continue
    match = re.fullmatch(r"best (\d+) trial (\d+) gates (\[.*\])", line)
    assert match
    claimed, trial = int(match[1]), int(match[2])
    gates = ast.literal_eval(match[3])
    assert len(gates) == 18
    errors, fp, fn, sampled = [], 0, 0, 0
    for mask in range(1024):
        wires = [bool(mask >> v & 1) for v in range(10)]
        wires.append(not wires[0])
        for index, (op, a, b) in enumerate(gates):
            assert op in (0, 1, 2)
            assert 0 <= a < 11 + index and 0 <= b < 11 + index
            wires.append((wires[a] and wires[b]) if op == 0 else
                         (wires[a] or wires[b]) if op == 1 else not wires[a])
        target = any(mask >> a & 1 and mask >> b & 1 for a, b in edges)
        if wires[-1] != target:
            errors.append(mask)
            fp += wires[-1]
            fn += not wires[-1]
            if rows is None or mask in rows:
                sampled += 4 if wires[-1] else 1
    assert claimed == sampled, (claimed, sampled)
    report = dict(claimed=claimed, trial=trial, false_positive=fp, false_negative=fn,
                  paid_not=sum(g[0] == 2 for g in gates))
    reports.append(report)
    candidate = dict(inputs=11, free_input="not x0", output=28, gates=gates,
                     validation=report, errors=errors)
    prefix.with_name(prefix.name + "-best.json").write_text(json.dumps(candidate, indent=2) + "\n")
prefix.with_name(prefix.name + "-validation.json").write_text(json.dumps(reports, indent=2) + "\n")
print(json.dumps(reports))
