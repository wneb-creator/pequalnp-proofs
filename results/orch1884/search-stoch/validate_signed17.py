import ast
import json
import re
import sys
from pathlib import Path

log, prefix = Path(sys.argv[1]), Path(sys.argv[2])
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
reports = []
for line in log.read_text().splitlines():
    if line.startswith("best "):
        match = re.fullmatch(r"best (\d+) trial (\d+) gates (\[.*\])", line)
        assert match
        gates = ast.literal_eval(match[3])
        assert len(gates) == 17 and gates[0] in ((1,0,1), (1,0,2))
        fp, fn, errors = 0, 0, []
        for mask in range(1024):
            wires = [bool(mask >> v & 1) for v in range(10)]
            for i, (op,a,b) in enumerate(gates):
                assert op in (0,1,2,3) and 0 <= a < 10+i and 0 <= b < 10+i
                wires.append((wires[a] and wires[b]) if op == 0 else
                             (wires[a] or wires[b]) if op == 1 else
                             (wires[a] and not wires[b]) if op == 2 else
                             (not wires[a] and wires[b]))
            target = any(mask >> a & 1 and mask >> b & 1 for a,b in edges)
            if wires[-1] != target:
                errors.append(mask)
                fp += wires[-1]
                fn += not wires[-1]
        assert 4*fp+fn == int(match[1])
        report = dict(trial=int(match[2]), weighted_score=4*fp+fn,
                      false_positive=fp, false_negative=fn, errors=errors)
        reports.append(report)
        candidate = dict(inputs=10, output=26, gates=gates,
                         operators=["AND", "OR", "a AND NOT b", "NOT a AND b"],
                         validation=report)
        prefix.with_name(prefix.name+"-best.json").write_text(json.dumps(candidate,indent=2)+"\n")
    elif line.startswith(("REALIZATION ", "FULL_WITNESS ")):
        label, payload = line.split(" ",1)
        candidate = json.loads(payload)
        gates = candidate["gates"]
        for mask in range(1024):
            wires = [bool(mask >> v & 1) for v in range(10)]
            wires.append(not wires[0])
            for i,(op,a,b) in enumerate(gates):
                assert op in (0,1,2) and 0 <= a < 11+i and 0 <= b < 11+i
                wires.append((wires[a] and wires[b]) if op == 0 else
                             (wires[a] or wires[b]) if op == 1 else not wires[a])
            target = any(mask >> a & 1 and mask >> b & 1 for a,b in edges)
            assert wires[candidate["output"]] == target
        candidate["assignments_verified"] = 1024
        candidate["within_target_budget"] = len(gates) <= 18
        if label == "FULL_WITNESS":
            assert candidate["within_target_budget"]
        prefix.with_name(prefix.name+"-realization.json").write_text(json.dumps(candidate,indent=2)+"\n")
prefix.with_name(prefix.name+"-validation.json").write_text(json.dumps(reports,indent=2)+"\n")
print(json.dumps([{k:v for k,v in r.items() if k!="errors"} for r in reports]))
