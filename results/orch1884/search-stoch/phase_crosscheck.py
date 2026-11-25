import json
import random
import subprocess
from itertools import product
from pathlib import Path

from polarity_realizer_independent import realize, signed_eval, actual_eval

root = Path(__file__).resolve().parent
driver = "/tmp/oec/pequalnp-pilot-103/phase1884_driver"
rng = random.Random(1884)
fixtures = []
for _ in range(8):
    fixtures.append([(rng.randrange(4), rng.randrange(10+i), rng.randrange(10+i))
                     for i in range(17)])
fixtures.append([(i%2, 0 if i == 0 else 9+i, 1+i%9) for i in range(17)])
fixtures.append([(2 if i%3 == 0 else 1, 0 if i == 0 else 9+i,
                  4 if i%3 == 0 else 1+i%9) for i in range(17)])
g = [(1,0,1), (0,2,3), (2,11,4), (2,12,10)]
g += [(1,9+i,1+i%9) for i in range(4,17)]
fixtures.append(g)
g = [(2,1,2), (2,3,4), (2,5,6), (1,10,11), (1,13,12)]
g += [(1,9+i,9) for i in range(5,17)]
fixtures.append(g)

def trim(gates):
    live = {26}
    for i in range(16,-1,-1):
        if 10+i in live:
            live.update(gates[i][1:])
    mapping = {i:i for i in range(10)}
    out = []
    for i,(op,a,b) in enumerate(gates):
        if 10+i in live:
            mapping[10+i] = 10+len(out)
            out.append((op,mapping[a],mapping[b]))
    return out

reports = []
for index,gates in enumerate(fixtures):
    data = "\n".join(" ".join(map(str,g)) for g in gates)+"\n"
    result = subprocess.run([driver], input=data, text=True, capture_output=True, check=True)
    cpp = json.loads(result.stdout)
    reduced = trim(gates)
    assert cpp["binary"] == len(reduced)
    witness = None
    for free in range(10):
        witness = realize(10,reduced,free_neg=free)
        if witness is not None:
            break
    assert (cpp["paid_not"] <= 1) == (witness is not None)
    checked = 0
    if witness is not None:
        for x in product([False,True],repeat=10):
            assert signed_eval(10,reduced,x) == actual_eval(10,witness,x)
            checked += 1
    reports.append(dict(fixture=index, gates=gates, cpp=cpp,
                        independent_feasible=witness is not None,
                        independent_rows_checked=checked,
                        driver_stdout=result.stdout, driver_stderr=result.stderr))
(root/"phase-crosscheck.json").write_text(json.dumps(reports,indent=2)+"\n")
print(json.dumps(dict(fixtures=len(reports),
                     feasible=sum(r["independent_feasible"] for r in reports),
                     truth_rows=sum(r["independent_rows_checked"] for r in reports),
                     all_threshold_decisions_agree=True)))
