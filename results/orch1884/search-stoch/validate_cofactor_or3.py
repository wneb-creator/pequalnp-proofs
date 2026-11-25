import ast
import json
import re
import sys
from pathlib import Path

edges = [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(4,6),(6,8),(8,5),(5,7),(7,4)]
full_edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def evaluate(gates, mask, supplied):
    w = supplied(mask)
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= a < len(w) and 0 <= b < len(w)
        w.append((w[a] and w[b]) if op == 0 else (w[a] or w[b]))
    return w[-1]

def cofactor_inputs(mask):
    w = [bool(mask >> i & 1) for i in range(9)]
    return w + [w[0] or w[3] or w[4]]

def full_inputs(mask):
    w = [bool(mask >> i & 1) for i in range(10)]
    return w + [not w[0]]

def target(mask, graph):
    return any(mask >> a & 1 and mask >> b & 1 for a, b in graph)

def lift(gates):
    out = [(1,1,4),(1,11,5)]
    def rename(i):
        return i + 1 if i < 9 else 12 if i == 9 else i + 3
    out += [(op, rename(a), rename(b)) for op,a,b in gates]
    cofactor_output = 12 + len(gates)
    new_and = 11 + len(out)
    out += [(0,0,12),(1,cofactor_output,new_and)]
    return out

def selftest():
    baseline = json.loads(Path('results/orch1884/search/cofactor-baseline16.json').read_text())
    shifted = [(op,a+(a>=9),b+(b>=9)) for op,a,b in baseline]
    for mask in range(512):
        assert evaluate(shifted, mask, cofactor_inputs) == target(mask, edges)
    full = lift(shifted)
    assert len(full) == 20
    for mask in range(1024):
        assert evaluate(full, mask, full_inputs) == target(mask, full_edges)
    print('SELFTEST_PASS known16 cofactor512 rows; lifted20 Petersen1024 rows')

if sys.argv[1] == 'selftest':
    selftest()
    sys.exit(0)

log, prefix = Path(sys.argv[1]), Path(sys.argv[2])
reports = []
for line in log.read_text().splitlines():
    if line.startswith('best '):
        match = re.fullmatch(r'best (\d+) trial (\d+) gates (\[.*\])', line)
        assert match
        gates = ast.literal_eval(match[3])
        assert len(gates) == 14
        errors = []
        fp = fn = 0
        for mask in range(512):
            actual = evaluate(gates, mask, cofactor_inputs)
            wanted = target(mask, edges)
            if actual != wanted:
                errors.append(mask)
                fp += actual
                fn += not actual
        assert 4*fp+fn == int(match[1])
        report = dict(trial=int(match[2]),weighted_score=4*fp+fn,false_positive=fp,false_negative=fn,errors=errors)
        reports.append(report)
        prefix.with_name(prefix.name+'-best.json').write_text(json.dumps(dict(inputs=10,output=23,free_or=[0,3,4],gates=gates,validation=report),indent=2)+'\n')
    elif line.startswith(('COFACTOR_WITNESS ', 'FULL_WITNESS ')):
        label, payload = line.split(' ',1)
        candidate = json.loads(payload)
        is_full = label == 'FULL_WITNESS'
        assert len(candidate['gates']) == (18 if is_full else 14)
        assert candidate['output'] == (28 if is_full else 23)
        for mask in range(1024 if is_full else 512):
            assert evaluate(candidate['gates'], mask, full_inputs if is_full else cofactor_inputs) == target(mask,full_edges if is_full else edges)
        candidate['assignments_verified'] = 1024 if is_full else 512
        prefix.with_name(prefix.name+('-full-witness.json' if is_full else '-cofactor-witness.json')).write_text(json.dumps(candidate,indent=2)+'\n')
prefix.with_name(prefix.name+'-validation.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k != 'errors'} for r in reports]))
