import itertools
import json
import re
from pathlib import Path

def php():
    rows = [tuple(4*p+h+1 for h in range(4)) for p in range(5)]
    blocks = [(-(4*p+h+1), -(4*q+h+1)) for p in range(5) for q in range(p+1,5) for h in range(4)]
    return rows + blocks

def propagation(db, assumptions):
    true = set(assumptions)
    assert all(-l not in true for l in true)
    trace = []
    while True:
        changed = False
        for i, clause in enumerate(db):
            if any(l in true for l in clause):
                continue
            unassigned = [l for l in clause if -l not in true]
            if not unassigned:
                return True, trace + [i]
            if len(unassigned) == 1:
                literal = unassigned[0]
                assert -literal not in true
                true.add(literal)
                trace.append(i)
                changed = True
        if not changed:
            return False, trace

def rup(db, clause):
    assert len(set(clause)) == len(clause)
    assert all(-l not in clause for l in clause)
    return propagation(db, [-l for l in clause])

def verify(run):
    db = php()
    traces = []
    for i, c in enumerate(run):
        okay, trace = rup(db, c)
        if not okay:
            return False, i, traces
        traces.append(trace)
        db.append(tuple(c))
    return bool(run) and len(run[-1]) == 0, len(run), traces

def library_baseline():
    text = Path('lean/PEqualNP/Outside/L_meta_9250.lean').read_text()
    result = []
    for i in range(20):
        line = next(line for line in text.splitlines() if line.startswith(f'def c{i} :'))
        clause = []
        for p, h, b in re.findall(r'\(\((\d+), (\d+)\), (true|false)\)', line):
            v = 4*int(p)+int(h)+1
            clause.append(v if b == 'true' else -v)
        result.append(clause)
    assert verify(result)[0]
    return result

if __name__ == '__main__':
    base = Path('results/orch9248/search-alt')
    run = library_baseline()
    okay, count, traces = verify(run)
    (base/'baseline20.json').write_text(json.dumps(dict(order='oldest first',encoding='signed(pigeon*4+hole+1)',run=run,traces=traces,valid=okay,length=count),indent=2)+'\n')
    print(f'BASELINE_VALID {okay} clauses={count}')
