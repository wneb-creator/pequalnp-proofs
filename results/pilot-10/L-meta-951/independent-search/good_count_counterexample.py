import hashlib
import json
from pathlib import Path

n=5
S={0,1,2,3}
gates=[('not',[4]),('or',[5,0]),('or',[6,1]),('or',[7,2]),('or',[8,3]),
       ('or',[4,0]),('or',[10,1]),('or',[11,2]),('or',[12,3]),('and',[9,13])]
rows=[]
for assignment in range(1 << n):
    wires=[bool((assignment >> i) & 1) for i in range(n)]
    for op,inputs in gates:
        xs=[wires[i] for i in inputs]
        wires.append(not xs[0] if op=='not' else any(xs) if op=='or' else all(xs))
    assert wires[-1]==any((assignment >> i) & 1 for i in S)
    rows.append(wires)
outside=sum(1 << i for i in range(n) if i not in S)
good=[]
details=[]
for j,gate in enumerate(gates):
    w=n+j
    low=all(not row[w] or any((assignment >> i) & 1 for i in S) for assignment,row in enumerate(rows))
    high=all(row[w] or not any((assignment >> i) & 1 for i in S) for assignment,row in enumerate(rows))
    hits=sum(rows[1 << i][w] for i in S)
    good_wire=(low or high) and hits>=2 and not rows[outside][w]
    if good_wire:
        good.append(w)
    details.append({'wire':w,'gate':gate,'low':low,'high':high,'singleton_hits':hits,'outside_value':rows[outside][w],'good':good_wire})
assert good==[9,14]
print(json.dumps({'variables':n,'target':sorted(S),'gate_count':len(gates),'assignments_checked':len(rows),'not_count':sum(op=='not' for op,_ in gates),'good_wires':good,'good_count':len(good),'desired_but_false_good_lower_bound':len(S)-1,'details':details},indent=2))
print('program_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
