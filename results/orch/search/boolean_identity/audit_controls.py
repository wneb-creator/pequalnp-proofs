from itertools import chain
from pathlib import Path
import json

D=Path(__file__).resolve().parent

def verify(name,neighborhoods):
    saved=json.loads((D/name).read_text())
    gates=saved['circuit']; left=len(neighborhoods); right=1+max(chain.from_iterable(neighborhoods))
    assert all(op in (0,1) and max(a,b)<left+right+i and min(a,b)>=0 for i,(op,a,b) in enumerate(gates))
    def output(a,b):
        vals=[bool(a>>i&1) for i in range(left)]+[bool(b>>j&1) for j in range(right)]
        for op,i,j in gates:
            vals.append(vals[i] and vals[j] if op else vals[i] or vals[j])
        return vals[-1]
    pos=sum(len(s) for s in neighborhoods)
    assert all(output(1<<i,1<<j) for i,s in enumerate(neighborhoods) for j in s)
    rows=[sum(1<<j for j in s) for s in neighborhoods]
    for b in range(1<<right):
        a=sum(1<<i for i,s in enumerate(rows) if not b&s)
        assert not output(a,b)
    print(name,len(gates),pos,1<<right)

q3=[{l for l in range(13) if (p-l)%13 in (0,1,3,9)} for p in range(13)]
affine_points=[p for p,s in enumerate(q3) if 0 not in s]
affine=[{i for i,p in enumerate(affine_points) if l in q3[p]} for l in range(1,13)]
grid=[{i,j+4} for i in range(4) for j in range(4)]+[set(range(4)),set(range(4,8))]
verify('direct65-control.json',q3)
verify('best-76131.json',q3)
for name in ('two-pencil-best-48.json','two-pencil-best-49.json'):verify(name,grid)
for f in sorted(D.glob('affine-best-*.json')):verify(f.name,affine)
