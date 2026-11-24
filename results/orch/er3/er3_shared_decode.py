import itertools, json, sys
from pathlib import Path

meta=json.loads(Path(sys.argv[1]).read_text());s=Path(sys.argv[2]).read_text()
positive=set()
for line in s.splitlines():
    if line.startswith('v '):positive.update(int(x) for x in line[2:].split() if int(x)>0)
if not positive:
    print('no model');sys.exit(0)
n=meta['n'];gates=[]
def add(op,a,b):
    gates.append([op,a,b]);return n+len(gates)-1
def decode(block,rename):
    for ls,rs,op in block:
        ll=[i for i,x in enumerate(ls) if x in positive]
        rr=[i for i,x in enumerate(rs) if x in positive]
        assert len(ll)==len(rr)==1
        rename.append(add('or' if op in positive else 'and',rename[ll[0]],rename[rr[0]]))
    return rename
shared=decode(meta['shared'],meta['A'].copy())[4:]
pieces=[]
for block in meta['locals']:
    wires=decode(block['gates'],block['vertices']+shared)
    pieces.append(wires[-1])
B=meta['B'];u=add('and',B[0],B[1]);v=add('or',B[0],B[1]);w=add('and',B[2],v)
pieces.append(add('or',u,w));output=pieces[0]
for p in pieces[1:]:output=add('or',output,p)
assert len(gates)==meta['budget']
es={tuple(sorted(e)) for e in meta['edges']}
hood=[0]*n
for i,j in es:hood[i]|=1<<j;hood[j]|=1<<i
assert all((hood[i]&hood[j]).bit_count()<2 for i,j in itertools.combinations(range(n),2))
max_ind=0
for row in range(1<<n):
    ws=[bool(row>>i&1) for i in range(n)]
    want=any(ws[i] and ws[j] for i,j in es)
    if not want:max_ind=max(max_ind,row.bit_count())
    for op,a,b in gates:ws.append((ws[a] or ws[b]) if op=='or' else (ws[a] and ws[b]))
    assert ws[output]==want,('wrong truth row',row)
tau=n-max_ind;bound=len(es)+tau-1
result={'n':n,'edges':sorted(es),'gates':gates,'output':output,'tau':tau,'bound':bound,
        'full_truth_rows':1<<n,'is_counterexample':len(gates)<bound}
Path(sys.argv[3]).write_text(json.dumps(result,indent=2))
print(json.dumps({k:result[k] for k in ['n','tau','bound','full_truth_rows','is_counterexample']}))
print('gate count',len(gates))
