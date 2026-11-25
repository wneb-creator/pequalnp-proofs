from pathlib import Path
import sys,json
meta=json.loads(Path(sys.argv[1]).read_text());d=json.loads(Path(meta['profile']).read_text());log=Path(sys.argv[2]).read_text()
if 's SATISFIABLE' not in log:
    print('NO SAT WITNESS');sys.exit(0)
assignment={abs(v):v>0 for line in log.splitlines() if line.startswith('v ') for v in map(int,line.split()[1:]) if v}
n=meta['n'];prog=[]
for z,ss in zip(meta['ops'],meta['choose']):
    a=[]
    for choices in ss:
        hits=[i for i,v in enumerate(choices) if assignment.get(v,False)]
        assert len(hits)==1
        a+=hits
    assert a[0]<a[1]
    prog.append(('and' if assignment[z] else 'or',a[0],a[1]))
prefix=[tuple(g) for g in d['prefix']];gates=prefix[:];mapping=d['preds'][:]
for op,a,b in prog:
    gates.append((op,mapping[a],mapping[b]));mapping.append(26+len(gates)-1)
if 'final_or_with' in d:
    gates.append(('or',d['final_or_with'],mapping[-1]));mapping.append(26+len(gates)-1)
out=mapping[-1]
def evaluate(s):
    w=[bool(s>>i&1) for i in range(26)]
    for j,(op,a,b) in enumerate(gates):
        assert a!=b and a<26+j and b<26+j
        w.append(w[a]or w[b] if op=='or' else w[a]and w[b])
    return w
def derivative(base,var):
    w=evaluate(base);v=[i==var for i in range(26)]
    for op,a,b in gates:v.append(v[a]or v[b] if op=='or' else(w[a]and v[b])or(v[a]and w[b]))
    return v[out]
edges=[(i,j) for i in range(13) for j in range(13) if(i-j)%13 in[0,1,3,9]]
pos=[(1<<i)|(1<<(13+j)) for i,j in edges]
neg=json.loads(Path('/tmp/oec/pequalnp-pilot-65/finite-search/plane-maxind.json').read_text())
bad=[s for s in pos if not evaluate(s)[out]]+[s for s in neg if evaluate(s)[out]]
dx=derivative(1,13);dy=derivative(1<<13,0)
report={'size':len(gates),'output':out,'bad_rows':bad,'dx':dx,'dy':dy,'window':prog,'gates':gates}
print(json.dumps({k:v for k,v in report.items() if k!='gates'}))
Path(sys.argv[3]).write_text(json.dumps(report,indent=2)+'\n')
assert not bad and not dx and not dy
