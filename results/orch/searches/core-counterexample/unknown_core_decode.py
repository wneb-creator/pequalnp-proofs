from pathlib import Path
import sys,json
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-71/core-counterexample')
from evaluator import Model
stem=Path(sys.argv[1]);meta=json.loads(stem.with_suffix('.meta.json').read_text());sol=stem.with_suffix('.sol').read_text();assert 's SATISFIABLE' in sol
true=set()
for line in sol.splitlines():
 if line.startswith('v '):true.update(int(x) for x in line.split()[1:] if int(x)>0)
def truth(lit):return lit in true if lit>0 else -lit not in true
for line in stem.with_suffix('.cnf').read_text().splitlines():
 if not line or line[0] in 'cp':continue
 clause=[int(x) for x in line.split() if x!='0'];assert any(truth(x) for x in clause),clause
n=meta['n'];left=meta['left'];edges=[e for e,v in zip(meta['edges'],meta['edgevars']) if truth(v)];gates=[]
for op,ss in zip(meta['ops'],meta['selectors']):
 ports=[]
 for side in ss:
  chosen=[a for a,v in enumerate(side) if truth(v)];assert len(chosen)==1;ports.append(chosen[0])
 gates.append((int(truth(op)),*ports))
M=Model(n,left,edges,'variable-graph-target')
if meta['control']!='c4':
 for a in range(left):
  for b in range(a):assert len(M.adj[a]&M.adj[b])<=1
ans=M.analyze(gates);assert ans is not None;t,s,D,mc,compact=ans
assert len(compact)==len(gates) and mc==len(meta['roots'])
assert M.base>=meta['matching']
cover=[a for a,z in enumerate(meta['cover']) if truth(z)]
for k,(a,b) in enumerate(M.edges):
 if not D>>k&1:assert a in cover or b in cover
assert M.tau(M.all^D)<=len(cover)
assert t==0 if meta['control']=='p4' else t<0
result=dict(n=n,left=left,edges=edges,gates=gates,roots=meta['roots'],D=D,accepted_edges=[e for k,e in enumerate(edges) if D>>k&1],U=len(compact),mc=mc,cover=cover,tau=M.base,residual_tau=M.tau(M.all^D),target_margin=t,stronger_margin=s,control=meta['control']);stem.with_suffix('.decoded.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['edges','gates','accepted_edges']}))
