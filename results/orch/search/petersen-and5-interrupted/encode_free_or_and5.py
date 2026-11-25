import runpy,time,json,itertools
from pathlib import Path
core=runpy.run_path('/tmp/oec/pequalnp-pilot-87/proof_structure/tiny_graph_counts.py')
CNF,lib,CB=core['CNF'],core['lib'],core['CB']
def encode(n,edges,k):
 c=CNF();sels=[([c.var() for _ in range(n+i)],[c.var() for _ in range(n+i)]) for i in range(k)];final=[c.var() for _ in range(k)]
 for row in range(1<<n):
  gs=[]
  for i,(left,right) in enumerate(sels):
   args=[]
   for ss in [left,right]:
    ts=[ss[j] for j in range(n) if row>>j&1]
    for j,v in enumerate(gs):
     s=ss[n+j];t=c.var();c.add(-t,s);c.add(-t,v);c.add(t,-s,-v);ts.append(t)
    a=c.var();c.add(-a,*ts)
    for t in ts:c.add(-t,a)
    args.append(a)
   a,b=args;z=c.var();c.add(-z,a);c.add(-z,b);c.add(z,-a,-b);gs.append(z)
  out=[]
  for s,v in zip(final,gs):
   t=c.var();c.add(-t,s);c.add(-t,v);c.add(t,-s,-v);out.append(t)
  yes=any((row>>a)&(row>>b)&1 for a,b in edges)
  if yes:c.add(*out)
  else:
   for t in out:c.add(-t)
 return c,sels,final
if __name__=='__main__':
 import hashlib
 out=Path('/tmp/oec/pequalnp-pilot-87/proof_structure/petersen-and5-long');out.mkdir(exist_ok=True)
 edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
 c,sels,final=encode(10,edges,5)
 assert c.n==41085 and len(c.cs)==175408
 path=out/'problem.cnf'
 with path.open('w') as f:
  f.write(f'p cnf {c.n} {len(c.cs)}\n')
  for row in c.cs:f.write(' '.join(map(str,row))+' 0\n')
 metadata={'n':10,'edges':edges,'and_cap':5,'or_cap':None,'variables':c.n,'clauses':len(c.cs),'selectors':sels,'output_selectors':final,'cnf_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'scope':'All1024assignments; arbitrary OR subsets of input and earlier AND outputs; no gate-order or irredundancy constraints.'}
 (out/'encoding.json').write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata,indent=2))
