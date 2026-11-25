import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-86/read1-construction/c6-11-sym')
data=json.loads(base.with_suffix('.json').read_text())
source=base.with_suffix('.cnf').read_text().splitlines()
assert source[0].split()[:2]==['p','cnf']
variables=int(source[0].split()[2]); clauses=[list(map(int,line.split()[:-1])) for line in source[1:] if line and not line.startswith('c')]
assert len(clauses)==int(source[0].split()[3])
def var():
 global variables
 variables+=1;return variables
def clause(*xs):
 out=[]
 for x in xs:
  if type(x) is bool:
   if x:return
   continue
  if -x in out:return
  if x not in out:out.append(x)
 clauses.append(out)
def neg(x):return not x if type(x) is bool else -x
def iff_mux(z,sel,vals):
 for s,w in zip(sel,vals):
  clause(-s,-z,w);clause(-s,z,neg(w))
def andeq(z,a,b):
 clause(-z,a);clause(-z,b);clause(z,neg(a),neg(b))
def ore_cond(z,a,b,cond):
 clause(neg(cond),z,neg(a));clause(neg(cond),z,neg(b));clause(neg(cond),-z,a,b)
n=data['n']; A=data['A'];B=data['B'];O=data['O'];V=data['V']; s=len(O)
below=[]
for i in range(s):
 z=var();below.append(z)
 for t in range(data['positive'],len(data['tests'])):clause(-z,-V[i][t])
 clause(z,*[V[i][t] for t in range(data['positive'],len(data['tests']))])
for i in range(s):
 ba=var();bb=var();vals=[False]*n+below[:i]
 iff_mux(ba,A[i],vals);iff_mux(bb,B[i],vals)
 # OR inputs have the same below-output status.
 clause(-O[i],-ba,bb);clause(-O[i],ba,-bb)
 # An AND input is not below output.
 clause(O[i],-ba);clause(O[i],-bb)
p,q=data['edges'][0]
mono=[]
for i in range(s):
 av=[];bv=[]
 for component in range(3):
  za=var();zb=var();av.append(za);bv.append(zb)
  initial=[(j==p if component==0 else j==q if component==1 else False) for j in range(n)]
  values=initial+[row[component] for row in mono]
  iff_mux(za,A[i],values);iff_mux(zb,B[i],values)
 current=[var() for _ in range(3)];mono.append(current)
 for c in [0,1]:
  # Singleton monomial occurs only through OR gates.
  clause(O[i],-current[c]);ore_cond(current[c],av[c],bv[c],O[i])
 ore_cond(current[2],av[2],bv[2],O[i])
 u=var();v=var();andeq(u,av[0],bv[1]);andeq(v,av[1],bv[0])
 ore_cond(current[2],u,v,-O[i])
clause(-mono[-1][2])
out=Path('/tmp/oec/pequalnp-pilot-86/read1-construction/c6-11-normalized-not-read1')
with out.with_suffix('.cnf').open('w') as f:
 f.write(f'p cnf {variables} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
data.update(below=below,monomial=mono,probe_edge=[p,q])
out.with_suffix('.json').write_text(json.dumps(data))
print('variables',variables,'clauses',len(clauses),'probe_edge',[p,q])
