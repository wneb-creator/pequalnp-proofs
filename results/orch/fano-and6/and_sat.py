import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--graph',choices=['fano','cycle12'],default='fano');p.add_argument('--ands',type=int,default=6);p.add_argument('--t0',action='store_true');a=p.parse_args()
if a.graph=='fano':
 left=right=7;edges=[(i,7+j) for j in range(7) for i in (j,(j+1)%7,(j+3)%7)]
else:
 left=right=6;edges=[(i,6+j) for i in range(6) for j in (i,(i+1)%6)]
n=left+right;k=a.ands;full=(1<<n)-1
ind=[]
for mask in range(1<<n):
 if any((mask>>u&1) and (mask>>v&1) for u,v in edges):continue
 if all(any((((mask|(1<<i))>>u)&1) and (((mask|(1<<i))>>v)&1) for u,v in edges) for i in range(n) if not(mask>>i&1)):ind.append(mask)
patterns=[((1<<u)|(1<<v),True) for u,v in edges]+[(m,False) for m in ind]
clauses=[];variables=[]
def var(label): variables.append(label);return len(variables)
def add(*xs):clauses.append(list(xs))
def conj(s,t,label):
 z=var(label);add(-z,s);add(-z,t);add(z,-s,-t);return z
def disj(xs,label):
 z=var(label)
 for s in xs:add(-s,z)
 add(-z,*xs);return z
selectors=[[[var(['select',j,b,i]) for i in range(n+j)] for b in range(2)] for j in range(k)]
outputs=[var(['output',j]) for j in range(k)]
add(outputs[-1])
for j in range(k):
 for b in range(2):
  add(*selectors[j][b])
  if a.t0:
   col=var(['colour',j,b])
   for i in range(n):add(-selectors[j][b][i],col if i>=left else -col)
 if j<k-1:add(outputs[j],*[selectors[h][b][n+j] for h in range(j+1,k) for b in range(2)])
 # Lex symmetry of the two operands, least index first.
 pref=var(['prefix',j,0]);add(pref)
 for i in range(n+j):
  x,y=selectors[j][0][i],selectors[j][1][i]
  add(-pref,-x,y)
  nex=var(['prefix',j,i+1])
  add(-nex,pref);add(-nex,-x,y);add(-nex,x,-y)
  add(-pref,x,y,nex);add(-pref,-x,-y,nex)
  pref=nex
for pi,(mask,target) in enumerate(patterns):
 values=[]
 for j in range(k):
  ops=[]
  for b in range(2):
   terms=[selectors[j][b][i] for i in range(n) if mask>>i&1]
   terms += [conj(selectors[j][b][n+h],values[h],['term',pi,j,b,h]) for h in range(j)]
   ops.append(disj(terms,['operand',pi,j,b]))
  values.append(conj(ops[0],ops[1],['gate',pi,j]))
 terms=[conj(outputs[j],values[j],['outputterm',pi,j]) for j in range(k)]
 if target:add(*terms)
 else:
  for term in terms:add(-term)
name=f'{a.graph}-{k}and-'+('t0' if a.t0 else 'general')
root=Path('/tmp/oec/pequalnp-pilot-157')
(root/(name+'.cnf')).write_text(f'p cnf {len(variables)} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
(root/(name+'.json')).write_text(json.dumps(dict(n=n,left=left,right=right,edges=edges,k=k,patterns=patterns,selectors=selectors,outputs=outputs,variables=variables,t0=a.t0)))
print(name,'inputs',n,'edges',len(edges),'maximal independent sets',len(ind),'variables',len(variables),'clauses',len(clauses))
