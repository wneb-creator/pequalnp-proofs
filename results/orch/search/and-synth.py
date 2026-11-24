import argparse,itertools,json
from pathlib import Path
from synth import CNF
p=argparse.ArgumentParser();p.add_argument('graph');p.add_argument('--ands',type=int,required=True);p.add_argument('--size',type=int);p.add_argument('--out',required=True);a=p.parse_args()
g=json.loads(Path(a.graph).read_text());n=g['n'];es={tuple(e)for e in g['edges']};k=a.ands
ind=lambda x:not any((x>>i&1)and(x>>j&1)for i,j in es)
rows=sorted(set([(1<<i)|(1<<j)for i,j in es]+[x for x in range(1<<n)if ind(x)and all(not ind(x|(1<<i))for i in range(n)if not(x>>i&1))]))
c=CNF();vals=[];gates=[];selectors=[]
for i in range(n):
 vs=[c.var()for x in rows]
 for x,v in zip(rows,vs):c.clause(v if x>>i&1 else -v)
 vals.append(vs)
for z in range(k):
 m=len(vals);sels=[[c.var()for i in range(m)]for j in range(2)];selectors.extend(sels[0]+sels[1]);gates.append(sels)
 for sel in sels:c.clause(*sel)
 # Sort the two OR operands numerically; AND is commutative.
 equal=c.var();c.clause(equal)
 for abit,bbit in reversed(list(zip(sels[0],sels[1]))):
  c.clause(-equal,-abit,bbit)
  q=c.var();c.clause(-q,-abit,bbit);c.clause(-q,abit,-bbit);c.clause(q,abit,bbit);c.clause(q,-abit,-bbit)
  equal=c.andv(equal,q)
 # A priority topological ordering makes maximum selected source nondecreasing.
 if z:
  old=gates[z-1]
  for side in old:
   for i,v in enumerate(side):c.clause(-v,*sels[0][i:],*sels[1][i:])
 vs=[]
 for row,x in enumerate(rows):
  operands=[]
  for sel in sels:
   terms=[c.andv(v,vals[i][row])for i,v in enumerate(sel)];y=c.var();c.clause(-y,*terms)
   for term in terms:c.clause(-term,y)
   operands.append(y)
  vs.append(c.andv(*operands))
 vals.append(vs)
outs=[c.var()for z in range(k)];selectors.extend(outs);c.clause(*outs)
for row,x in enumerate(rows):
 terms=[c.andv(v,vals[n+i][row])for i,v in enumerate(outs)];y=c.var();c.clause(-y,*terms)
 for term in terms:c.clause(-term,y)
 c.clause(y if not ind(x)else -y)
# Each generated AND must be selected later or at output.
for z in range(k):c.clause(outs[z],*[s[n+z]for later in gates[z+1:]for s in later])
if a.size is not None:
 # With nonempty OR input lists, expansion costs sum(fanins)-k-1.
 c.clause(-c.threshold(selectors,a.size+k+2))
p=Path(a.out);p.write_text('p cnf %d %d\n'%(c.n,len(c.cs))+''.join(' '.join(map(str,v))+' 0\n'for v in c.cs));p.with_suffix('.json').write_text(json.dumps({'n':n,'edges':list(es),'ands':k,'size_limit':a.size,'gates':gates,'outs':outs,'rows':rows,'variables':c.n,'clauses':len(c.cs)}))
print('vars',c.n,'clauses',len(c.cs),'rows',len(rows),'ands',k,'size',a.size,flush=True)
