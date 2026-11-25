import argparse,itertools,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--graph',choices=['c5','theta233','petersen','friendship2'],default='theta233');p.add_argument('--or-gates',type=int,required=True);p.add_argument('--pair-only',action='store_true');p.add_argument('--out',required=True);p.add_argument('--decode');a=p.parse_args();k=a.or_gates
if a.graph=='theta233':n=7;edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
elif a.graph=='petersen':
 pairs=list(itertools.combinations(range(5),2));n=10;edges=[(i,j) for i in range(n) for j in range(i+1,n) if not set(pairs[i])&set(pairs[j])]
elif a.graph=='friendship2':n=5;edges=[(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)]
else:n=5;edges=[(i,(i+1)%5) for i in range(5)]
E={frozenset(e) for e in edges}
if a.pair_only:samples=[((1<<u)|(1<<v),int(frozenset((u,v)) in E)) for u,v in itertools.combinations(range(n),2)]+[(1<<v,0) for v in range(n)]+[(0,0)]
else:
 ind=[x for x in range(1<<n) if not any((x>>u)&1 and (x>>v)&1 for u,v in edges)]
 mx=[x for x in ind if all((x|(1<<v)) not in ind for v in range(n) if not ((x>>v)&1))]
 samples=[((1<<u)|(1<<v),1) for u,v in edges]+[(x,0) for x in mx]
V={};clauses=[]
def var(key):
 if key not in V:V[key]=len(V)+1
 return V[key]
def clause(*xs):clauses.append(tuple(xs))
def sources(t):return [('false',0)]+[('input',j) for j in range(n)]+[('or',j) for j in range(t)]
def meet(label,t):
 src=sources(t)
 for w in src:var(('sel',label,w))
 for i,(x,target) in enumerate(samples):
  z=var(('meet',label,i));bad=[]
  for w in src:
   sel=var(('sel',label,w))
   if w[0]=='false' or (w[0]=='input' and not ((x>>w[1])&1)):bad.append(sel)
   elif w[0]=='or':
    q=var(('orval',w[1],i));b=var(('bad',label,w[1],i));bad.append(b)
    clause(-b,sel);clause(-b,-q);clause(b,-sel,q)
  for b in bad:clause(-z,-b)
  clause(z,*bad)
 return src
for t in range(k):
 src=meet((t,0),t);meet((t,1),t)
 # Order two selector bitmasks lexicographically from most significant bit.
 eq=var(('prefixeq',t,len(src)));clause(eq)
 for j in reversed(range(len(src))):
  u=var(('sel',(t,0),src[j]));v=var(('sel',(t,1),src[j]))
  clause(-eq,-u,v)
  ne=var(('prefixeq',t,j))
  clause(-ne,eq);clause(-ne,-u,v);clause(-ne,u,-v)
  clause(-eq,-u,-v,ne);clause(-eq,u,v,ne)
  eq=ne
 for i,_ in enumerate(samples):
  y=var(('orval',t,i));u=var(('meet',(t,0),i));v=var(('meet',(t,1),i))
  clause(-u,y);clause(-v,y);clause(u,v,-y)
meet('output',k)
for i,(_,target) in enumerate(samples):clause(var(('meet','output',i)) if target else -var(('meet','output',i)))
meta={'graph':a.graph,'n':n,'edges':edges,'or_gates':k,'and_gates':'unbounded via meet closure','pair_only':a.pair_only,'samples':samples,'variables':len(V),'clauses':len(clauses)}
if a.decode:
 model={}
 for l in Path(a.decode).read_text().splitlines():
  if l.startswith('v '):
   for s in l.split()[1:]:
    v=int(s)
    if v:model[abs(v)]=v>0
 assert all(any(model.get(abs(v),False)==(v>0) for v in c) for c in clauses),'CNF assignment failed validation'
 choices={}
 for t in range(k):
  for side in [0,1]:choices[str((t,side))]=[w for w in sources(t) if model[var(('sel',(t,side),w))]]
 choices['output']=[w for w in sources(k) if model[var(('sel','output',w))]]
 def calc(x):
  ovs=[]
  def m(ws):return all(False if typ=='false' else bool((x>>j)&1) if typ=='input' else ovs[j] for typ,j in ws)
  for t in range(k):ovs.append(m(choices[str((t,0))]) or m(choices[str((t,1))]))
  return m(choices['output'])
 for x in range(1<<n):
  if not a.pair_only or x.bit_count()<=2:assert calc(x)==any((x>>u)&1 and (x>>v)&1 for u,v in edges),(x,choices)
 meta['witness']=choices;meta['independent_validation']='All CNF clauses and all required Boolean inputs checked'
 Path(a.out+'.witness.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
else:
 Path(a.out+'.cnf').write_text('p cnf '+str(len(V))+' '+str(len(clauses))+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
 Path(a.out+'.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
