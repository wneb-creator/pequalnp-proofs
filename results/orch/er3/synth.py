import argparse,itertools,json,time,subprocess
from pathlib import Path

class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def clause(self,*ls):self.cs.append(list(ls))
 def onehot(self,vs):
  self.cs.append(vs)
  for a,b in itertools.combinations(vs,2):self.clause(-a,-b)
 def equiv(self,a,b,cond=None):
  p=[] if cond is None else [-cond]
  self.clause(*p,-a,b);self.clause(*p,a,-b)
 def andv(self,a,b):
  c=self.var();self.clause(-c,a);self.clause(-c,b);self.clause(c,-a,-b);return c
 def orv(self,a,b):
  c=self.var();self.clause(c,-a);self.clause(c,-b);self.clause(-c,a,b);return c
 def threshold(self,vs,r):
  zero=self.var();self.clause(-zero)
  one=self.var();self.clause(one)
  row=[one]+[zero]*r
  for v in vs:
   row=[one]+[self.orv(row[j],self.andv(v,row[j-1])) for j in range(1,r+1)]
  return row[r]

def generate(n,e,t,out,graph=None,template=None,distance=3,k_override=None,and_count=None,fixed_gates=None):
 fixed_prefix=[] if fixed_gates is None else json.loads(Path(fixed_gates).read_text())
 k=e+t-2 if k_override is None else k_override;c=CNF();edges={p:c.var() for p in itertools.combinations(range(n),2)}
 E=lambda i,j:edges[tuple(sorted((i,j)))]
 c.clause(c.threshold(list(edges.values()),e))
 # C4 exclusion.
 for a,b,d,f in itertools.combinations(range(n),4):
  for cyc in [(a,b,d,f),(a,b,f,d),(a,d,b,f)]:
   c.clause(*[-E(cyc[i],cyc[(i+1)%4]) for i in range(4)])
 # Every set of n-t+1 vertices contains an edge, so cover number >=t.
 for s in itertools.combinations(range(n),n-t+1):c.clause(*[E(i,j) for i,j in itertools.combinations(s,2)])
 if graph is not None:
  g=json.loads(Path(graph).read_text());fixed={tuple(sorted(p)) for p in g['edges']}
  for p,v in edges.items():c.clause(v if p in fixed else -v)
  rows=[(1<<i)|(1<<j) for i,j in fixed]
  for x in range(1<<n):
   independent=lambda y:not any((y>>i&1) and (y>>j&1) for i,j in fixed)
   if independent(x) and all(not independent(x|(1<<i)) for i in range(n) if not(x>>i&1)):rows.append(x)
  rows=sorted(set(rows))
 else:rows=list(range(1<<n))
 vals=[];gates=[]
 for i in range(n):
  v=[]
  for x in rows:
   q=c.var();c.clause(q if (x>>i)&1 else -q);v.append(q)
  vals.append(v)
 for z in range(k):
  m=len(vals);ls=[c.var() for _ in range(m)];rs=[c.var() for _ in range(m)];op=c.var()
  c.onehot(ls);c.onehot(rs)
  for i in range(m):
   for j in range(i+1):c.clause(-ls[i],-rs[j])
  if z==0 and graph is None and fixed_gates is None:c.clause(ls[0]);c.clause(rs[1])
  if gates and template is None and fixed_gates is None:
   oldl,oldr,oldo=gates[-1]
   for i,u in enumerate(oldr):
    for j,v in enumerate(rs):
     if i>j:c.clause(-u,-v)
   for i,u in enumerate(oldr):
    for j,a in enumerate(oldl):
     for jj,b in enumerate(ls):
      if j>jj:c.clause(-u,-rs[i],-a,-b)
  v=[]
  for row,x in enumerate(rows):
   a,b,y=c.var(),c.var(),c.var();v.append(y)
   for i in range(m):c.equiv(a,vals[i][row],ls[i]);c.equiv(b,vals[i][row],rs[i])
   # op=true means OR; false means AND.
   c.clause(op,-y,a);c.clause(op,-y,b);c.clause(op,y,-a,-b)
   c.clause(-op,y,-a);c.clause(-op,y,-b);c.clause(-op,-y,a,b)
  vals.append(v);gates.append((ls,rs,op))
 if and_count is not None:
  assert 0<=and_count<=k
  and_variables=[-op for ls,rs,op in gates]
  c.clause(c.threshold(and_variables,and_count))
  if and_count<k:c.clause(-c.threshold(and_variables,and_count+1))
 for row,x in enumerate(rows):
  present=[v for (i,j),v in edges.items() if ((x>>i)&1) and ((x>>j)&1)]
  y=vals[-1][row]
  c.clause(-y,*present)
  for v in present:c.clause(y,-v)
 # Every gate before output has at least one syntactic use.
 for z in range(k-1):
  if z<len(fixed_prefix):continue
  uses=[]
  for ls,rs,op in gates[z+1:]:uses.extend([ls[n+z],rs[n+z]])
  c.clause(*uses)
 for z,(operation,a,b) in enumerate(fixed_prefix):
  a,b=sorted((a,b));assert 0<=a<b<n+z
  ls,rs,op=gates[z];c.clause(ls[a]);c.clause(rs[b]);c.clause(op if operation=='or' else -op)
 if template is not None:
  seed=json.loads(Path(template).read_text())['gates'];assert len(seed)==k
  matches=[]
  for (ls,rs,op),(o,a,b) in zip(gates,seed):
   a,b=sorted((a,b));lit=op if o=='or' or o==1 else -op
   matches.append(c.andv(c.andv(ls[a],rs[b]),lit))
  c.clause(c.threshold(matches,k-distance))
 p=Path(out);p.write_text('p cnf %d %d\n'%(c.n,len(c.cs))+''.join(' '.join(map(str,a))+' 0\n' for a in c.cs))
 meta={'n':n,'e':e,'t':t,'k':k,'and_count':and_count,'edges':[(i,j,v) for (i,j),v in edges.items()],'gates':gates,'variables':c.n,'clauses':len(c.cs)}
 p.with_suffix('.json').write_text(json.dumps(meta))
 print(json.dumps({q:meta[q] for q in ['n','e','t','k','variables','clauses']}),flush=True)

def decode(meta_path,answer):
 d=json.loads(Path(meta_path).read_text());vs=set()
 for ln in Path(answer).read_text().splitlines():
  if ln.startswith('v '):vs.update(int(x) for x in ln[2:].split() if int(x)>0)
 if not vs:print('no model');return
 n=d['n'];es=[(i,j) for i,j,v in d['edges'] if v in vs];gs=[]
 for ls,rs,op in d['gates']:
  gs.append(('or' if op in vs else 'and',next(i for i,v in enumerate(ls) if v in vs),next(i for i,v in enumerate(rs) if v in vs)))
 for x in range(1<<n):
  ws=[bool((x>>i)&1) for i in range(n)]
  for op,a,b in gs:ws.append((ws[a] or ws[b]) if op=='or' else (ws[a] and ws[b]))
  want=any(ws[i] and ws[j] for i,j in es)
  assert ws[-1]==want,(x,ws[-1],want)
 tau=next(r for r in range(n+1) if any(all(i in s or j in s for i,j in es) for s in map(set,itertools.combinations(range(n),r))))
 hood=[0]*n
 for i,j in es:hood[i]|=1<<j;hood[j]|=1<<i
 assert all((hood[i]&hood[j]).bit_count()<2 for i,j in itertools.combinations(range(n),2))
 print(json.dumps({'n':n,'edges':es,'tau':tau,'gates':gs,'lower_bound':len(es)+tau-1,'truth_table_verified':True,'c4_free_verified':True,'is_counterexample':len(gs)<len(es)+tau-1},indent=2))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--n',type=int);p.add_argument('--k',type=int);p.add_argument('--and-count',type=int);p.add_argument('--fixed-gates');p.add_argument('--e',type=int);p.add_argument('--t',type=int);p.add_argument('--out');p.add_argument('--graph');p.add_argument('--template');p.add_argument('--distance',type=int,default=3);p.add_argument('--decode',nargs=2);a=p.parse_args()
 if a.decode:decode(*a.decode)
 else:generate(a.n,a.e,a.t,a.out,a.graph,a.template,a.distance,a.k,a.and_count,a.fixed_gates)
