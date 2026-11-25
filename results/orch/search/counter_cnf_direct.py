import argparse,itertools,json,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('graph');p.add_argument('k',type=int);p.add_argument('--seconds',type=int,default=180);p.add_argument('--dirty',action='store_true');p.add_argument('--aux-mask',type=int);p.add_argument('--aux-last',action='store_true');p.add_argument('--allow-identity',action='store_true');a=p.parse_args()
d=json.loads(Path(a.graph).read_text());n=d['n'];k=a.k;rows=d['positive']+d['negative'];R=len(rows);P=len(d['positive']);clauses=[];nv=0
def new():
 global nv
 nv+=1;return nv
def neg(x):return not x if isinstance(x,bool)else-x
def add(*xs):
 if any(x is True for x in xs):return
 clauses.append(tuple(x for x in xs if x is not False))
def equiv_or(v,xs):
 add(-v,*xs)
 for x in xs:add(neg(x),v)
def equiv_and(v,xs):
 add(v,*[neg(x)for x in xs])
 for x in xs:add(-v,x)
def exactly_one(xs):
 pref=[xs[0]]
 for x in xs[1:]:
  v=new();equiv_or(v,[pref[-1],x]);add(-pref[-1],-x);pref.append(v)
 add(pref[-1]);return pref
V=[[bool(x>>i&1)for x in rows]for i in range(n)]+[[new()for _ in rows]for _ in range(k)]
ops=[new()for _ in range(k)];choices=[];prefix=[]
for j in range(k):
 cs=[(new(),op,u,v)for v in range(0 if a.allow_identity else 1,n+j)for u in range(v+1 if a.allow_identity else v)for op in [0,1]]
 choices.append(cs);prefix.append(exactly_one([q for q,_,_,_ in cs]))
 for q,op,u,v in cs:
  add(-q,ops[j]if op==0 else-ops[j])
  for r in range(R):
   x,y,z=V[u][r],V[v][r],V[n+j][r]
   if op==0:add(-q,neg(x),neg(y),z);add(-q,x,-z);add(-q,y,-z)
   else:add(-q,x,y,-z);add(-q,neg(x),z);add(-q,neg(y),z)
 for i in range(n):add(*[neg(z)if V[i][r]else z for r,z in enumerate(V[n+j])])
 add(*V[n+j]);add(*[-z for z in V[n+j]])
 if j:
  for c in range(len(prefix[j-1])):add(-prefix[j][c],prefix[j-1][c-1]if c else False)
aux=[]
if a.aux_mask is not None:
 auxpattern=[bool(x&a.aux_mask)for x in rows];graphpattern=[r<P for r in range(R)]
 lastpattern=auxpattern if a.aux_last else graphpattern;otherpattern=graphpattern if a.aux_last else auxpattern
 for j in range(k-1):
  v=new();equiv_and(v,[z if otherpattern[r]else-z for r,z in enumerate(V[n+j])]);aux.append(v)
 add(*aux)
else:lastpattern=[r<P for r in range(R)]
for r,z in enumerate(V[-1]):add(z if lastpattern[r]else-z)
for j in range(k-1):
 add(*[q for t in range(j+1,k)for q,op,u,v in choices[t]if u==n+j or v==n+j],aux[j]if aux else False)
if a.dirty:
 dirties=[]
 for j in range(k):
  v=new();some=new();equiv_or(some,V[n+j][P:]);equiv_and(v,[ops[j],some]);dirties.append(v)
 add(*dirties)
adj=[[False]*n for _ in range(n)]
for u,v in d['edges']:adj[u][v]=adj[v][u]=True
degree=[sum(r)for r in adj];mapping=[-1]*n;used=[False]*n;autos=[]
def rec():
 if all(x>=0 for x in mapping):autos.append(mapping.copy());return
 u=max((u for u in range(n)if mapping[u]<0),key=lambda u:(sum(adj[u][v]for v in range(n)if mapping[v]>=0),degree[u],-u))
 for v in range(n):
  if used[v]or degree[u]!=degree[v]or(a.aux_mask is not None and(a.aux_mask>>u&1)!=(a.aux_mask>>v&1)):continue
  if any(adj[u][x]!=adj[v][mapping[x]]for x in range(n)if mapping[x]>=0):continue
  mapping[u]=v;used[v]=True;rec();mapping[u]=-1;used[v]=False
rec();reps={min(tuple(sorted((q[u],q[v])))for q in autos)for u,v in itertools.combinations(range(n),2)}
for q,op,u,v in choices[0]:
 if(u,v)not in reps:add(-q)
stem='counter_direct_'+d['name']+'_'+str(k)+('_dirty'if a.dirty else'')+('_auxlast'if a.aux_last else'_aux'if a.aux_mask is not None else'')+('_id'if a.allow_identity else'')
base=Path('/tmp/oec/pequalnp-pilot-56');cnf=base/(stem+'.cnf')
with cnf.open('w')as f:
 f.write('p cnf %d %d\n'%(nv,len(clauses)))
 for cl in clauses:f.write(' '.join(map(str,cl))+' 0\n')
print('START',d['name'],'n',n,'k',k,'rows',R,'variables',nv,'clauses',len(clauses),'autos',len(autos),'cnfbytes',cnf.stat().st_size,flush=True)
t=time.time();outpath=base/(stem+'.out');errpath=base/(stem+'.err')
with outpath.open('w')as out,errpath.open('w')as err:rr=subprocess.run(['/tmp/oec/pequalnp-pilot-56/lean-4.36.0-linux/bin/cadical','-t',str(a.seconds),str(cnf)],stdout=out,stderr=err)
result=outpath.read_text();status='sat'if's SATISFIABLE'in result else'unsat'if's UNSATISFIABLE'in result else'unknown';print('RESULT',status,'seconds',time.time()-t,'exit',rr.returncode,flush=True)
if status=='sat':
 values={abs(int(v)):int(v)>0 for line in result.splitlines()if line.startswith('v ')for v in line[2:].split()if int(v)}
 gates=[]
 for cs in choices:
  chosen=[(op,u,v)for q,op,u,v in cs if values.get(q,False)];assert len(chosen)==1;gates.append(chosen[0])
 print('GATES',gates,flush=True)
 auxindices=[j for j,v in enumerate(aux)if values[v]]
 if aux:print('AUX_INDICES',auxindices,flush=True)
 def evals(x):
  ws=[bool(x>>i&1)for i in range(n)]
  for op,i,j in gates:ws.append((ws[i]or ws[j])if op else(ws[i]and ws[j]))
  return ws
 errors=[]
 mainout=n+auxindices[0]if a.aux_last else n+k-1
 auxout=n+k-1 if a.aux_last else n+auxindices[0]if aux else None
 for x in range(1<<n):
  ws=evals(x);want=any((x>>u&1)and(x>>v&1)for u,v in d['edges'])
  if ws[mainout]!=want or(auxout is not None and ws[auxout]!=bool(x&a.aux_mask)):errors.append(x)
 print('FULL_TABLE_ERRORS',errors,flush=True)
 (base/(stem+'_witness.json')).write_text(json.dumps({'graph':d,'gates':gates,'mainout':mainout,'auxout':auxout,'errors':errors},indent=2))
