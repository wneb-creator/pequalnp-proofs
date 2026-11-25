from pathlib import Path
import os
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[key]='1'
import itertools,json,hashlib,time,resource,sys
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
j=Path('/tmp/oec/pequalnp-pilot-79');priority=sys.argv[1] if len(sys.argv)>1 else 'meta3773-cgp-79024-100-best.json';tag=sys.argv[2] if len(sys.argv)>2 else 'ordered1';assert tag.replace('-','').isalnum();start=time.monotonic();D={0,1,3,9};rows=[]
for p in range(13):
 for l in range(13):
  if (p+l)%13 in D:rows.append(((1<<p)|(1<<(13+l)),True))
for k in range(4):
 for sub in itertools.combinations(range(13),k):
  off=[l for l in range(13) if all((p+l)%13 not in D for p in sub)]
  a=sum(1<<p for p in sub);b=sum(1<<l for l in off)
  rows.extend([(a|(b<<13),False),(b|(a<<13),False)])
assert len(rows)==808
values=[sum(((m>>i)&1)<<t for t,(m,e) in enumerate(rows)) for i in range(26)]
index={v:i for i,v in enumerate(values)};assert len(index)==26
target=sum(int(e)<<t for t,(m,e) in enumerate(rows));inputs=[];seeds=[];initial=[]
names=(j/'root-meta3773-egraph-active-files.txt').read_text().splitlines();assert priority in names;names.remove(priority);names.insert(0,priority)
for name in names:
 p=j/name;raw=p.read_bytes();snap=j/'root-meta3773-egraph-inputs';snap.mkdir(exist_ok=True);(snap/(hashlib.sha256(raw).hexdigest()+'.json')).write_bytes(raw);d=json.loads(raw);gs=d['gates'];out=d.get('output',d.get('outputs',[None])[0]);assert type(out) is int and 0<=out<26+len(gs)
 inverse=d.get('operation_convention')=='0=OR,1=AND';wires=list(range(26));seed=[]
 for op,a,b in gs:
  assert type(op) is int and type(a) is int and type(b) is int
  op=1-op if inverse else op;assert op in [0,1] and 0<=a<len(wires) and 0<=b<len(wires)
  a,b=wires[a],wires[b];v=values[a]|values[b] if op else values[a]&values[b]
  if v not in index:index[v]=len(values);values.append(v)
  c=index[v];wires.append(c)
  if c not in [a,b]:seed.append((c,op,min(a,b),max(a,b)))
 seeds.append((wires[out],seed));inputs.append({'path':name,'sha256':hashlib.sha256(raw).hexdigest(),'gates':len(gs),'output_errors':(values[wires[out]]^target).bit_count()})
N=len(values);targetid=index[target];alts=[];byfunc=[[] for _ in range(N)]
for a in range(N):
 for b in range(a):
  for op,v in [(0,values[a]&values[b]),(1,values[a]|values[b])]:
   c=index.get(v)
   if c is not None and c>=26 and c not in [a,b] and v&target and targetid not in [a,b] and (c==targetid or (a<c and b<c)):
    byfunc[c].append(len(alts));alts.append((c,op,b,a))
A=len(alts);nv=2*N+A;ri=[];ci=[];data=[];lo=[];hi=[]
def row(items,l=-np.inf,u=np.inf):
 t=len(lo)
 for c,v in items:ri.append(t);ci.append(c);data.append(v)
 lo.append(l);hi.append(u)
for c in range(26,N):row([(N+a,1) for a in byfunc[c]]+[(c,-1)],0,0)
for a,(c,op,b,d) in enumerate(alts):
 z=N+a
 for child in [b,d]:
  row([(z,1),(child,-1)],u=0)
  # Rank constraints are redundant: strict seed order, with target last, already excludes cycles.
for c in range(26,N):
 if c!=targetid:row([(c,1)]+[(N+i,-1) for i,(_,op,a,b) in enumerate(alts) if c in [a,b]],u=0)
for c in range(26):row([(N+i,1) for i,(_,op,a,b) in enumerate(alts) if c in [a,b]],l=1)
row([(N+i,1) for i,(_,op,a,b) in enumerate(alts) if op==0],l=13)
row([(N+i,1) for i,(c,op,a,b) in enumerate(alts) if op==0 and values[c]&~target],l=1)
row([(i,1) for i in range(26,N)],u=63)
lower=np.zeros(nv);upper=np.ones(nv);upper[N+A:]=64
lower[:26]=1;upper[N+A:N+A+26]=0;lower[targetid]=1
cvec=np.zeros(nv);cvec[26:N]=1;integral=np.ones(nv);integral[N+A:]=0
matrix=coo_matrix((data,(ri,ci)),shape=(len(lo),nv)).tocsc()
# Verify the encoding admits a known64 gate seed when the sole budget is relaxed to64.
control=None;lookup={a:i for i,a in enumerate(alts)}
for out,seed in seeds:
 if out!=targetid:continue
 selected={};rank={i:0 for i in range(26)}
 for c,op,a,b in seed:
  if c<26 or c in selected:continue
  if a in rank and b in rank:selected[c]=(c,op,a,b);rank[c]=max(rank[a],rank[b])+1
 if targetid not in selected:continue
 needed=set()
 def visit(c):
  if c<26 or c in needed:return
  needed.add(c);_,_,a,b=selected[c];visit(a);visit(b)
 visit(targetid)
 if len(needed)>64:continue
 x=np.zeros(nv);x[:26]=1
 for c in needed:x[c]=1;x[N+lookup[selected[c]]]=1;x[N+A+c]=rank[c]
 v=matrix@x;lc=np.asarray(lo);uc=np.asarray(hi);uc[-1]=64;lc[-2]=0 # Bad-AND necessity applies only below64; relax it for this positive control.
 assert np.all(v>=lc-1e-7) and np.all(v<=uc+1e-7) and np.all(x>=lower) and np.all(x<=upper)
 control={'size':len(needed),'max_rank':max(rank[c] for c in needed),'all_constraints_pass':True,'control_relaxes_budget_to64_and_bad_AND_requirement':True};break
assert control is not None
meta={'scope':'Fixed-seed-order acyclic semantic egraph heuristic, with target last and additional raw-use,13-AND,and bad-AND cuts; all gates positive on an edge. Infeasibility applies only to this finite ordered pool over seed808-bit intermediate functions; infeasibility is only within this finite pool, not a global lower bound.','input_files':inputs,'priority_seed':priority,'functions':N,'alternatives':A,'variables':nv,'constraints':len(lo),'control':control,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
print(json.dumps({k:meta[k] for k in ['functions','alternatives','variables','constraints','control']}),flush=True)
res=milp(cvec,integrality=integral,bounds=Bounds(lower,upper),constraints=LinearConstraint(matrix,np.array(lo),np.array(hi)),options={'time_limit':60,'disp':True,'mip_rel_gap':0,'threads':1})
meta.update(status=int(res.status),message=str(res.message),seconds=time.monotonic()-start,mip_gap=float(res.mip_gap) if getattr(res,'mip_gap',None) is not None else None)
if res.x is not None:
 chosen={c:(op,a,b) for i,(c,op,a,b) in enumerate(alts) if res.x[N+i]>.5};mapping={i:i for i in range(26)};gs=[];active=set()
 def emit(c):
  if c in mapping:return mapping[c]
  assert c not in active;active.add(c);op,a,b=chosen[c];a=emit(a);b=emit(b);active.remove(c);mapping[c]=26+len(gs);gs.append([op,a,b]);return mapping[c]
 out=emit(targetid);vals=values[:26]
 for op,a,b in gs:vals.append(vals[a]|vals[b] if op else vals[a]&vals[b])
 assert vals[out]==target and len(gs)<=63
 meta.update(gates=gs,output=out,input_count=26,size=len(gs),errors=0)
(j/('root-meta3773-egraph-'+tag+'-result.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps({k:v for k,v in meta.items() if k not in ['input_files','gates']}),flush=True)
