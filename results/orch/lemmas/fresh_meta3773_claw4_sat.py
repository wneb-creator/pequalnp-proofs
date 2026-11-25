"""Four-arm restricted claw search. Every permitted use set has one of 11 S4 orbit types.
This run uses the exact set of used free features and explicitly requires all raw inputs.
With 10 binary gates there are 20 operand occurrences, against 9+9+k compulsory users.
"""
from pathlib import Path
import hashlib,itertools,json,resource,subprocess,sys,time
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(800<<20,800<<20))
job=Path(__file__).resolve().parent
F=[set(t) for l in [2,3,4] for t in itertools.combinations(range(4),l)]
def canon(G):return min(tuple(sorted(sum(1<<p[i] for i in T) for T in G)) for p in itertools.permutations(range(4)))
reps=sorted({canon(G)for k in range(3) for G in itertools.combinations(F,k)},key=lambda G:(-len(G),G));idx=int(sys.argv[1]); sec=int(sys.argv[2]); assert 0<sec<=120
free=reps[idx];n=9+len(free);budget=10;E=[(i,4)for i in range(4)]+[(i,5+i)for i in range(4)]
neg=[]
for P in range(16):
 y=sum((1<<j) for j in range(4,9) if not any(P>>i&1 and (i,j) in E for i in range(4))); neg.append(P|y)
pos=[(1<<i)|(1<<j) for i,j in E];tests=pos+neg
V=0; clauses=[]
def new():
 global V;V+=1;return V
def cl(*ls):
 if any(type(x)==bool and x for x in ls): return
 a={x for x in ls if type(x)!=bool}
 if any(-x in a for x in a): return
 clauses.append(tuple(sorted(a)))
def inv(x):return not x if type(x)==bool else -x
def onehot(xs):
 cl(*xs)
 for a,b in itertools.combinations(xs,2):cl(-a,-b)
A=[];B=[];O=[];Z=[]
for k in range(budget):
 h=n+k;A.append([new()for _ in range(h)]);B.append([new()for _ in range(h)]);onehot(A[-1]);onehot(B[-1]);O.append(new());Z.append([new()for _ in tests]);
 for a in range(h):
  for b in range(a):cl(-A[k][a],-B[k][b]);
 for t,raw in enumerate(tests):
  m=raw|sum((1<<(9+j)) for j,G in enumerate(free) if (raw>>5)&G)
  w1=new();w2=new();z=Z[k][t];op=O[k]
  for w,selector in [(w1,A[k]),(w2,B[k])]:
   for i,v in enumerate(selector):
    u=bool(m>>i&1) if i<n else Z[i-n][t];cl(-v,-w,u);cl(-v,w,inv(u))
  cl(-op,-w1,z);cl(-op,-w2,z);cl(-op,w1,w2,-z);cl(op,-z,w1);cl(op,-z,w2);cl(op,-w1,-w2,z)
for j in range(n+budget-1):
 uses=[s[j]for k in range(budget) for s in [A[k],B[k]] if j<len(s)];cl(*uses)
 if len(free)==2:
  for u,v in itertools.combinations(uses,2):cl(-u,-v)
# Canonical adjacent independent gates, ordered by (largest operand, smaller operand, OR flag).
for k in range(budget-1):
 h=n+k
 for b in range(h):
  for d in range(b):cl(-B[k][b],-B[k+1][d])
  for a in range(b+1):
   for c in range(a):cl(-B[k][b],-B[k+1][b],-A[k][a],-A[k+1][c])
   cl(-B[k][b],-B[k+1][b],-A[k][a],-A[k+1][a],-O[k],O[k+1]);
for t in range(len(tests)):cl(Z[-1][t]if t<len(pos) else -Z[-1][t]);
stem=job/f'fresh-meta3773-claw4-{idx}';cnf=stem.with_suffix('.cnf');cnf.write_text(f'p cnf {V} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
with stem.with_suffix('.log').open('w') as log:
 start=time.perf_counter(); r=subprocess.run([str(job/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'),'-t',str(sec),str(cnf)],cwd='/workspace/pequalnp-proofs',stdout=log,stderr=subprocess.STDOUT,timeout=sec+5); elapsed=time.perf_counter()-start
result={'index':idx,'free':free,'code':r.returncode,'seconds':elapsed,'hash':hashlib.sha256(cnf.read_bytes()).hexdigest(),'variables':V,'clauses':len(clauses)}
if r.returncode==10:
 model=set()
 for line in stem.with_suffix('.log').read_text().splitlines():
  if line.startswith('v '):model.update(int(v)for v in line[2:].split()if int(v)>0)
 gates=[('or' if O[k] in model else 'and',next(i for i,v in enumerate(A[k])if v in model),next(i for i,v in enumerate(B[k])if v in model)) for k in range(budget)];result['gates']=gates
 for raw in range(512):
  vals=[bool(raw>>i&1)for i in range(9)]+[bool((raw>>5)&G) for G in free]
  for op,i,j in gates:vals.append((vals[i] or vals[j]) if op=='or' else (vals[i] and vals[j]))
  assert vals[-1]==any(raw>>i&1 and raw>>j&1 for i,j in E)
result['num_orbits']=len(reps);stem.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
