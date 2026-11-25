from pathlib import Path
import itertools,json,resource,subprocess,time,os,sys,hashlib
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
job=Path('/tmp/oec/pequalnp-pilot-79');label=sys.argv[1];budget=int(sys.argv[2]);seconds=int(sys.argv[3]);assert 1<=budget<=63;assert label in ['c6','c8','three_stars','four_stars','k4sub','theta'];assert 0<seconds<=180
if label in ['three_stars','four_stars']:
 points=[0,1,2] if label=='three_stars' else [0,1,2,5];count=len(points);D={0,1,3,9};rs=sorted({(d-i)%13 for i in points for d in D});n=count+len(rs);edges=sorted((j,count+rs.index((d-i)%13)) for j,i in enumerate(points) for d in D)
elif label=='theta':
 n=8;edges=[e for i in range(3) for e in [(0,2+2*i),(2+2*i,3+2*i),(3+2*i,1)]]
elif label=='theta':
 n=8;edges=[edge for i in range(3) for edge in [(0,2+i),(2+i,5+i),(5+i,1)]]
elif label=='k4sub':
 pairs=list(itertools.combinations(range(4),2));n=10;edges=[(i,4+j) for j,pair in enumerate(pairs) for i in pair]
else:
 n=int(label[1:]);edges=[(i,(i+1)%n) for i in range(n)]
adj=[0]*n
for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
pos=sorted({(1<<a)|(1<<b) for a,b in edges});neg=[]
for m in range(1<<n):
 if any(m>>a&1 and m>>b&1 for a,b in edges):continue
 if all((m>>v&1) or (adj[v]&m) for v in range(n)):neg.append(m)
samples=[(m,True) for m in pos]+[(m,False) for m in neg];clauses=[];nv=0
def new():
 global nv;nv+=1;return nv
def inv(x):return not x if isinstance(x,bool) else -x
def clause(*lits):
 out=[]
 for x in lits:
  if isinstance(x,bool):
   if x:return
  elif -x in out:return
  elif x not in out:out.append(x)
 clauses.append(out)
def exactly_one(xs):
 clause(*xs)
 prefix=None
 for x in xs[:-1]:
  cur=new();clause(-x,cur)
  if prefix is not None:clause(-prefix,cur);clause(-x,-prefix)
  prefix=cur
 if prefix is not None:clause(-xs[-1],-prefix)
values=[[new() for _ in samples] for _ in range(budget)];options=[]
for k in range(budget):
 opts=[]
 for a in range(n+k):
  for b in range(a,n+k):
   for op in ([0] if a==b else [0,1]):
    sel=new();opts.append((sel,op,a,b))
    for t,(m,expected) in enumerate(samples):
     va=bool(m>>a&1) if a<n else values[a-n][t];vb=bool(m>>b&1) if b<n else values[b-n][t];out=values[k][t]
     if op==0:clause(-sel,-out,va);clause(-sel,-out,vb);clause(-sel,out,inv(va),inv(vb))
     else:clause(-sel,out,inv(va));clause(-sel,out,inv(vb));clause(-sel,-out,va,vb)
 exactly_one([o[0] for o in opts]);options.append(opts)
# Unused internal gates can always be removed and replaced by a chain of output copies,
# so requiring every gate to be read preserves existence with an upper gate bound.
for k in range(budget-1):clause(*(sel for opts in options[k+1:] for sel,op,a,b in opts if a==n+k or b==n+k))
canonical=len(sys.argv)>4 and sys.argv[4]=='lex'
if canonical:
 for k in range(budget-1):
  for first,op,a,b in options[k]:
   for second,oq,c,d in options[k+1]:
    if d<n+k and (c,d,oq)<(a,b,op):clause(-first,-second)
for t,(m,expected) in enumerate(samples):clause(values[-1][t] if expected else -values[-1][t])
stem='meta3773-motif-'+label+'-'+str(budget)+('-lex' if canonical else '');cnf=job/(stem+'.cnf')
with cnf.open('w') as f:
 f.write('p cnf '+str(nv)+' '+str(len(clauses))+'\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
meta={'canonical_adjacent_independent_gates':canonical,'label':label,'inputs':n,'budget':budget,'edges':edges,'positive_samples':pos,'maximal_negative_samples':neg,'variables':nv,'clauses':len(clauses),'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest()};(job/(stem+'-input.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta|{'positive_samples':len(pos),'maximal_negative_samples':len(neg)}),flush=True)
env={k:v for k,v in os.environ.items() if k in ['PATH','LANG','LC_ALL','TMPDIR']};before=time.monotonic()
with (job/(stem+'-solver.log')).open('w') as log:
 p=subprocess.run([str(job/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'),'-t',str(seconds),str(cnf)],cwd='/workspace/pequalnp-proofs',env=env,stdout=log,stderr=subprocess.STDOUT,timeout=seconds+10)
result={'exit_code':p.returncode,'seconds':time.monotonic()-before,'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest()};assert result['cnf_sha256']==meta['cnf_sha256']
if p.returncode==10:
 true=set()
 for line in (job/(stem+'-solver.log')).read_text().splitlines():
  if line.startswith('v '):true.update(int(v) for v in line[2:].split() if int(v)>0)
 gates=[]
 for opts in options:
  chosen=[(op,a,b) for sel,op,a,b in opts if sel in true];assert len(chosen)==1;gates.append(chosen[0])
 for m in range(1<<n):
  vals=[bool(m>>i&1) for i in range(n)]
  for op,a,b in gates:vals.append((vals[a] or vals[b]) if op else (vals[a] and vals[b]))
  assert vals[-1]==any(bool(m>>a&1) and bool(m>>b&1) for a,b in edges)
 result.update(gates=gates,full_truth_table_verified=True)
(job/(stem+'-result.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
