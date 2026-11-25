from pathlib import Path
import itertools,json,resource,subprocess,time,os,sys,hashlib
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
job=Path('/tmp/oec/pequalnp-pilot-79');label='arc-full';budget=18;seconds=int(sys.argv[1]);assert 0<seconds<=180
source_data=job/'meta3773-full-patch-data.json';data=json.loads(source_data.read_text());raw_n=data['raw_inputs'];n=data['inputs_with_free_or_signals'];edges=data['edges'];free_gates=data['default_free_ors'];assert raw_n==14 and n==29 and len(free_gates)==15
pos=data['positive_raw_masks'];neg=data['maximal_negative_raw_masks']
def augment(m):
 for i,g in enumerate(free_gates):
  assert g['wire']==raw_n+i and g['op']=='or'
  a,b=g['inputs'];assert a<g['wire'] and b<g['wire']
  if m>>a&1 or m>>b&1:m|=1<<g['wire']
 return m
samples=[(augment(m),True) for m in pos]+[(augment(m),False) for m in neg]
clauses=[];nv=0
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
canonical=True
# Each physical input must occur as a literal leaf; outside stars intersect each target star once.
for i in range(raw_n):
 clause(*(sel for opts in options for sel,op,a,b in opts if a==i or b==i))
# Greedy topological order gives nondecreasing maximum fanin index.
maxima=[]
for k,opts in enumerate(options):
 ms=[]
 for b in range(n+k):
  v=new();ss=[sel for sel,op,a,d in opts if d==b]
  clause(-v,*ss)
  for sel in ss:clause(-sel,v)
  ms.append(v)
 maxima.append(ms)
for k in range(budget-1):
 for b,v in enumerate(maxima[k]):
  for d in range(b):clause(-v,-maxima[k+1][d])
# Fourteen mandatory raw leaves leave room for at most five helper leaves.
used=[]
for i in range(raw_n,n):
 u=new();ss=[sel for opts in options for sel,op,a,b in opts if a==i or b==i]
 clause(-u,*ss)
 for sel in ss:clause(-sel,u)
 used.append(u)
clause(*used)
for six in itertools.combinations(used,6):clause(*[-u for u in six])
# Gates zero on every positive input can be eliminated; a valid sub-64 circuit needs a bad AND.
bad=[]
for k,opts in enumerate(options):
 clause(*(values[k][t] for t,(m,e) in enumerate(samples) if e))
 b=new();bad.append(b)
 for sel,op,a,c in opts:
  if op:clause(-b,-sel)
 clause(-b,*(values[k][t] for t,(m,e) in enumerate(samples) if not e))
clause(*bad)
for t,(m,expected) in enumerate(samples):clause(values[-1][t] if expected else -values[-1][t])
stem='meta3773-motif-'+label+'-'+str(budget)+'-colex-raw-helper5-badand';cnf=job/(stem+'.cnf')
with cnf.open('w') as f:
 f.write('p cnf '+str(nv)+' '+str(len(clauses))+'\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
meta={'nondecreasing_max_fanin':canonical,'mandatory_raw':True,'at_most_five_free_leaves':True,'unproductive_and_required':True,'label':label,'inputs':n,'raw_inputs':raw_n,'free_or_gates':free_gates,'data_sha256':hashlib.sha256(source_data.read_bytes()).hexdigest(),'budget':budget,'edges':edges,'positive_samples':pos,'maximal_negative_samples':neg,'variables':nv,'clauses':len(clauses),'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest()};(job/(stem+'-input.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta|{'positive_samples':len(pos),'maximal_negative_samples':len(neg)}),flush=True)
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
 for raw in range(1<<raw_n):
  m=augment(raw)
  vals=[bool(m>>i&1) for i in range(n)]
  for op,a,b in gates:vals.append((vals[a] or vals[b]) if op else (vals[a] and vals[b]))
  assert vals[-1]==any(bool(m>>a&1) and bool(m>>b&1) for a,b in edges)
 result.update(gates=gates,full_truth_table_verified=True)
(job/(stem+'-result.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
