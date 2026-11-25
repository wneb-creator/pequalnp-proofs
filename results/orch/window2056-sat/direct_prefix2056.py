import argparse,datetime,json,os,resource,signal,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--data',required=True)
p.add_argument('--rows',required=True)
p.add_argument('--size',type=int,required=True)
p.add_argument('--seconds',type=int,required=True)
p.add_argument('--prefix',required=True)
p.add_argument('--fixed-gates')
p.add_argument('--fixed-prefix',type=int)
p.add_argument('--emit-only',action='store_true')
a=p.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
base=Path(a.prefix);base.parent.mkdir(exist_ok=True)
data=json.loads(Path(a.data).read_text());rows=json.loads(Path(a.rows).read_text())
n=data['n'];size=a.size
assert type(n)is int and n>0 and size>0 and len(rows)==len(set(rows))
assert all(type(r)is int and 0<=r<1<<n for r in rows)
edges=[tuple(e) for e in data['edges']]
assert all(len(e)==2 and all(type(v)is int and 0<=v<n for v in e) for e in edges)
def target(r):return any(bool(r&(1<<u)) and bool(r&(1<<v)) for u,v in edges)
def neg(x):return not x if type(x)is bool else -x

started=time.monotonic();clauses=[];variables=0

def fresh():
 global variables
 variables+=1
 return variables

def add(*literals):
 if any(x is True for x in literals):return
 clause=[x for x in literals if x is not False]
 assert all(type(x)is int and x!=0 for x in clause)
 clauses.append(clause)

def exactly_one(xs):
 assert xs
 add(*xs)
 if len(xs)==1:return
 prefix=[fresh() for _ in xs[:-1]]
 add(-xs[0],prefix[0])
 for i in range(1,len(xs)-1):
  add(-xs[i],prefix[i])
  add(-prefix[i-1],prefix[i])
  add(-xs[i],-prefix[i-1])
 add(-xs[-1],-prefix[-1])

fixed=[];fixed_count=0
if a.fixed_gates:
 fixed=json.loads(Path(a.fixed_gates).read_text())
 assert len(fixed)==size
 fixed_count=size if a.fixed_prefix is None else a.fixed_prefix
 assert 0<=fixed_count<=size
 for j,g in enumerate(fixed):
  assert isinstance(g,list) and len(g)==3 and all(type(x)is int for x in g)
  op,u,v=g;assert op in(0,1) and 0<=u<n+j and 0<=v<n+j
else:assert a.fixed_prefix is None
ops=[];left=[];right=[];values=[]
for j in range(size):
 m=n+j
 if j<fixed_count:
  op,u,v=fixed[j]
  out=[]
  for k,r in enumerate(rows):
   x=bool(r&(1<<u)) if u<n else values[u-n][k]
   y=bool(r&(1<<v)) if v<n else values[v-n][k]
   assert type(x)is bool and type(y)is bool
   out.append(x or y if op else x and y)
  ops.append(None);left.append(None);right.append(None);values.append(out)
  continue
 op=fresh();aa=[fresh() for _ in range(m)];bb=[fresh() for _ in range(m)]
 exactly_one(aa);exactly_one(bb)
 out=[fresh() for _ in rows];av=[fresh() for _ in rows];bv=[fresh() for _ in rows]
 for k,r in enumerate(rows):
  for i in range(m):
   source=bool(r&(1<<i)) if i<n else values[i-n][k]
   add(-aa[i],-av[k],source);add(-aa[i],av[k],neg(source))
   add(-bb[i],-bv[k],source);add(-bb[i],bv[k],neg(source))
  o,x,y,z=op,av[k],bv[k],out[k]
  add(o,-z,x);add(o,-z,y);add(o,z,-x,-y)
  add(-o,z,-x);add(-o,z,-y);add(-o,-z,x,y)
 ops.append(op);left.append(aa);right.append(bb);values.append(out)
for k,r in enumerate(rows):add(values[-1][k] if target(r) else neg(values[-1][k]))
cnf=base.with_suffix('.cnf')
with cnf.open('w') as f:
 f.write(f'p cnf {variables} {len(clauses)}\n')
 for clause in clauses:f.write(' '.join(map(str,clause))+' 0\n')
mapping={'n':n,'size':size,'rows':rows,'ops':ops,'left':left,'right':right,'outputs':values[-1],'fixed_gates':fixed[:fixed_count],'fixed_prefix':fixed_count}
base.with_suffix('.mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'n':n,'size':size,'sampled_rows':len(rows),'variables':variables,'clauses':len(clauses),'conversion_seconds':time.monotonic()-started,'seconds_limit':a.seconds,'fixed_prefix':fixed_count,'encoder':'direct one-hot binary AND/OR with constant-folded fixed prefix'}
print(json.dumps(record),flush=True)
if a.emit_only:
 record['status']='CNF emitted; solver not run';base.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n');raise SystemExit(0)
exe='/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical'
termination_signal=None
with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:
 proc=subprocess.Popen([exe,'-t',str(a.seconds),'-w',str(base.with_suffix('.sol')),str(cnf)],stdout=out,stderr=err,start_new_session=True)
 base.with_suffix('.process.json').write_text(json.dumps({'wrapper_pid':os.getpid(),'solver_pid':proc.pid,'prefix':str(base)},indent=2)+'\n')
 def terminate(sig,frame):
  global termination_signal
  termination_signal=sig
  if proc.returncode is not None:raise SystemExit(128+sig)
  try:os.killpg(proc.pid,sig)
  except ProcessLookupError:pass
 signal.signal(signal.SIGTERM,terminate)
 proc.wait()
record['exit_code']=proc.returncode
if termination_signal is not None:
 record['status']='interrupted';record['termination_signal']=termination_signal
elif proc.returncode==10:
 assignment={}
 for line in base.with_suffix('.sol').read_text().splitlines():
  if line.startswith('v '):
   for value in map(int,line[2:].split()):
    if value:assignment[abs(value)]=value>0
 assert set(assignment)==set(range(1,variables+1))
 assert all(any(assignment[abs(x)]==(x>0) for x in clause) for clause in clauses)
 gates=[]
 for j in range(size):
  if j<fixed_count:
   gates.append(fixed[j]);continue
  aa=[i for i,x in enumerate(left[j]) if assignment[x]];bb=[i for i,x in enumerate(right[j]) if assignment[x]]
  assert len(aa)==len(bb)==1
  gates.append([int(assignment[ops[j]]),aa[0],bb[0]])
 def evaluate(r):
  vs=[bool(r&(1<<i)) for i in range(n)]
  for op,u,v in gates:vs.append(vs[u] or vs[v] if op else vs[u] and vs[v])
  return vs[-1]
 assert all(evaluate(r)==target(r) for r in rows)
 violations=[r for r in data['rows'] if evaluate(r)!=target(r)]
 record.update({'status':'SAT; full boundary passed; Lean verification required' if not violations else 'SAT; sampled rows passed; full boundary incomplete','gates':gates,'cnf_clauses_verified':len(clauses),'full_boundary_mismatches':violations,'full_boundary_rows':len(data['rows'])})
 if n<=20:
  exhaustive=[r for r in range(1<<n) if evaluate(r)!=target(r)]
  record.update({'exhaustive_assignments':1<<n,'exhaustive_mismatches':len(exhaustive)})
  if exhaustive:record['status']='SAT; invalid exhaustive candidate'
elif proc.returncode==20:record['status']='UNSAT; external solver only, not Lean checked'
elif proc.returncode==0:record['status']='UNKNOWN; time or resource limit'
else:record['status']='solver error'
record['elapsed_seconds']=time.monotonic()-started
record['max_rss_kb']=max(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
base.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['gates','full_boundary_mismatches']}),flush=True)
if termination_signal is not None:raise SystemExit(128+termination_signal)
