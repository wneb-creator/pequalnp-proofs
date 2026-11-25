import argparse,datetime,json,os,resource,signal,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--data',required=True)
p.add_argument('--rows',required=True)
p.add_argument('--size',type=int,required=True)
p.add_argument('--seconds',type=int,required=True)
p.add_argument('--prefix',required=True)
p.add_argument('--warm-gates',required=True)
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
positive_rows={(1<<p)|(1<<l) for p,l in edges}
assert positive_rows.issubset(rows)
def target(r):return any(bool(r&(1<<u)) and bool(r&(1<<v)) for u,v in edges)
def neg(x):return not x if type(x)is bool else -x

assert n==26
expected_edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
assert len(edges)==52 and set(edges)==expected_edges
neighbors=[sum(1<<l for l in range(13) if (p,13+l) in expected_edges) for p in range(13)]
expected_negatives=set()
for points in range(1<<13):
 lines=(1<<13)-1
 for p in range(13):
  if points&(1<<p):lines&=~neighbors[p]
 closed_points=sum(1<<p for p in range(13) if not (neighbors[p]&lines))
 if points==closed_points:expected_negatives.add(points|(lines<<13))
assert len(expected_negatives)==704
assert len(data['negative_rows'])==704 and set(data['negative_rows'])==expected_negatives
assert len(data['rows'])==756 and set(data['rows'])==positive_rows|expected_negatives
assert len(rows)==756 and set(rows)==positive_rows|expected_negatives
started=time.monotonic();clauses=[];variables=0
preferred={}
one_hot_prefixes=[]
warm=json.loads(Path(a.warm_gates).read_text())
assert isinstance(warm,list) and len(warm)==size
for j,g in enumerate(warm):
 assert isinstance(g,list) and len(g)==3 and all(type(x)is int for x in g)
 op,u,v=g;assert op in(0,1) and 0<=u<n+j and 0<=v<n+j
 u,v=sorted([u,v]);warm[j]=[1 if u==v else op,u,v]
warm_values=[[bool(r&(1<<i)) for r in rows] for i in range(n)]

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
 one_hot_prefixes.append((xs,prefix))
 add(-xs[0],prefix[0])
 for i in range(1,len(xs)-1):
  add(-xs[i],prefix[i])
  add(-prefix[i-1],prefix[i])
  add(-xs[i],-prefix[i-1])
 add(-xs[-1],-prefix[-1])

ops=[];left=[];right=[];values=[]
for j in range(size):
 m=n+j
 op=fresh();aa=[fresh() for _ in range(m)];bb=[fresh() for _ in range(m)]
 exactly_one(aa);exactly_one(bb)
 for i in range(m):
  add(-aa[i],*bb[i:])
  add(-aa[i],-bb[i],op)
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
 wo,wu,wv=warm[j]
 preferred[op]=bool(wo)
 preferred.update({x:i==wu for i,x in enumerate(aa)})
 preferred.update({x:i==wv for i,x in enumerate(bb)})
 result=[]
 for k in range(len(rows)):
  x=warm_values[wu][k];y=warm_values[wv][k];z=(x or y) if wo else (x and y)
  preferred[av[k]]=x;preferred[bv[k]]=y;preferred[out[k]]=z;result.append(z)
 warm_values.append(result)
width=(n+size-1).bit_length()
left_bits=[];right_bits=[]
def code_source(selectors,desired_index):
 bits=[fresh() for _ in range(width)]
 for shift,bit in zip(range(width-1,-1,-1),bits):preferred[bit]=bool((desired_index>>shift)&1)
 for i,selector in enumerate(selectors):
  for shift,bit in zip(range(width-1,-1,-1),bits):add(-selector,bit if (i>>shift)&1 else -bit)
 return bits
for j in range(size):
 left_bits.append(code_source(left[j],warm[j][1]));right_bits.append(code_source(right[j],warm[j][2]))
for j in range(size-1):
 xbits=left_bits[j]+right_bits[j]+[ops[j]]
 ybits=left_bits[j+1]+right_bits[j+1]+[ops[j+1]]
 dependency=[left[j+1][n+j],right[j+1][n+j]]
 equal_prefix=True
 for pos,(x,y) in enumerate(zip(xbits,ybits)):
  add(*dependency,neg(equal_prefix),-x,y)
  if pos+1<len(xbits):
   eq=fresh()
   preferred[eq]=(equal_prefix if type(equal_prefix)is bool else preferred[equal_prefix]) and preferred[x]==preferred[y]
   add(-eq,equal_prefix)
   add(-eq,-x,y);add(-eq,x,-y)
   add(neg(equal_prefix),-x,-y,eq)
   add(neg(equal_prefix),x,y,eq)
   equal_prefix=eq
for j in range(size-1):
 readers=[left[k][n+j] for k in range(j+1,size)]+[right[k][n+j] for k in range(j+1,size)]
 add(*readers)
for i in sorted({v for e in edges for v in e}):
 add(*[left[j][i] for j in range(size)],*[right[j][i] for j in range(size)])
positive_columns=[k for k,r in enumerate(rows) if r in positive_rows]
for gate_values in values:add(*[gate_values[k] for k in positive_columns])
for k,r in enumerate(rows):add(values[-1][k] if target(r) else -values[-1][k])
fixed_count=0
if a.fixed_gates:
 fixed=json.loads(Path(a.fixed_gates).read_text())
 assert len(fixed)==size
 fixed_count=size if a.fixed_prefix is None else a.fixed_prefix
 assert 0<=fixed_count<=size
 for j,g in enumerate(fixed):
  assert isinstance(g,list) and len(g)==3 and all(type(x)is int for x in g)
  op,u,v=g;assert op in(0,1) and 0<=u<n+j and 0<=v<n+j
  u,v=sorted([u,v])
  if u==v:op=1
  if j<fixed_count:add(ops[j] if op else -ops[j]);add(left[j][u]);add(right[j][v])
else:assert a.fixed_prefix is None
negative_rows=set(data['negative_rows'])
assert negative_rows and negative_rows.issubset(set(rows))
assert all(not target(r) for r in negative_rows)
negative_columns=[k for k,r in enumerate(rows) if r in negative_rows]
clean=[]
for j in range(size):
 flag=fresh();clean.append(flag)
 preferred[flag]=not any(warm_values[n+j][k] for k in negative_columns)
 for k in negative_columns:add(-flag,-values[j][k])
 add(flag,*[values[j][k] for k in negative_columns])
def guarded_at_most_one(xs,condition):
 if len(xs)<=1:return
 prefix=[fresh() for _ in xs[:-1]]
 for i,x in enumerate(prefix):preferred[x]=any(preferred[y] for y in xs[:i+1])
 add(-condition,-xs[0],prefix[0])
 for i in range(1,len(xs)-1):
  add(-condition,-xs[i],prefix[i])
  add(-condition,-prefix[i-1],prefix[i])
  add(-condition,-xs[i],-prefix[i-1])
 add(-condition,-xs[-1],-prefix[-1])
for j in range(size):
 readers=[]
 for k in range(j+1,size):
  aa=left[k][n+j];bb=right[k][n+j]
  reader=fresh();readers.append(reader)
  preferred[reader]=(warm[k][1]==n+j or warm[k][2]==n+j)
  add(-reader,aa,bb);add(-aa,reader);add(-bb,reader)
  for selector in (aa,bb):
   add(-clean[j],-selector,ops[k])
   add(-clean[j],-selector,-ops[k],clean[k])
 guarded_at_most_one(readers,clean[j])
previous=[True]+[False]*10
and_count=0
for j in range(size):
 and_count+=int(warm[j][0]==0)
 current=[True]
 for k in range(1,11):
  z=fresh();preferred[z]=and_count>=k;current.append(z)
  aa=previous[k];bb=-ops[j];cc=previous[k-1]
  add(neg(aa),z);add(neg(bb),neg(cc),z)
  add(-z,aa,bb);add(-z,aa,cc)
 previous=current
add(previous[10])
for xs,prefix in one_hot_prefixes:
 for i,x in enumerate(prefix):preferred[x]=any(preferred[y] for y in xs[:i+1])
assert set(preferred)==set(range(1,variables+1))
flipped={x for x,v in preferred.items() if v}
def rename(x):return -x if abs(x) in flipped else x
cnf=base.with_suffix('.cnf')
with cnf.open('w') as f:
 f.write(f'p cnf {variables} {len(clauses)}\n')
 for clause in clauses:f.write(' '.join(str(rename(x)) for x in clause)+' 0\n')
mapping={'n':n,'size':size,'rows':rows,'ops':ops,'left':left,'right':right,'outputs':values[-1],'flipped_variables':sorted(flipped),'warm_gates':warm}
base.with_suffix('.mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'n':n,'size':size,'sampled_rows':len(rows),'variables':variables,'clauses':len(clauses),'conversion_seconds':time.monotonic()-started,'seconds_limit':a.seconds,'fixed_prefix':fixed_count,'warm_true_variables':len(flipped),'complete_negative_rows':len(negative_rows),'minimum_and_gates':10,'encoder':'full-boundary polarity-warm AO2 with lex, clean-gate normalizations and AND>=10'}
print(json.dumps(record),flush=True)
if a.emit_only:
 record['status']='CNF emitted; solver not run';base.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n');raise SystemExit(0)
exe='/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical'
termination_signal=None
with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:
 proc=subprocess.Popen([exe,'--phase=false','-t',str(a.seconds),'-w',str(base.with_suffix('.sol')),str(cnf)],stdout=out,stderr=err,start_new_session=True)
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
 assert all(any(assignment[abs(rename(x))]==(rename(x)>0) for x in clause) for clause in clauses)
 assignment={x:(not v if x in flipped else v) for x,v in assignment.items()}
 assert all(any(assignment[abs(x)]==(x>0) for x in clause) for clause in clauses)
 gates=[]
 for j in range(size):
  aa=[i for i,x in enumerate(left[j]) if assignment[x]];bb=[i for i,x in enumerate(right[j]) if assignment[x]]
  assert len(aa)==len(bb)==1
  gates.append([int(assignment[ops[j]]),aa[0],bb[0]])
  assert aa[0]<=bb[0] and (aa[0]!=bb[0] or assignment[ops[j]])
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
