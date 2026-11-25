from pathlib import Path
import json,hashlib,itertools,collections,re,ast
base=Path('/workspace/pequalnp-proofs/results/orch/finite')
files={p.name:p for p in base.iterdir() if p.is_file()}
def read(name):
 assert name in files,name
 return files[name].read_text()
def sha(name):return hashlib.sha256(files[name].read_bytes()).hexdigest()
manifest=json.loads(read('sha256.json'))
assert isinstance(manifest,dict) and len(manifest)==381
assert set(manifest)==set(files)-{'sha256.json'}
for name,digest in manifest.items():assert sha(name)==digest,name
assert sha('sha256.json')=='c3a1a298431640f23830688902e3e2e09d3785f10a9eccca75015746631d9d64'
print('PASS archive: exact381-file coverage, all hashes, manifest hash')
report=json.loads(read('conjecture-run-outcomes.json'))
assert isinstance(report,dict) and isinstance(report['cases'],list)
cases=[r for r in report['cases'] if r.get('kind')=='oracle']
assert len(cases)==24
counts=collections.Counter(r['status'] for r in cases)
assert counts=={'UNSAT':21,'UNKNOWN_TIME_LIMIT':3}
assert report['oracle_counts']=={'SAT':0,**counts}
sourcehash=sha('synth_sat_packing_oracle.py')
assert sourcehash=='d750dd818860db0e27763b806e3ec6db2ca93b52dd4e2a1ee8a64810924e6c19'
print('PASS oracle census:',dict(counts),'sourceSHA',sourcehash)

def supports_by_distance(n,edges):
 adj=[set() for _ in range(n)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 forbidden={(a,b) for a in range(n) for b in range(a+1,n) if b in adj[a] or adj[a]&adj[b]}
 result=[1<<i for i in range(n)]
 for s in range(1<<n):
  vertices=[i for i in range(n) if s&(1<<i)]
  if len(vertices)>=2 and all((a,b) not in forbidden for a,b in itertools.combinations(vertices,2)):result.append(s)
 return result

# Independent check of the six guarded gate clauses.
for op,z,a,b in itertools.product([False,True],repeat=4):
 clauses=[[op,not z,a],[op,not z,b],[op,z,not a,not b],
          [not op,z,not a],[not op,z,not b],[not op,not z,a,b]]
 assert all(any(c) for c in clauses)==(z==((a or b) if op else (a and b)))

for row in cases:
 pre=row['prefix'];meta=json.loads(read(pre+'.json'));n=row['n'];edges=[tuple(e) for e in row['edges']];K=row['K']
 graph=list(map(int,read(row['graph']).split()));assert graph[:2]==[n,len(edges)]
 assert list(zip(graph[2::2],graph[3::2]))==edges
 assert len(set(frozenset(e) for e in edges))==len(edges)
 assert all(0<=a<n and 0<=b<n and a!=b for a,b in edges)
 support=supports_by_distance(n,edges);B=len(support)
 assert meta['free_supports']==support and meta['free_wire_count']==B
 assert row['nontrivial_free_or_count']==B-n
 # Generate maximal independent assignments using strict subset maximality.
 independent=[s for s in range(1<<n) if all(not(s&(1<<a) and s&(1<<b)) for a,b in edges)]
 maximal=[s for s in independent if all(s==t or s&t!=s for t in independent)]
 points=[(1<<a)+(1<<b) for a,b in edges]+maximal;R=len(points)
 assert points==meta['rows']==row['rows']
 expectednames=[]
 expectednames += [('op',j) for j in range(K)]
 for kind in ['val','aval','bval']:expectednames += [(kind,j,t) for j in range(K) for t in range(R)]
 for kind in ['asel','bsel']:expectednames += [(kind,j,i) for j in range(K) for i in range(B+j)]
 assert [tuple(v) for v in meta['variables']]==expectednames
 names={v:i+1 for i,v in enumerate(expectednames)}
 def v(*name):return names[name]
 clauses=[]
 def clause(*lits):clauses.append(tuple(sorted(lits)))
 for j in range(K):
  for side in ['asel','bsel']:
   one=[v(side,j,i) for i in range(B+j)];clause(*one)
   for a,b in itertools.combinations(one,2):clause(-a,-b)
  for a in range(B+j):
   for b in range(a+1):clause(-v('asel',j,a),-v('bsel',j,b))
  for side,valkind in [('asel','aval'),('bsel','bval')]:
   for i in range(B+j):
    selector=v(side,j,i)
    for t,assignment in enumerate(points):
     wire=v(valkind,j,t)
     if i<B:clause(-selector,wire if assignment & support[i] else -wire)
     else:
      source=v('val',i-B,t);clause(-selector,-wire,source);clause(-selector,wire,-source)
  for t in range(R):
   o=v('op',j);z=v('val',j,t);a=v('aval',j,t);b=v('bval',j,t)
   clause(o,-z,a);clause(o,-z,b);clause(o,z,-a,-b)
   clause(-o,z,-a);clause(-o,z,-b);clause(-o,-z,a,b)
 for t in range(R):clause(v('val',K-1,t) if t<len(edges) else -v('val',K-1,t))
 assert row['ordered']==meta['ordered']==True
 for j in range(K-1):
  for a in range(B+j):
   for b in range(a):clause(-v('bsel',j,a),-v('bsel',j+1,b))
 raw=read(pre+'.cnf').splitlines();header=raw[0].split();assert header==['p','cnf',str(len(names)),str(len(clauses))]
 actual=[]
 for line in raw[1:]:
  ints=list(map(int,line.split()));assert ints[-1]==0 and all(1<=abs(x)<=len(names) for x in ints[:-1]);actual.append(tuple(sorted(ints[:-1])))
 assert collections.Counter(actual)==collections.Counter(clauses),pre
 assert meta['clauses']==len(clauses)
 digest=sha(pre+'.cnf');assert digest==row['cnf_sha256']==meta['cnf_sha256']
 assert row['source']=='synth_sat_packing_oracle.py' and row['source_sha256']==sourcehash
 assert meta['ops']==[v('op',j) for j in range(K)]
 assert meta['asel']==[[v('asel',j,i) for i in range(B+j)] for j in range(K)]
 assert meta['bsel']==[[v('bsel',j,i) for i in range(B+j)] for j in range(K)]
 wrapper=read(pre+'.log');solver=read(pre+'.solver.log')
 lines=solver.splitlines();status=[line for line in lines if line.startswith('s ')]
 assert status==row['solver_status']
 result=re.search(r'^RESULT (\d+) SECONDS ([0-9.]+)$',wrapper,re.M);assert result
 assert int(result[1])==row['exit'] and float(result[2])==row['wrapper_seconds']
 stat=re.search(r'^STATUS (.+)$',wrapper,re.M);assert stat and ast.literal_eval(stat[1])==status
 assert f"setting time limit to {row['native_limit_seconds']} seconds" in solver
 if row['status']=='UNSAT':assert row['exit']==20 and status==['s UNSATISFIABLE']
 else:
  assert row['status']=='UNKNOWN_TIME_LIMIT' and row['exit']==0 and not status and 'c UNKNOWN' in lines
  assert row['wrapper_seconds']>=row['native_limit_seconds']
 print('PASS',pre,row['status'],'n',n,'K',K,'free',B,'clauses',len(clauses))

# Independent matching witness truth and minimum-paid-cost enumeration.
witness=json.loads(read('packing-matching2-witness.log'));edges=[(0,1),(2,3)];n=4
supports=witness['free_supports'];assert set(supports)==set(supports_by_distance(n,edges))
gates=witness['paid_gates'];assert len(gates)==3
source=[];and_ancestors=[]
for j,(op,a,b) in enumerate(gates):
 assert 0<=a<b<len(supports)+j and op in [0,1]
 ancestors=set()
 for wire in (a,b):
  if wire>=len(supports):
   k=wire-len(supports);ancestors.update(and_ancestors[k])
   if gates[k][0]==0:ancestors.add(k)
 and_ancestors.append(ancestors)
 if op==0 and not ancestors:source.append(j)
truth=[];dirty=[[] for _ in gates]
for point in range(16):
 values=[bool(point&s) for s in supports]
 for op,a,b in gates:values.append((values[a] or values[b]) if op else (values[a] and values[b]))
 goal=bool((point&3)==3 or (point&12)==12);assert values[-1]==goal
 truth.append([point,int(goal),int(values[-1])])
 if not goal:
  for j in range(3):
   if values[len(supports)+j]:dirty[j].append(point)
assert truth==witness['truth_table'] and dirty==witness['dirty_inputs_per_and']
assert source==witness['source_ands']==[0,1] and all(dirty[j] for j in source) and dirty[2]==[]
assert witness['paid_gate_count']==3
ordinary=3+sum(s.bit_count()-1 for s in supports if s.bit_count()>1)
assert ordinary==witness['ordinary_gate_count']==7
bank=[sum((1<<x) for x in range(16) if x&s) for s in supports]
target=sum((1<<x) for x in range(16) if (x&3)==3 or (x&12)==12)
assert target not in bank
first=[]
for a,b in itertools.combinations(range(len(bank)),2):
 for op in ['AND','OR']:
  value=(bank[a]&bank[b]) if op=='AND' else (bank[a]|bank[b]);assert value!=target;first.append(value)
count=0
for f in first:
 ext=bank+[f]
 for a,b in itertools.combinations(range(len(ext)),2):
  for op in ['AND','OR']:
   value=(ext[a]&ext[b]) if op=='AND' else (ext[a]|ext[b]);assert value!=target;count+=1
assert len(first)==56 and count==4032
print('PASS matching2: full16rows; bothsourceANDs dirty; 3paid/7ordinary; exhaustive56 one-gate and4032 two-gate circuits fail')
print('REVIEW PASS: finite solver evidence only. UNKNOWN is not a lower bound; oracle gates have different cost from ordinary circuits. No full-gap refutation.')
