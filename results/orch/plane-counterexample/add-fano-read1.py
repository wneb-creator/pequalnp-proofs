from pathlib import Path
import json,random
D=json.loads(Path('fano-data.json').read_text());n,s=14,26;rows=sorted(D['minimal_true']+D['maximal_false']);A=len(rows)+n+s+1
base=10*(s+1)*A
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
wf=lambda w,t:base+1+w*3+t
of=lambda side,j,t:base+1+3*(n+s)+(side*s+j)*3+t
cf=lambda j,t:base+1+3*(n+s)+6*s+2*j+t
clauses=[]
def equivalence(out,a,guard=None):
 for c in [[-out,a],[out,-a]]:clauses.append(c if guard is None else [-guard]+c)
def conjunction(out,a,b):clauses.extend([[-out,a],[-out,b],[out,-a,-b]])
def disjunction(out,a,b,guard=None):
 for c in [[out,-a],[out,-b],[-out,a,b]]:clauses.append(c if guard is None else [-guard]+c)
for w in range(n):
 for t in range(3):clauses.append([wf(w,t) if (t==0 and w==0) or (t==1 and w==8) else -wf(w,t)])
for j in range(s):
 for side in range(2):
  for k in range(n+j+1):
   for t in range(3):equivalence(of(side,j,t),wf(k,t),p(side+1,j,k))
 conjunction(cf(j,0),of(0,j,0),of(1,j,1))
 conjunction(cf(j,1),of(0,j,1),of(1,j,0))
 for t in [0,1]:clauses.append([-p(0,j,0),-wf(n+j,t)])
 disjunction(wf(n+j,2),cf(j,0),cf(j,1),p(0,j,0))
 for t in range(3):
  disjunction(wf(n+j,t),of(0,j,t),of(1,j,t),p(0,j,1))
  clauses.append([-p(0,j,2),-wf(n+j,t)])
for k in range(n+s):clauses.append([-p(6,0,k),-wf(k,2)])
original=Path('fano26-onehot.cnf').read_text().splitlines();header=original[0].split();nv=base+3*(n+s)+8*s
original[0]=f'p cnf {nv} {int(header[3])+len(clauses)}'
Path('fano26-read1-cut.cnf').write_text('\n'.join(original)+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
# Distinct representative: move the omitted edge of the one-error seed to(0,8).
seed=json.loads(Path('fano26-seed.json').read_text());missing=next(r for r in seed['errors'] if r in D['minimal_true']);u,v=[i for i in range(n) if missing>>i&1]
actions=json.loads(Path('/workspace/pequalnp-proofs/results/orch/plane-symmetry.json').read_text())['all_168_actions']
action=next(a for a in actions if a['point_permutation'][u]==0 and a['line_permutation'][v-7]==1)
ren={i:action['point_permutation'][i] for i in range(7)}|{i+7:action['line_permutation'][i]+7 for i in range(7)}
pending={n+j:tuple(g) for j,g in enumerate(seed['gates'])};c=[]
while pending:
 ready=[]
 for old,(op,a,b) in pending.items():
  if a in ren and b in ren:
   a,b=sorted((ren[a],ren[b]));ready.append(((a,b,op),old,op,a,b))
 _,old,op,a,b=min(ready);ren[old]=n+len(c);c.append([op,a,b]);del pending[old]
assert ren[seed['output']]==n+s-1
Path('fano26-cut-seed.txt').write_text('errors 47\n'+'\n'.join(f'{n+j} {op} {a} {b}' for j,(op,a,b) in enumerate(c))+'\n')
truth={p(6,0,n+s-1)}
for j,(op,a,b) in enumerate(c):truth.update([p(0,j,op),p(1,j,a),p(2,j,b)])
for ri,r in enumerate(rows):
 w=[bool(r>>i&1) for i in range(n)]
 for j,(op,a,b) in enumerate(c):
  av,bv=w[a],w[b];z=av and bv if op==0 else av or bv;w.append(z)
  for kd,val in [(3,z),(4,av),(5,bv)]:
   if val:truth.add(p(kd,j,ri))
flags=[(w==0,w==8,False) for w in range(n)]
for w,f in enumerate(flags):
 for t,z in enumerate(f):
  if z:truth.add(wf(w,t))
for j,(op,a,b) in enumerate(c):
 af,bf=flags[a],flags[b];cross=(af[0] and bf[1],af[1] and bf[0]);out=(False,False,any(cross)) if op==0 else tuple(x or y for x,y in zip(af,bf))
 for side,vals in enumerate([af,bf]):
  for t,z in enumerate(vals):
   if z:truth.add(of(side,j,t))
 for t,z in enumerate(cross):
  if z:truth.add(cf(j,t))
 for t,z in enumerate(out):
  if z:truth.add(wf(n+j,t))
 flags.append(out)
assert flags[-1][2] is False
failures=[]
with Path('fano26-read1-cut.cnf').open() as f:
 header=f.readline().split()
 for num,line in enumerate(f,1):
  lits=list(map(int,line.split()))[:-1]
  if not any((v in truth) if v>0 else (-v not in truth) for v in lits):failures.append([num,lits])
assert len(failures)==1
# Independently compare three flags against the full joint capped-count recursion.
for case in range(2000):
 flags=[(w==0,w==8,False) for w in range(n)]
 vectors=[{(1,0)} if w==0 else {(0,1)} if w==8 else set() for w in range(n)]
 for j in range(s):
  a,b=random.randrange(n+j),random.randrange(n+j);op=random.randrange(2)
  af,bf=flags[a],flags[b]
  out=(False,False,(af[0] and bf[1]) or (af[1] and bf[0])) if op==0 else tuple(x or y for x,y in zip(af,bf))
  vec={(min(x+z,2),min(y+t,2)) for x,y in vectors[a] for z,t in vectors[b]} if op==0 else vectors[a]|vectors[b]
  assert out==((1,0) in vec,(0,1) in vec,(1,1) in vec)
  flags.append(out);vectors.append(vec)
report={'distinguished_edge':[0,8],'added_variables':nv-base,'added_clauses':len(clauses),'total_variables':nv,'total_clauses':num,'seed_failed_clauses':failures,'random_circuits_checked':2000,'random_gate_flag_checks':2000*s,'padding':'constant pads have false flags and cannot be read by nonpads','status':'prepared only; not launched'}
Path('fano26-read1-cut-validation.json').write_text(json.dumps(report,indent=2));print(report)
