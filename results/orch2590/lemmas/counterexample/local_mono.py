from pathlib import Path
from itertools import combinations
import subprocess, json, time, sys

DIR=Path('/tmp/oec/pequalnp-pilot-110/counterexample2590/local')
DIR.mkdir(exist_ok=True)
SOLVER='/tmp/oec/pequalnp-pilot-110/sat_strategy/cadical/build/cadical'
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
BASE=[('or',7,1),('or',1,4),('or',8,0),('or',7,12),('and',5,13),('or',9,0),('or',4,2),('and',11,15),('or',1,9),('or',18,8),('and',6,19),('or',9,2),('and',10,21),('or',8,16),('and',3,23),('or',14,24),('or',25,22),('or',26,17),('or',27,20)]
OPS=['and','or']

def neg(x): return not x if type(x) is bool else -x
class CNF:
 def __init__(self): self.count=0; self.clauses=[]
 def var(self): self.count+=1; return self.count
 def add(self,*xs):
  if any(x is True for x in xs): return
  xs=set(x for x in xs if x is not False)
  if any(-x in xs for x in xs): return
  self.clauses.append(tuple(sorted(xs,key=lambda x:(abs(x),x))))
 def exactly_one(self,xs):
  self.add(*xs)
  for a,b in combinations(xs,2):self.add(-a,-b)
 def gate(self,z,op,a,b,guard=False):
  if op=='and':
   self.add(guard,-z,a);self.add(guard,-z,b);self.add(guard,z,neg(a),neg(b))
  elif op=='or':
   self.add(guard,z,neg(a));self.add(guard,z,neg(b));self.add(guard,-z,a,b)
  elif op=='not':
   self.add(guard,-z,neg(a));self.add(guard,z,a)
  else:self.add(guard,z)
 def write(self,path):
  with path.open('w') as f:
   f.write(f'p cnf {self.count} {len(self.clauses)}\n')
   for c in self.clauses:f.write(' '.join(map(str,c))+' 0\n')

def target(row): return any((row>>a&1) and (row>>b&1) for a,b in EDGES)
def evaluate(circuit,row):
 wires=[bool(row>>i&1) for i in range(10)]
 for op,a,b in circuit:
  a=wires[a] if a<len(wires) else False
  b=wires[b] if b<len(wires) else False
  wires.append(a and b if op=='and' else a or b if op=='or' else not a if op=='not' else True)
 return wires[-1]

def encoding(window,rows,require_not=False,base=BASE):
 cnf=CNF(); selects={}
 for j in window:
  sources=list(range(10+j))+[1000]
  ops=[cnf.var() for _ in OPS]; a=[cnf.var() for _ in sources];b=[cnf.var() for _ in sources]
  cnf.exactly_one(ops);cnf.exactly_one(a);cnf.exactly_one(b)
  selects[j]=(sources,ops,a,b)
  for ia,sa in enumerate(a):
   for ib,sb in enumerate(b):
    if ia>ib:
     cnf.add(-ops[0],-sa,-sb);cnf.add(-ops[1],-sa,-sb)
 if require_not:cnf.add(*(s[1][2] for s in selects.values()))
 for row in rows:
  wires=[bool(row>>i&1) for i in range(10)]
  for j,(op,a,b) in enumerate(base):
   z=cnf.var()
   if j in selects:
    sources,ops,ass,bss=selects[j]
    va,vb=cnf.var(),cnf.var()
    for ss,v in ((ass,va),(bss,vb)):
     for source,s in zip(sources,ss):
      value=wires[source] if source<len(wires) else False
      cnf.add(-s,-v,value);cnf.add(-s,v,neg(value))
    for opname,o in zip(OPS,ops):cnf.gate(z,opname,va,vb,-o)
   else:cnf.gate(z,op,wires[a],wires[b])
   wires.append(z)
  cnf.add(wires[-1] if target(row) else -wires[-1])
 return cnf,selects

def initial_rows():
 indep=[r for r in range(1024) if not target(r)]
 maximal=[r for r in indep if all(target(r|(1<<i)) for i in range(10) if not(r>>i&1))]
 return sorted(set([(1<<a)|(1<<b) for a,b in EDGES]+maximal))

def solve_window(window,limit=15):
 rows=initial_rows();name='w'+('-'.join(str(j+10) for j in window));start=time.monotonic()
 for iteration in range(30):
  cnf,selectors=encoding(window,rows)
  stem=DIR/(name+'-'+str(iteration));cnf.write(stem.with_suffix('.cnf'))
  with stem.with_suffix('.log').open('w') as output:
   process=subprocess.run([SOLVER,'-t',str(limit),str(stem.with_suffix('.cnf'))],stdout=output,stderr=subprocess.STDOUT)
  text=stem.with_suffix('.log').read_text()
  if process.returncode!=10:
   result={'window':[j+10 for j in window],'iterations':iteration+1,'rows':len(rows),'status':'UNSAT' if process.returncode==20 else 'UNKNOWN','seconds':time.monotonic()-start,'returncode':process.returncode}
   print(json.dumps(result),flush=True);return result
  literals={int(x) for l in text.splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x)>0}
  candidate=BASE[:]
  for j,(sources,ops,ass,bss) in selectors.items():
   op=next(op for op,v in zip(OPS,ops) if v in literals)
   a=next(a for a,v in zip(sources,ass) if v in literals)
   b=next(b for b,v in zip(sources,bss) if v in literals)
   candidate[j]=(op,a,b)
  errors=[r for r in range(1024) if evaluate(candidate,r)!=target(r)]
  if not errors:
   result={'window':[j+10 for j in window],'iterations':iteration+1,'rows':len(rows),'status':'SAT_FULL_1024','seconds':time.monotonic()-start,'circuit':candidate}
   (DIR/'COUNTEREXAMPLE.json').write_text(json.dumps(result,indent=2))
   print(json.dumps(result),flush=True);return result
  if any(r in rows for r in errors):raise RuntimeError('CNF model violates enforced row')
  print(json.dumps({'window':[j+10 for j in window],'iteration':iteration,'rows':len(rows),'errors':len(errors),'add':errors[:12]}),flush=True)
  rows=sorted(set(rows+errors[:64]))
 return {'window':[j+10 for j in window],'status':'ITERATION_LIMIT'}

if __name__=='__main__':
 # Gate numbers are externally wire indices; internals use zero-based gate indices.
 windows=[(17,22),(11,15,17),(10,21,22),(15,17,22),(10,17,22),(11,17,22),(17,21,22),(17,22,27),(17,22,26),(17,22,28),
  (11,15,17,22),(10,17,21,22),(10,11,17,22),(15,17,21,22),(17,18,20,22),(17,19,20,22),(14,17,22,24),(17,22,26,27),
  (10,11,15,17),(10,11,21,22),(11,15,21,22),(10,15,17,22)]
 if len(sys.argv)>1:windows=[tuple(int(x) for x in s.split(',')) for s in sys.argv[1:]]
 for window in windows:
  result=solve_window(tuple(j-10 for j in window),60)
  if result['status']=='SAT_FULL_1024':break
