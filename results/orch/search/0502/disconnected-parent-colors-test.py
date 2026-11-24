from pathlib import Path
import importlib.util,json,random
B=Path('/tmp/oec/pequalnp-pilot-21/search')
def load(name,file):
 s=importlib.util.spec_from_file_location(name,B/file);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
m=load('colors_test','disconnected_parent_colors.py');f=load('colors_base','cegis.py')
c=f.CNF();aa=[];bb=[]
for j in range(14):aa.append([c.var() for _ in range(15+j)]);bb.append([c.var() for _ in range(15+j)])
before=c.n;parents,edges=m.disconnected_parents(c,aa,bb)
assert c.n-before==29 and len(c.cs)==482
rng=random.Random(1024);graphs=[]
for _ in range(200):
 used=[rng.randrange(24)];g=[]
 for j in range(5):
  a=rng.choice(used);b=rng.randrange(24);g.append((a,b));used.append(b)
 graphs.append(g)
for _ in range(200):graphs.append([(rng.randrange(12),rng.randrange(12)) for _ in range(3)]+[(rng.randrange(12,24),rng.randrange(12,24)) for _ in range(2)])
for _ in range(100):graphs.append([(rng.randrange(24),rng.randrange(24)) for _ in range(5)])
def up(values):
 values=dict(values)
 while True:
  changed=False
  for clause in c.cs:
   if any(abs(x) in values and values[abs(x)]==(x>0) for x in clause):continue
   remaining=[x for x in clause if abs(x) not in values]
   if not remaining:return True,values
   if len(remaining)==1:values[abs(remaining[0])]=remaining[0]>0;changed=True
  if not changed:return False,values
counts={'connected_rejected':0,'disconnected_models':0}
for graph in graphs:
 representatives=list(range(24))
 def find(x):
  while representatives[x]!=x:x=representatives[x]
  return x
 for a,b in graph:representatives[find(a)]=find(b)
 component=find(graph[0][0]);connected=all(find(a)==component for a,b in graph)
 values={}
 for j,(a,b) in enumerate(graph):
  for selectors,chosen in ((aa[9+j],a),(bb[9+j],b)):
   values.update({variable:k==chosen for k,variable in enumerate(selectors)})
 conflict,_=up(values)
 if connected:
  assert conflict;counts['connected_rejected']+=1
 else:
  assert not conflict
  values.update({variable:find(p)!=component for p,variable in enumerate(parents)})
  values.update({variable:find(graph[j][0])!=component for j,variable in enumerate(edges)})
  assert all(any(values[abs(x)]==(x>0) for x in clause) for clause in c.cs)
  counts['disconnected_models']+=1
runner=load('colors_driver','cegis-general-five-cost-disconnected.py')
class Count(f.CNF):
 def __init__(self):self.n=0;self.count=0;self.bytes=0
 def add(self,*xs):self.count+=1;self.bytes+=len((' '.join(map(str,xs))+' 0\n').encode())
cc=Count();runner.encode(cc,runner.f.ROWS)
assert cc.n==129594 and cc.count==2680563
report={'graphs':len(graphs),'guard_variables':29,'guard_clauses':482,**counts,'full_variables':cc.n,'full_clauses':cc.count,'exact_DIMACS_bytes':cc.bytes+len(f'p cnf {cc.n} {cc.count}\n'.encode()),'solver_launched':False}
(B/'disconnected-parent-colors-test.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
