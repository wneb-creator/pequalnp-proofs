import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('metadata');p.add_argument('solution');p.add_argument('output');a=p.parse_args()
d=json.loads(Path(a.metadata).read_text());text=Path(a.solution).read_text();assert 's SATISFIABLE' in text,text
positive=set()
for line in text.splitlines():
 if line.startswith('v '):positive.update(int(x) for x in line[2:].split() if int(x)>0)
def pick(vs):
 choices=[i for i,v in enumerate(vs) if v in positive];assert len(choices)==1,choices;return choices[0]
gates=([(2,d['not_input'],0)] if d['fixed_not'] else [])+[(int(o in positive),pick(x),pick(y)) for o,x,y in zip(d['ops'],d['a'],d['b'])]
if d.get('final_or_edge',False):gates.append((1,10,10+len(gates)))
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
errors=[]
for x in range(1024):
 w=[bool(x>>j&1) for j in range(10)];target=any(w[u] and w[v] for u,v in edges)
 w.append(w[0] and w[1] if d['edge_op']=='and' else w[0] or w[1])
 for op,u,v in gates:w.append(w[u] and w[v] if op==0 else w[u] or w[v] if op==1 else not w[u])
 if w[-1]!=target:errors.append(x)
out={'gates':gates,'output':10+len(gates),'edge_op':d['edge_op'],'errors':errors,'rows_checked':1024};Path(a.output).write_text(json.dumps(out,indent=2));print('Validated all 1024 rows; gates excluding free edge =',len(gates),'NOTs =',sum(o==2 for o,_,_ in gates),'errors =',len(errors));assert not errors
