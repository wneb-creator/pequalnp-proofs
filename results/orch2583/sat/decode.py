#!/usr/bin/env python3
"""Decode and independently verify an AO2 synthesis model, including READ-1."""
import argparse
import json
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('metadata',type=Path)
p.add_argument('solver_log',type=Path)
p.add_argument('output',type=Path)
p.add_argument('--cnf',type=Path)
a=p.parse_args()
m=json.loads(a.metadata.read_text());d=json.loads(Path(m['data']).read_text())
n=d['n'];s=m['size'];edges=d['edges'];rows=d['rows'];assign={}
lines=a.solver_log.read_text().splitlines()
if 's SATISFIABLE' not in lines:raise SystemExit('No SAT model in solver log')
for line in lines:
 if line.startswith('v '):
  for lit in map(int,line[2:].split()):
   if lit:assign[abs(lit)]=lit>0
def true(v):return assign[v]
gates=[]
for j in range(s):
 ss=[]
 for side in range(2):
  hits=[k for k,v in enumerate(m['src'][j][side]) if true(v)]
  assert len(hits)==1,hits
  ss.append(hits[0])
 gates.append(['or' if true(m['op'][j]) else 'and',*ss])
allrows=range(1<<n)
w=[sum(1<<r for r in allrows if r>>i&1) for i in range(n)]
leaf=[1<<i for i in range(n)];clean=[0]*n
for op,u,v in gates:
 assert 0<=u<len(w) and 0<=v<len(w)
 w.append((w[u]|w[v]) if op=='or' else (w[u]&w[v]))
 if op=='or':leaf.append(leaf[u]|leaf[v]);clean.append(clean[u]|clean[v])
 else:
  leaf.append(0)
  clean.append(sum(1<<k for k,(x,y) in enumerate(edges)
   if (leaf[u]>>x&1 and leaf[v]>>y&1) or (leaf[u]>>y&1 and leaf[v]>>x&1)))
target=sum(1<<r for r in allrows if any(r>>u&1 and r>>v&1 for u,v in edges))
wrong=w[-1]^target
violations=[];clauses=0
if a.cnf:
 for line in a.cnf.read_text().splitlines():
  if line.startswith(('c','p')):continue
  lits=list(map(int,line.split()));assert lits[-1]==0;lits=lits[:-1];clauses+=1
  if not any(assign[abs(v)]==(v>0) for v in lits):violations.append(clauses)
report={'gates':gates,'output':n+s-1,'padding':[j for j,v in enumerate(m['pad']) if true(v)],
 'truth_table_wrong_count':wrong.bit_count(),'wrong_rows':[r for r in allrows if wrong>>r&1],
 'boundary_wrong_count':sum(bool(wrong>>r&1) for r in rows),'read1_edges':clean[-1].bit_count(),
 'read1_missing_edges':[e for k,e in enumerate(edges) if not clean[-1]>>k&1],
 'checked_cnf_clauses':clauses,'violated_cnf_clauses':violations}
a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['gates','wrong_rows']}))
assert not violations
