from pathlib import Path
import json
base=Path(__file__).resolve().parent;n=6;edges=[tuple(sorted((i,(i+1)%6))) for i in range(6)];graph=[any(m>>a&1 and m>>b&1 for a,b in edges) for m in range(64)];neg=[m for m in range(64) if not graph[m]];mis=[m for m in neg if all(m>>i&1 or m|(1<<i) not in neg for i in range(6))];omit=21;assert omit in mis;order=[m for m in mis if m!=omit]+[omit];gates=[];roots=[]
def add(op,a,b):gates.append([op,a,b]);return 5+len(gates)
for m in order:
 xs=[i for i in range(6) if not(m>>i&1)];w=xs[0]
 for q in xs[1:]:w=add('or',w,q)
 roots.append(w)
w=roots[0]
for q in roots[1:-1]:w=add('and',w,q)
D=w;out=add('and',w,roots[-1]);values=[[bool(m>>i&1) for m in range(64)] for i in range(6)];support=[{i} for i in range(6)];anc=[set() for _ in range(6)];tops=[];junk=[]
for j,(op,a,b) in enumerate(gates):
 values.append([x and y if op=='and' else x or y for x,y in zip(values[a],values[b])]);support.append(set() if op=='and' else support[a]|support[b]);anc.append(anc[a]|anc[b]|({a-6} if a>=6 else set())|({b-6} if b>=6 else set()))
 if op=='and':(tops if all(not v or g for v,g in zip(values[-1],graph)) else junk).append(j)
assert values[out]==graph
assert values[D]==[g or m&omit==omit for m,g in enumerate(graph)]
bad=[m for m in neg if values[D][m]];assert bad==[21]
assert all(i not in anc[6+j] for i in tops for j,g in enumerate(gates) if g[0]=='and')
star={tuple(sorted((p,q))) for j in tops for p in support[gates[j][1]] for q in support[gates[j][2]]};ustar=sorted(set(edges)-star)
report={'n':6,'gates':gates,'output':out,'distinguished_dirty_wire':D,'graph_edges':edges,'size':len(gates),'full_truth_rows_checked':64,'TopForm':True,'tops':tops,'junk':junk,'Ustar':ustar,'dirty_bad_assignments':bad,'min_independent_bad_certificate':3,'dirty_function':'F_C6 OR (x0 AND x2 AND x4)','standard_star_upper':8,'least':False,'scope':'nonleast TopForm control showing dirty certificates need not be singletons/pairs'}
(base/'c6-bad-triple-control.witness.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='gates'},indent=2))
