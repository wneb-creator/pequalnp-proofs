from pathlib import Path
import sys,json
n,s=10,18
A=(1<<n)+n+s+1
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(r): return any((r>>u)&1 and (r>>v)&1 for u,v in edges)
def p(kd,j,a): return (kd*(s+1)+j)*A+a+1
positive=set()
for line in Path(sys.argv[1]).read_text().splitlines():
 if line.startswith('v '): positive.update(int(v) for v in line.split()[1:] if int(v)>0)
def selected(kd,j,m):
 choices=[a for a in range(m) if p(kd,j,a) in positive]
 if not choices: raise ValueError(f'No choice {kd,j,m}')
 return choices[0]
circuit=[]
for j in range(s):
 op=selected(0,j,3)
 a,b=selected(1,j,n+j+1),selected(2,j,n+j+1)
 circuit.append({'op':['and','or','and'][op], 'inputs':[] if op==2 else [a,b]})
output=selected(6,0,n+s+1)
# Add a dead NOT while preserving the selected output.
circuit.append({'op':'not','inputs':[0]})
rows=[]; errors=[]
for r in range(1<<n):
 w=[bool((r>>i)&1) for i in range(n)]
 for gate in circuit:
  vals=[w[k] if k<len(w) else False for k in gate['inputs']]
  w.append(all(vals) if gate['op']=='and' else any(vals) if gate['op']=='or' else not vals[0])
 got=w[output] if output<len(w) else False
 want=bool(target(r))
 rows.append({'row':r,'expected':want,'actual':got})
 if got!=want: errors.append(r)
report={'gates':circuit,'output':output,'actual_size':len(circuit),'actual_not_count':sum(g['op']=='not' for g in circuit),'errors':errors,'rows':rows,'held_gap_counterexample':len(circuit)<=19 and any(g['op']=='not' for g in circuit) and not errors}
Path(sys.argv[2]).write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k not in ['gates','rows']}))
