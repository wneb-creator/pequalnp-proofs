import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--data',required=True);p.add_argument('--rows',required=True);p.add_argument('--model',required=True);p.add_argument('--output-rows',required=True);p.add_argument('--report',required=True);p.add_argument('--batch',type=int,default=16)
a=p.parse_args();data=json.loads(Path(a.data).read_text());rows=json.loads(Path(a.rows).read_text());model=json.loads(Path(a.model).read_text());n=data['n'];gates=model['gates']
assert n==26 and len(gates)==63 and len(rows)==len(set(rows)) and a.batch>0
assert set(data['positive_rows']).issubset(rows)
assert all(isinstance(g,list) and len(g)==3 and all(type(x)is int for x in g) and g[0] in (0,1) and 0<=g[1]<n+j and 0<=g[2]<n+j for j,g in enumerate(gates))
violations=[]
for row in data['rows']:
 values=[bool(row&(1<<i)) for i in range(n)]
 for op,u,v in gates:values.append(values[u] and values[v] if op==0 else values[u] or values[v])
 expected=any(bool(row&(1<<u)) and bool(row&(1<<v)) for u,v in data['edges'])
 if values[-1]!=expected:violations.append(row)
assert set(violations)==set(model['full_boundary_mismatches'])
assert set(violations).issubset(data['negative_rows']) and not set(violations)&set(rows)
remaining=set(violations);selected=[];anchors=[r for r in rows if r in set(data['negative_rows'])]
while remaining and len(selected)<a.batch:
 chosen=max(remaining,key=lambda r:(min((r^s).bit_count() for s in anchors+selected),-r))
 selected.append(chosen);remaining.remove(chosen)
updated=sorted(set(rows)|set(selected));Path(a.output_rows).write_text(json.dumps(updated,indent=2)+'\n')
report={'status':'full boundary passed; Lean verification still required' if not violations else 'counterexamples added','gates':len(gates),'tested_rows':len(data['rows']),'violations':len(violations),'previous_rows':len(rows),'selected_rows':selected,'updated_rows':len(updated)}
Path(a.report).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
