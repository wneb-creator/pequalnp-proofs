import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('circuit');p.add_argument('output');a=p.parse_args()
d=json.loads(Path(a.circuit).read_text());raw=d['gates'];mapping=[0,4,3,2,7,5]
def wire(i):return mapping[i] if i<6 else i+4
out=[]
for i,(op,x,y) in enumerate(raw):
 op={0:'and',1:'or',2:'not'}.get(op,op)
 assert op in ('and','or','not')
 assert x<6+i and (op=='not' or y<6+i)
 out.append({'op':op,'inputs':[wire(x)] if op=='not' else [wire(x),wire(y)]})
assert [(g['op'],sorted(g['inputs'])) for g in out[:3]]==[('or',[0,2]),('or',[3,5]),('or',[4,7])]
roots=[wire(d['output'])]
for center,prefix in ((1,10),(8,11),(9,12)):
 k=10+len(out);out.append({'op':'or','inputs':[prefix,6]});out.append({'op':'and','inputs':[center,k]});roots.append(k+1)
root=roots[0]
for other in roots[1:]:
 k=10+len(out);out.append({'op':'or','inputs':[root,other]});root=k
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
errors=[]
for x in range(1024):
 w=[bool(x>>i&1) for i in range(10)];target=any(w[i] and w[j] for i,j in edges)
 for g in out:
  v=[w[i] for i in g['inputs']];w.append(all(v) if g['op']=='and' else any(v) if g['op']=='or' else not v[0])
 if w[root]!=target:errors.append(x)
assert not errors,errors
not_count=sum(g['op']=='not' for g in out)
r={'gates':out,'output':root,'size':len(out),'not_gates':not_count,'truth_table_errors':errors,'qualifies_for_L_meta_2592_counterexample':len(out)<=19 and not_count>=1}
Path(a.output).write_text(json.dumps(r,indent=2))
print(json.dumps({k:v for k,v in r.items() if k!='gates'},indent=2))
