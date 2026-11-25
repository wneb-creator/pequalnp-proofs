from pathlib import Path
import json,sys,itertools
base=Path(__file__).resolve().parent;m=int(sys.argv[1]);n=2*m;edges=[(2*i,2*i+1) for i in range(m)];graph=[any(mask>>a&1 and mask>>b&1 for a,b in edges) for mask in range(1<<n)];S=sum(1<<(2*i) for i in range(m));transversals=[sum(1<<(2*i+b) for i,b in enumerate(bs)) for bs in itertools.product(range(2),repeat=m)];order=[s for s in transversals if s!=S]+[S];gates=[];roots=[]
def add(op,a,b):gates.append([op,a,b]);return n-1+len(gates)
for s in order:
 clause=[i for i in range(n) if not(s>>i&1)];w=clause[0]
 for q in clause[1:]:w=add('or',w,q)
 roots.append(w)
w=roots[0]
for q in roots[1:-1]:w=add('and',w,q)
D=w;out=add('and',w,roots[-1]);values=[[bool(mask>>i&1) for mask in range(1<<n)] for i in range(n)];support=[{i} for i in range(n)];anc=[set() for _ in range(n)];tops=[];junk=[]
for j,(op,a,b) in enumerate(gates):
 assert 0<=a<n+j and 0<=b<n+j
 values.append([x and y if op=='and' else x or y for x,y in zip(values[a],values[b])]);support.append(set() if op=='and' else support[a]|support[b]);anc.append(anc[a]|anc[b]|({a-n} if a>=n else set())|({b-n} if b>=n else set()))
 if op=='and':(tops if all(not v or g for v,g in zip(values[-1],graph)) else junk).append(j)
assert values[out]==graph
assert values[D]==[g or mask&S==S for mask,g in enumerate(graph)]
bad=[mask for mask,g in enumerate(graph) if not g and values[D][mask]];assert bad==[S]
assert all(i not in anc[n+j] for i in tops for j,g in enumerate(gates) if g[0]=='and')
star={tuple(sorted((p,q))) for j in tops for p in support[gates[j][1]] for q in support[gates[j][2]]};ustar=sorted(set(edges)-star)
assert len(gates)==m*(1<<m)-1 and len(ustar)==m
report={'n':n,'matching_size':m,'gates':gates,'output':out,'distinguished_dirty_wire':D,'graph_edges':edges,'size':len(gates),'full_truth_rows_checked':1<<n,'TopForm':True,'tops':tops,'junk':junk,'Ustar':ustar,'dirty_bad_assignments':bad,'min_independent_bad_certificate':m,'dirty_function':'matching edge function OR conjunction of even-indexed inputs','standard_star_upper':2*m-1,'least':False,'scope':'nonleast TopForm control showing no uniform bound on independent dirty-certificate size'}
(base/f'matching{m}-bad-certificate.witness.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='gates'},indent=2))
