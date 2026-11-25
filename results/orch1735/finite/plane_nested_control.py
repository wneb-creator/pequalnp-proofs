from pathlib import Path
import json,itertools
base=Path(__file__).resolve().parent;n=26;v=13;diff={0,1,3,9};edges=[(p,13+l) for p in range(v) for l in range(v) if(p-l)%v in diff]
assert len(edges)==52
assert all(sum((p,13+l) in edges and (q,13+l) in edges for l in range(v))<=1 for p in range(v) for q in range(p))
negative=[]
for pm in range(1<<v):
 qs={l for l in range(v) if all(not(pm>>p&1) or (p,13+l) not in edges for p in range(v))}
 ps={p for p in range(v) if all((p,13+l) not in edges for l in qs)}
 if sum(1<<p for p in ps)==pm:negative.append(pm|sum(1<<(13+l) for l in qs))
assert len(negative)==704
positive=[(1<<a)|(1<<b) for a,b in edges];rows=positive+negative;target=(1<<len(positive))-1;bad=((1<<len(rows))-1)^target
wires=[sum(1<<j for j,m in enumerate(rows) if m>>i&1) for i in range(n)];support=[{i} for i in range(n)];ancestors=[set() for _ in range(n)];gates=[]
def gate(op,a,b):
 j=len(gates);assert a<n+j and b<n+j
 gates.append([op,a,b]);wires.append(wires[a]&wires[b] if op=='and' else wires[a]|wires[b]);support.append(set() if op=='and' else support[a]|support[b]);ancestors.append(ancestors[a]|ancestors[b]|({a-n} if a>=n else set())|({b-n} if b>=n else set()));return n+j
def disj(vs):
 out=vs[0]
 for w in vs[1:]:out=gate('or',out,w)
 return out
left=disj(list(range(13)));right=disj(list(range(13,26)));D=gate('and',left,right);roots=[];filters=[]
for p in range(13):
 Np=disj([q for a,q in edges if a==p]);J=gate('and',D,Np);filters.append(J);roots.append(gate('and',p,J))
out=disj(roots);assert wires[out]==target
clean=[j for j in range(len(gates)) if not(wires[n+j]&bad)];tops=[j for j in clean if gates[j][0]=='and'];junk=[j for j,g in enumerate(gates) if g[0]=='and' and j not in clean]
assert all(i not in ancestors[n+j] for i in tops for j,g in enumerate(gates) if g[0]=='and')
star={tuple(sorted((p,q))) for j in tops for p in support[gates[j][1]] for q in support[gates[j][2]]};ustar=sorted(set(edges)-star)
assert len(gates)==102 and len(ustar)==52 and len(tops)==13 and len(junk)==14
pairs=[(i,j) for j in junk for i in junk if i in ancestors[n+j]];assert len(pairs)==13
witnesses={str(j):rows[(wires[n+j]&bad & -(wires[n+j]&bad)).bit_length()-1] for j in junk}
report={'n':26,'gates':gates,'output':out,'graph_edges':edges,'minimal_positive_rows':52,'maximal_negative_rows':704,'exact_semantics_verified':True,'girth_at_least_6':'bipartite and pairwise-left common-neighbor count <=1 verified','size':102,'star_upper_bound':64,'is_least':False,'leastness_failure':'explicit standard point-star circuit has only64 gates','TopForm':True,'tops':tops,'junk':junk,'nested_junk_pairs':pairs,'dirty_witness_masks':witnesses,'Ustar':ustar,'ratio_Ustar_over_size_plus_one':52/103,'scope':'nonleast nested-junk diagnostic, not a refutation of L-meta-1735'}
(base/'plane-nested-control102.witness.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['gates','graph_edges','Ustar','dirty_witness_masks']},indent=2))
