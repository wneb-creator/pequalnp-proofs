from pathlib import Path
import json,itertools
base=Path(__file__).resolve().parent;spec=json.loads((base/'subdivided-k4.json').read_text());n=8;edges={tuple(sorted(e)) for e in spec['edges']};gates=[list(g) for g in spec['prefix']]
def add(op,a,b):gates.append([op,a,b]);return 7+len(gates)
g=add('and',8,9);h=add('and',g,10);core=add('and',h,11);stars=[add('and',i,8+j) for j,i in enumerate(range(4,8))];out=core
for x in stars:out=add('or',out,x)
assert len(gates)==15
values=[[bool(m>>i&1) for m in range(256)] for i in range(8)];support=[{i} for i in range(8)];anc=[set() for _ in range(8)];graph=[any(m>>a&1 and m>>b&1 for a,b in edges) for m in range(256)];tops=[];junk=[]
for j,(op,a,b) in enumerate(gates):
 values.append([x and y if op=='and' else x or y for x,y in zip(values[a],values[b])]);support.append(set() if op=='and' else support[a]|support[b]);anc.append(anc[a]|anc[b]|({a-8} if a>=8 else set())|({b-8} if b>=8 else set()))
 if op=='and':(tops if all(not v or g for v,g in zip(values[-1],graph)) else junk).append(j)
assert values[out]==graph
assert all(i not in anc[8+j] for i in tops for j,g in enumerate(gates) if g[0]=='and')
assert all(not all(tuple(sorted(e)) in edges for e in [(a,b),(b,c),(c,a)]) for a,b,c in itertools.combinations(range(8),3))
assert all(sum(tuple(sorted((a,w))) in edges and tuple(sorted((b,w))) in edges for w in range(8))<=1 for a,b in itertools.combinations(range(8),2))
covers=[m for m in range(256) if all(m>>a&1 or m>>b&1 for a,b in edges)];tau=min(map(int.bit_count,covers));assert tau==4
star={tuple(sorted((p,q))) for j in tops for p in support[gates[j][1]] for q in support[gates[j][2]]};ustar=sorted(edges-star);assert ustar==[(0,2),(1,3)]
report={'n':8,'gates':gates,'output':out,'graph_edges':sorted(edges),'size':15,'full_truth_rows_checked':256,'girth_at_least5':True,'minimum_vertex_cover':4,'standard_star_upper':13,'least':False,'TopForm':True,'tops':tops,'junk':junk,'nested_junk_pairs':[(i,j) for i in junk for j in junk if i in anc[8+j]],'Ustar':ustar,'scope':'shared dirty-clause TopForm positive control; not least and not a counterexample to L-meta-1735'}
(base/'subdivided-k4-control15.witness.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='gates'},indent=2))
