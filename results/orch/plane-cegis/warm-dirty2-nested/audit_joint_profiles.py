import argparse,json,hashlib
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--data',required=True)
p.add_argument('--gates',required=True,nargs='+')
p.add_argument('--output',required=True)
a=p.parse_args()
data=json.loads(Path(a.data).read_text())
assert data['n']==26
edges=sorted(tuple(e) for e in data['edges'])
assert set(edges)=={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
records=[]
for name in a.gates:
 source=Path(name);gates=json.loads(source.read_text())
 bad=[];accepted_bad=[];comparisons=0
 for p,l in edges:
  counts=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(26)]
  triples=[(i==p,i==l,False) for i in range(26)]
  truth=[i in (p,l) for i in range(26)]
  for j,(op,u,v) in enumerate(gates):
   assert op in (0,1) and 0<=u<26+j and 0<=v<26+j
   if op:
    counts.append(counts[u]|counts[v])
    triples.append(tuple(x or y for x,y in zip(triples[u],triples[v])))
    truth.append(truth[u] or truth[v])
   else:
    counts.append({(min(2,x1+y1),min(2,x2+y2)) for x1,x2 in counts[u] for y1,y2 in counts[v]})
    aa,bb=triples[u],triples[v]
    triples.append((False,False,(aa[0] and bb[1]) or (aa[1] and bb[0])))
    truth.append(truth[u] and truth[v])
  for count,triple in zip(counts,triples):
   assert (0,0) not in count
   assert all(0<=x<=2 and 0<=y<=2 for x,y in count)
   assert triple==tuple(v in count for v in [(1,0),(0,1),(1,1)])
   comparisons+=1
  if not triples[-1][2]:
   bad.append([p,l])
   if truth[-1]:accepted_bad.append([p,l])
 violations=[]
 for row in data['rows']:
  vs=[bool(row&(1<<i)) for i in range(26)]
  for op,u,v in gates:vs.append(vs[u] or vs[v] if op else vs[u] and vs[v])
  want=any(bool(row&(1<<p)) and bool(row&(1<<l)) for p,l in edges)
  if vs[-1]!=want:violations.append(row)
 records.append({'path':str(source),'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'size':len(gates),'first_gate':gates[0],'wire_edge_comparisons':comparisons,'missing_joint11_edges':bad,'accepted_nonread1_edges':accepted_bad,'full_boundary_mismatches':violations})
result={'scope':'Independent capped-count recursion compared to three-state recurrence on every wire and every incident pair; external diagnostic, not Lean proof','records':records}
Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
