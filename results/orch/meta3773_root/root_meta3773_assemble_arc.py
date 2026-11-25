from pathlib import Path
import argparse,itertools,json,hashlib
p=argparse.ArgumentParser(description="Assemble a compatible four-arc patch into a normalized full incidence circuit and independently replay all posted tests.")
p.add_argument("--candidate",type=Path)
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
j=Path("/tmp/oec/pequalnp-pilot-79")
data=json.loads((j/"meta3773-full-patch-data.json").read_text())
D={0,1,3,9};points=data["point_inputs"];lines=data["line_inputs"]
assert points==[0,1,2,5] and len(lines)==10
if a.candidate:
 source=json.loads(a.candidate.read_text());patch=source["gates"]
 helpers=source.get("free_or_gates",data["default_free_ors"])
else:
 helpers=data["default_free_ors"];patch=[];terms=[]
 for i in range(4):
  ns=[v for u,v in data["edges"] if u==i]
  t=ns[0]
  for v in ns[1:]:patch.append([1,t,v]);t=29+len(patch)-1
  patch.append([0,i,t]);terms.append(29+len(patch)-1)
 t=terms[0]
 for v in terms[1:]:patch.append([1,t,v]);t=29+len(patch)-1
assert len(helpers)==15
mapping={i:points[i] for i in range(4)}
mapping.update({4+i:13+l for i,l in enumerate(lines)})
gates=[]
def add(op,a,b):
 assert op in [0,1] and 0<=a<26+len(gates) and 0<=b<26+len(gates)
 gates.append([op,a,b]);return 25+len(gates)
for i,h in enumerate(helpers):
 assert h["wire"]==14+i and h["op"]=="or"
 x,y=h["inputs"];assert x<14+i and y<14+i
 mapping[14+i]=add(1,mapping[x],mapping[y])
terms=[]
for group in data["outside_groups"]:
 point=group["outside_point"];ns={l for l in range(13) if (point+l)%13 in D}
 v=mapping[group["first_free_wire"]+len(group["raw_wires"])-2]
 # Verify chosen helper chain really covers precisely the in-patch neighbors.
 supports={i:{lines[i-4]} for i in range(4,14)}
 for h in helpers:
  supports[h["wire"]]=supports[h["inputs"][0]]|supports[h["inputs"][1]]
 assert supports[group["first_free_wire"]+len(group["raw_wires"])-2]==ns.intersection(lines)
 for line in sorted(ns.difference(lines)):v=add(1,v,13+line)
 terms.append(add(0,point,v))
assert len(gates)==36
for i,(op,x,y) in enumerate(patch):
 assert 0<=x<29+i and 0<=y<29+i
 mapping[29+i]=add(op,mapping[x],mapping[y])
assert patch
terms.append(mapping[28+len(patch)])
t=terms[0]
for v in terms[1:]:t=add(1,t,v)
assert len(gates)==45+len(patch) and t==25+len(gates)
def rename(i):
 if i<13:return 13+(9*i+3)%13
 if i<26:return (9*(i-13)-3)%13
 return i
normalized=[[op,rename(x),rename(y)] for op,x,y in gates]
assert normalized[0]==[1,0,1]
rows=[]
for point in range(13):
 for line in range(13):
  if (point+line)%13 in D:rows.append(((1<<point)|(1<<(13+line)),True))
for k in range(4):
 for sub in itertools.combinations(range(13),k):
  off=[l for l in range(13) if all((point+l)%13 not in D for point in sub)]
  left=sum(1<<i for i in sub);right=sum(1<<i for i in off)
  rows.append((left|(right<<13),False));rows.append((right|(left<<13),False))
assert len(rows)==808 and sum(v for m,v in rows)==52
vals=[sum(((m>>i)&1)<<t for t,(m,e) in enumerate(rows)) for i in range(26)]
for op,x,y in normalized:vals.append((vals[x]|vals[y]) if op else (vals[x]&vals[y]))
target=sum(int(e)<<t for t,(m,e) in enumerate(rows))
errors=(vals[-1]^target).bit_count()
result={"scope":"independent finite replay; not a Lean proof", "source_data_sha256":hashlib.sha256((j/"meta3773-full-patch-data.json").read_bytes()).hexdigest(),"patch_gates":patch,"free_or_gates":helpers,"gates":normalized,"output":25+len(gates),"size":len(gates),"first_gate":normalized[0],"rows":808,"errors":errors,"all_posted_tests_pass":errors==0,"target_63_met":errors==0 and len(gates)<=63}
a.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:result[k] for k in ["size","first_gate","rows","errors","all_posted_tests_pass","target_63_met"]}))
assert errors==0
