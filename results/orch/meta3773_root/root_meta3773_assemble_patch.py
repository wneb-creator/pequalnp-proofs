from pathlib import Path
import argparse,itertools,json,hashlib
p=argparse.ArgumentParser(description="Assemble a compatible projective-plane patch into a normalized full incidence circuit and independently replay all posted tests.")
p.add_argument("--candidate",type=Path)
p.add_argument("--data",type=Path,default=Path("/tmp/oec/pequalnp-pilot-79/meta3773-five-patch-data.json"))
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
j=Path("/tmp/oec/pequalnp-pilot-79")
data=json.loads(a.data.read_text())
D={0,1,3,9};points=data["point_inputs"];lines=data["line_inputs"]
k=len(points);raw_n=k+len(lines);n_inputs=data["inputs_with_free_or_signals"];assert k in [4,5] and raw_n==data["raw_inputs"]
if a.candidate:
 source=json.loads(a.candidate.read_text());patch=source["gates"]
 helpers=source.get("free_or_gates",data["default_free_ors"])
else:
 helpers=data["default_free_ors"];patch=[];terms=[]
 for i in range(k):
  ns=[v for u,v in data["edges"] if u==i]
  t=ns[0]
  for v in ns[1:]:patch.append([1,t,v]);t=n_inputs+len(patch)-1
  patch.append([0,i,t]);terms.append(n_inputs+len(patch)-1)
 t=terms[0]
 for v in terms[1:]:patch.append([1,t,v]);t=n_inputs+len(patch)-1
assert len(helpers)==n_inputs-raw_n
mapping={i:points[i] for i in range(k)}
mapping.update({k+i:13+l for i,l in enumerate(lines)})
gates=[]
def add(op,a,b):
 assert op in [0,1] and 0<=a<26+len(gates) and 0<=b<26+len(gates)
 gates.append([op,a,b]);return 25+len(gates)
for i,h in enumerate(helpers):
 assert h["wire"]==raw_n+i and h["op"]=="or"
 x,y=h["inputs"];assert x<raw_n+i and y<raw_n+i
 mapping[raw_n+i]=add(1,mapping[x],mapping[y])
terms=[]
for group in data["outside_groups"]:
 point=group["outside_point"];ns={l for l in range(13) if (point+l)%13 in D}
 v=mapping[group["first_free_wire"]+len(group["raw_wires"])-2]
 # Verify chosen helper chain really covers precisely the in-patch neighbors.
 supports={i:{lines[i-k]} for i in range(k,raw_n)}
 for h in helpers:
  supports[h["wire"]]=supports[h["inputs"][0]]|supports[h["inputs"][1]]
 assert supports[group["first_free_wire"]+len(group["raw_wires"])-2]==ns.intersection(lines)
 for line in sorted(ns.difference(lines)):v=add(1,v,13+line)
 terms.append(add(0,point,v))
assert len(gates)==4*(13-k)
for i,(op,x,y) in enumerate(patch):
 assert 0<=x<n_inputs+i and 0<=y<n_inputs+i
 mapping[n_inputs+i]=add(op,mapping[x],mapping[y])
assert patch
terms.append(mapping[n_inputs-1+len(patch)])
t=terms[0]
for v in terms[1:]:t=add(1,t,v)
assert len(gates)==65-5*k+len(patch) and t==25+len(gates)
first= gates[0][1:]
assert all(13<=i<26 for i in first)
l1,l2=[i-13 for i in first]
permutation=None
for u in [1,3,9]:
 for reverse in [False,True]:
  left,right=(l2,l1) if reverse else (l1,l2)
  if u*(right-left)%13!=1:continue
  shift=u*left%13
  permutation=[13+(u*i+shift)%13 if i<13 else (u*(i-13)-shift)%13 for i in range(26)]
  break
 if permutation is not None:break
if permutation is None:
 def norm(v):
  v=tuple(x%3 for x in v);lead=next(x for x in v if x)
  return tuple(x*pow(lead,-1,3)%3 for x in v)
 def cross(a,b):return norm((a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]))
 pv={0:(1,0,0),1:(0,1,0),2:(0,0,1),5:(1,1,1)};lv={}
 for step in range(10):
  old=(len(pv),len(lv))
  for x,y in itertools.combinations(list(pv),2):
   labs=[l for l in range(13) if (x+l)%13 in D and (y+l)%13 in D];assert len(labs)==1
   lab=labs[0];v=cross(pv[x],pv[y]);assert lab not in lv or lv[lab]==v;lv[lab]=v
  for x,y in itertools.combinations(list(lv),2):
   labs=[p0 for p0 in range(13) if (p0+x)%13 in D and (p0+y)%13 in D];assert len(labs)==1
   lab=labs[0];v=cross(lv[x],lv[y]);assert lab not in pv or pv[lab]==v;pv[lab]=v
  if (len(pv),len(lv))==old:break
 assert len(pv)==len(lv)==13
 for p0 in range(13):
  for l0 in range(13):assert ((p0+l0)%13 in D)==(sum(x*y for x,y in zip(pv[p0],lv[l0]))%3==0)
 def columns(vs):return [[vs[c][r] for c in range(3)] for r in range(3)]
 def inverse(A):
  m=[[A[r][c]%3 for c in range(3)]+[int(r==c) for c in range(3)] for r in range(3)]
  for c in range(3):
   choices=[r for r in range(c,3) if m[r][c]]
   if not choices:return None
   r=choices[0];m[c],m[r]=m[r],m[c];u=pow(m[c][c],-1,3);m[c]=[x*u%3 for x in m[c]]
   for r in range(3):
    if r!=c:
     u=m[r][c];m[r]=[(x-u*y)%3 for x,y in zip(m[r],m[c])]
  return [row[3:] for row in m]
 src_inv=None
 for l3 in range(13):
  src_inv=inverse(columns([lv[l1],lv[l2],lv[l3]]))
  if src_inv is not None:break
 assert src_inv is not None
 target=columns([pv[0],pv[1],pv[2]])
 A=[[sum(target[r][k]*src_inv[k][c] for k in range(3))%3 for c in range(3)] for r in range(3)]
 Ai=inverse(A);assert Ai is not None
 def apply(M,v):return norm(tuple(sum(M[r][c]*v[c] for c in range(3))%3 for r in range(3)))
 ATi=[[Ai[c][r] for c in range(3)] for r in range(3)]
 points_by_vec={v:k for k,v in pv.items()};lines_by_vec={v:k for k,v in lv.items()}
 permutation=[13+lines_by_vec[apply(ATi,pv[i])] for i in range(13)]+[points_by_vec[apply(A,lv[i])] for i in range(13)]
assert sorted(permutation)==list(range(26))
for p0 in range(13):
 for l0 in range(13):assert ((p0+l0)%13 in D)==((permutation[p0]+permutation[13+l0]-13)%13 in D)
def rename(i):return permutation[i] if i<26 else i
normalized=[[op,rename(x),rename(y)] for op,x,y in gates]
if normalized[0]==[1,1,0]:normalized[0]=[1,0,1]
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
result={"scope":"independent finite replay; not a Lean proof", "source_data_sha256":hashlib.sha256(a.data.read_bytes()).hexdigest(),"patch_gates":patch,"free_or_gates":helpers,"gates":normalized,"output":25+len(gates),"size":len(gates),"first_gate":normalized[0],"rows":808,"errors":errors,"all_posted_tests_pass":errors==0,"target_63_met":errors==0 and len(gates)<=63}
a.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:result[k] for k in ["size","first_gate","rows","errors","all_posted_tests_pass","target_63_met"]}))
assert errors==0
