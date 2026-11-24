from pathlib import Path
import hashlib,itertools,json,time
ROOT=Path('/tmp/oec/pequalnp-pilot-18')
OUT=ROOT/'orch/S04'
E=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
EM=[(1<<a)|(1<<b) for a,b in E]
N=[sum(1<<(b if a==v else a) for a,b in E if v in (a,b)) for v in range(11)]
def F(x):return any(x&e==e for e in EM)
def H(v,x):return F(x) or bool(x&N[v])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ind=[x for x in range(2048) if not F(x)]
assert len(ind)==125
families=[]
for tri in [(1,4,8),(3,6,7)]:
 factors=[]
 for v in tri:
  s=N[v]; residual=[e for e in EM if not e&s]
  cover=min((c.bit_count(),c) for c in range(2048) if all(c&e for e in residual))
  cn=[w for w in range(11) if s&~N[w]==0]
  assert cn==[v]
  factors.append(dict(owner=v,support=s,residual_edges=residual,cover_size=cover[0],cover=cover[1],L=s.bit_count()+len(residual)+cover[0]-1))
 assert all(all(H(v,x) for v in tri)==F(x) for x in range(2048))
 witnesses=[]
 for v in tri:
  x=1<<v; assert [H(w,x) for w in tri]==[w!=v for w in tri]
  witnesses.append(x)
 si=N[tri[0]]; d=sum(bool(si&(1<<v)) for v in tri[1:]); assert d==2
 cases=[]
 for ancestry in itertools.product([False,True],repeat=2):
  inside=sum(ancestry); bound=factors[0]['L']+inside+2-inside
  cases.append(dict(ancestor_flags=ancestry,AND_charge=inside,outside_gate_charge=2-inside,total_bound=bound))
 families.append(dict(triangle=tri,factors=factors,minimal_witnesses=witnesses,joint_bound=bound,ancestry_cases=cases))
assert [f['joint_bound'] for f in families]==[18,19]

# Actual clean DAGs with shared edge nodes, repeated OR operands, free constants,
# and a charged first-AND lying inside the other charged gate's B operand.
# Evaluate and remove all charges jointly; every original wire retains boundary values.
def make_control(tri,mode):
 gates=[]
 def gate(op,a,b):gates.append((op,a,b));return 12+len(gates)
 def OR(xs):
  xs=list(xs); out=xs[0]
  for w in xs[1:]:out=gate('or',out,w)
  return out
 edges={e:gate('and',a,b) for e,(a,b) in zip(EM,E)}
 if mode&1:
  gate('or',12,12) # dead TRUE copy; does not enter any productive clean AND
  zero=gate('or',11,11)
 else:zero=11
 def factor(v):
  s=N[v]; leaves=[i for i in range(11) if s>>i&1]+[edges[e] for e in EM if not e&s]
  out=OR(leaves)
  if mode&1:out=gate('or',out,zero);out=gate('or',out,out)
  return out
 i,j,k=tri; wj=factor(j); wk=factor(k)
 residual=[e for e in EM if not e&N[i]]
 assert len(residual)>=2
 # B_k has singleton support {k}; B_j has singleton support {j}, and depends on q_k.
 bk=OR([k,edges[residual[0]]]);qk=gate('and',wk,bk)
 bj=OR([j,edges[residual[1]],qk]);qj=gate('and',wj,bj)
 support=OR([v for v in range(11) if N[i]>>v&1])
 if mode&2:support=gate('or',support,support)
 wi=OR([support]+[edges[e] for e in residual]+[qj,qk])
 if mode&1:wi=gate('or',wi,zero);wi=gate('or',wi,wi)
 return gates,wi,[wi,wj,wk],{qj:bj,qk:bk}

def evaluate(gates,x):
 values=[bool(x>>v&1) for v in range(11)]+[False,True]
 for op,a,b in gates:values.append(values[a] and values[b] if op=='and' else values[a] or values[b])
 return values
controls=[]
for tri in [(1,4,8),(3,6,7)]:
 for mode in range(4):
  gates,output,outputs,charged=make_control(tri,mode)
  values=[evaluate(gates,x) for x in range(2048)]
  supports=[sum(1<<v for v in range(11) if values[1<<v][w]) for w in range(13+len(gates))]
  for g,(op,a,b) in enumerate(gates):
   if op=='and':
    assert supports[a] and supports[b]
    assert all(not values[x][13+g] for x in ind)
  assert all([values[x][w] for w in outputs]==[H(v,x) for v in tri] for x in range(2048))
  cone=set()
  def visit(w):
   if w<13 or w in cone:return
   cone.add(w)
   _,a,b=gates[w-13];visit(a);visit(b)
  visit(output)
  ancestry=set()
  def orvisit(w):
   if w in ancestry:return
   ancestry.add(w)
   if w>=13:
    op,a,b=gates[w-13]
    if op=='or':orvisit(a);orvisit(b)
  orvisit(output)
  si=N[tri[0]]
  pure={v for v in range(11) if si>>v&1}|{11}
  for g,(op,a,b) in enumerate(gates):
   if op=='or' and a in pure and b in pure:pure.add(g+13)
  pure_gates={w for w in ancestry&pure if w>=13}
  boundary={}
  for w in ancestry-pure:
   if w>=13:
    op,a,b=gates[w-13]
    if op=='or' and ((a in pure) != (b in pure)):boundary[w]=b if a in pure else a
  assert len(pure_gates)+len(boundary)>=si.bit_count()
  assert set(charged)<=cone
  assert not(set(charged)&(pure_gates|set(boundary)))
  # Redirect by original topological index. This handles B_j depending on q_k.
  remap={v:11 if si>>v&1 else v for v in range(11)}|{11:11,12:12}
  new=[];deleted=[]
  for g,(op,a,b) in enumerate(gates):
   w=13+g
   if w not in cone:continue
   if w in pure_gates:remap[w]=11;deleted.append(w)
   elif w in boundary:remap[w]=remap[boundary[w]];deleted.append(w)
   elif w in charged:remap[w]=remap[charged[w]];deleted.append(w)
   else:new.append((op,remap[a],remap[b]));remap[w]=12+len(new)
  assert len(new)<=len(cone)-si.bit_count()-len(charged)
  rows=[x for x in range(2048) if not x&si and (not F(x) or x in EM)]
  comparisons=0
  for x in rows:
   nv=evaluate(new,x)
   for w in cone:
    assert nv[remap[w]]==values[x][w],(tri,mode,x,w)
    comparisons+=1
  for x in range(2048):
   if x&si:continue
   nv=evaluate(new,x)
   if not F(x):assert all(not nv[13+g] for g,(op,a,b) in enumerate(new) if op=='and')
  controls.append(dict(triangle=tri,mode=mode,original_gates=len(gates),cone_gates=len(cone),pure_OR_deletions=len(pure_gates),boundary_OR_deletions=len(boundary),charged_ANDs=charged,reduced_gates=len(new),boundary_rows=len(rows),all_wire_boundary_comparisons=comparisons,overlapping_charged_cones=True,gates=gates,output=output,remap=remap,reduced_circuit=new))
result=dict(verdict='PASS_MATHEMATICAL_REVIEW_AND_BOUNDED_CONTROLS',source_sha256=sha(__file__),reviewed_math_sha256=sha(ROOT/'orch/S01/joint-factor-cost.md'),families=families,truth_identity_rows=4096,actual_DAG_controls=controls,boundary_wire_comparisons=sum(c['all_wire_boundary_comparisons'] for c in controls),solver_run=False,Lean_proof=False,scope='Stated minimal productive clean full-cover factor families only; not global AAAA exhaustion or a CNF UNSAT certificate.')
(OUT/'joint-factor-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['verdict','source_sha256','reviewed_math_sha256','truth_identity_rows','boundary_wire_comparisons']}))
print('joint bounds:',[(f['triangle'],f['joint_bound']) for f in families])
print('eight overlapping-cone DAG controls PASS; exact full circuits and redirects retained in JSON')
