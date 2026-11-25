import itertools,json,pathlib,sys,time
HERE=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"circuit_search"))
from generate_full_guard_seeds import Builder
case=json.loads((HERE/"k9_arc_4_8_10_12.json").read_text())
base_seeds=json.loads((HERE/"k9-multiguard-seeds.json").read_text())
neighbors=[{b for a,b in case["edges"]if a==p}for p in range(9)]
tests=case["tests"]
sigs=[sum(((m>>i)&1)<<j for j,(m,_)in enumerate(tests))for i in range(22)]
pos=(1<<36)-1;neg=((1<<len(tests))-1)^pos
start=time.monotonic();checked=0;found=[];seen=set();best=10000;stop=False
for seed in base_seeds:
 if seed["size"]>40:continue
 group=tuple(seed["group"]);U=set().union(*(neighbors[p]for p in group))
 base_order=list(seed["guarded"])
 if seed["mode"]%2:base_order.reverse()
 initial=[set(group)-{p}for p in base_order]
 extras=[]
 for k in range(1,len(group)):
  for A in itertools.combinations(group,k):
   A=set(A);B=set(group)-A
   if A in initial or len(B)==1:continue
   if set().union(*(neighbors[p]for p in B))==U:continue
   extras.append(A)
 counts=[1,2]if seed["size"]==39 else[1]
 for count in counts:
  for extra in itertools.combinations(extras,count):
   for before in[False,True]:
    checked+=1
    if time.monotonic()-start>30:stop=True;break
    builder=Builder(inputs=22)
    remaining=[p for p in range(9)if p not in group]
    if seed["mode"]%2:remaining.reverse()
    if seed["mode"]>=2:
     for p in remaining:builder.union(neighbors[p])
    guardsets=list(extra)+initial if before else initial+list(extra)
    guards=[]
    for A in guardsets:
     B=set(group)-A
     guards.append(builder.gate(1,builder.union(A),builder.union(set().union(*(neighbors[p]for p in B)))))
    merged=builder.gate(0,builder.union(group),builder.union(U))
    for guard in guards:merged=builder.gate(0,merged,guard)
    terms=[merged]+[builder.gate(0,p,builder.union(neighbors[p]))for p in remaining]
    output=terms[0]
    for term in terms[1:]:output=builder.gate(1,output,term)
    gates=builder.compact(output)
    if len(gates)>43:continue
    values=sigs.copy()
    for op,a,b in gates:values.append(values[a]|values[b]if op else values[a]&values[b])
    result=values[-1];assert result&pos==pos
    bad=(result&neg).bit_count()
    key=tuple(map(tuple,gates))
    if key in seen:continue
    seen.add(key)
    found.append({"group":list(group),"guard_A_sets":[sorted(A)for A in guardsets],"gates":gates,"output":21+len(gates),"size":len(gates),"maximal_negative_errors":bad})
    if bad<best:
     best=bad;print("BEST",bad,"gates",len(gates),"guards",len(guardsets),"group",group,flush=True)
   if stop:break
  if stop:break
 if stop:break
(HERE/"k9-partition-multiguard-seeds.json").write_text(json.dumps(found))
print(json.dumps({"checked":checked,"elapsed_seconds":time.monotonic()-start,"stopped":stop,"seeds":len(found),"best_errors":best if found else None}),flush=True)
