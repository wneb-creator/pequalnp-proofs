import itertools,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
case=json.loads((HERE/"k9_arc_4_8_10_12.json").read_text())
seeds=json.loads((HERE/"k9-multiguard-seeds.json").read_text())+json.loads((HERE/"k9-partition-multiguard-seeds.json").read_text())
pairs=[(p,l)for p in range(9)for l in range(9,22)]
masks=[(1<<p)|(1<<l)for p,l in pairs]
triple_start=len(masks)
masks +=[(1<<p)|(1<<q)|(1<<l)for p,q in itertools.combinations(range(9),2)for l in range(9,22)]
masks +=[m for m,_ in case["tests"]]
sigs=[sum(bool(m>>i&1)<<j for j,m in enumerate(masks))for i in range(22)]
triple_mask=((1<<(triple_start+468))-1)^((1<<triple_start)-1)
unique={};counts={2:0,3:0,4:0};cubic_all=[]
for seed in seeds:
 vals=sigs.copy()
 for op,a,b in seed["gates"]:vals.append(vals[a]|vals[b]if op else vals[a]&vals[b])
 result=vals[-1]
 quadratic=0
 for k,(p,l)in enumerate(pairs):
  if result>>k&1:quadratic|=sigs[p]&sigs[l]
 higher=result&~quadratic&triple_mask
 if not higher:continue
 count=len(seed.get("guarded",seed.get("guard_A_sets",[])))
 counts[count]+=1
 witness_index=(higher&-higher).bit_length()-1
 seed=dict(seed)
 seed["genuine_cubic_witness"]=[i for i in range(22)if masks[witness_index]>>i&1]
 seed["added_quadratic_terms"]=sum(bool(result>>k&1)for k in range(len(pairs)))-36
 cubic_all.append(seed)
 score=(seed["maximal_negative_errors"],seed["size"])
 if result not in unique or score<(unique[result]["maximal_negative_errors"],unique[result]["size"]):unique[result]=seed
values=list(unique.values())
selected=[];seen=set()
for order in [sorted(values,key=lambda s:(s["maximal_negative_errors"],s["size"])),sorted(values,key=lambda s:(s["size"],s["maximal_negative_errors"])), sorted([s for s in values if len(s.get("guarded",s.get("guard_A_sets",[])))>=3],key=lambda s:(s["maximal_negative_errors"],s["size"]))[:32]]:
 for seed in order[:64]:
  key=tuple(map(tuple,seed["gates"]))
  if key not in seen:seen.add(key);selected.append(seed)
third_added=0
for seed in sorted([s for s in cubic_all if len(s.get("guarded",s.get("guard_A_sets",[])))>=3],key=lambda s:(s["maximal_negative_errors"],s["size"])):
 key=tuple(map(tuple,seed["gates"]))
 if key not in seen:
  seen.add(key);selected.append(seed);third_added+=1
 if third_added==32:break
(HERE/"k9-genuine-guard-seeds.json").write_text(json.dumps(selected))
summary={"cubic_seed_counts_by_guard_count":counts,"distinct_cubic_test_signatures":len(values),"selected":len(selected),"minimum_errors":min((s["maximal_negative_errors"]for s in selected),default=None),"minimum_gates":min((s["size"]for s in selected),default=None)}
(HERE/"k9-genuine-guard-summary.json").write_text(json.dumps(summary,indent=2))
print(json.dumps(summary))
