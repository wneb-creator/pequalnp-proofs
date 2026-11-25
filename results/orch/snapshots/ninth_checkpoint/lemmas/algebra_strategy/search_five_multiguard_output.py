"""Bounded OR-clause output guards; heuristic candidate search, not a lower bound."""
import itertools,json,time
from pathlib import Path
from assemble_five_owner import assemble_five
HERE=Path(__file__).resolve().parent
case=json.loads((HERE/'five-owner-joint-packet.json').read_text())[0]
seeds=json.loads((HERE.parent/'circuit_search'/'joint-five-multiguard-seeds.json').read_text())
n=case['inputs'];tests=case['raw_tests'];P=sum(1<<i for i,(m,y) in enumerate(tests) if y)
features=case['features']
base=[]
for j in range(case['raw_inputs']):base.append(sum(1<<i for i,(m,y) in enumerate(tests) if m>>j&1))
for feature in features:base.append(sum(1<<i for i,(m,y) in enumerate(tests) if any(m>>j&1 for j in feature['raw_indices'])))
reports=[];witnesses=[]
for index,seed in enumerate(seeds):
 budget=23-seed['assembly']['core_gates']-seed['assembly']['prefix_extra_cost']
 if budget<4:continue
 start=time.monotonic();values=base[:]
 for op,a,b in seed['gates']:values.append(values[a]|values[b] if op else values[a]&values[b])
 bad=values[-1]&~P
 # Deduplicate sources; unused alternative feature encodings may have different outside costs.
 # This is a search heuristic and never claims exhaustive budget infeasibility.
 sources={}
 for wire,v in enumerate(values):
  if v&P:sources.setdefault((v&P,v&bad),wire)
 sources=[(p,b,w) for (p,b),w in sources.items()]
 clauses={};enumerated=0
 for cost in range(1,budget+1):
  for chosen in itertools.combinations(sources,cost):
   enumerated+=1;pos=0;neg=0
   for p,b,w in chosen:pos|=p;neg|=b
   if pos!=P:continue
   rejected=bad&~neg
   if not rejected:continue
   if rejected not in clauses:clauses[rejected]=(cost,tuple(x[2] for x in chosen))
 # Dynamic programming over unions of rejected current-error negatives.
 bycost=[[] for _ in range(budget+1)]
 for reject,(cost,wires) in clauses.items():bycost[cost].append((reject,wires))
 dp=[{} for _ in range(budget+1)];dp[0][0]=[]
 for total in range(1,budget+1):
  for c in range(1,total+1):
   for before,chosen in dp[total-c].items():
    for rejected,wires in bycost[c]:
     union=before|rejected
     if union not in dp[total]:dp[total][union]=chosen+[wires]
  if bad in dp[total]:
   gates=[list(g) for g in seed['gates']];out=n+len(gates)-1
   for wires in dp[total][bad]:
    guard=wires[0]
    for wire in wires[1:]:gates.append([1,guard,wire]);guard=n+len(gates)-1
    gates.append([0,out,guard]);out=n+len(gates)-1
   full,metadata=assemble_five(case,gates,out)
   witnesses.append(dict(seed_index=index,guards=dp[total][bad],gates=gates,output=out,assembly=metadata))
   break
 report=dict(seed_index=index,budget=budget,sources=len(sources),clauses_enumerated=enumerated,distinct_rejection_masks=len(clauses),dp_states=sum(map(len,dp)),found=any(w['seed_index']==index for w in witnesses),elapsed_seconds=time.monotonic()-start)
 reports.append(report);print(json.dumps(report),flush=True)
report=dict(scope='Bounded output AND of pure OR clauses from existing wires/available features. Deduplicates equivalent source signatures and keeps one minimum-cost clause per rejected subset; no general impossibility or exhaustive prefix-cost claim.',results=reports,witnesses=witnesses)
(HERE/'five-multiguard-output-guard-search.json').write_text(json.dumps(report,indent=2)+'\n')
