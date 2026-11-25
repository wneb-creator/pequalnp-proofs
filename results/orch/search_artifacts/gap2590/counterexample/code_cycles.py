from pathlib import Path
import json
from encode import EDGES

P=Path(__file__).resolve().parent
edge_set={tuple(sorted(e)) for e in EDGES}
cycles=[[0,2,4,1,3],[5,9,8,7,6]]
codes={}
for t,cycle in enumerate(cycles):
    for i,v in enumerate(cycle):codes[v]={5*t+i,5*t+(i+1)%5}
assert all(not codes[x].issubset(codes[a]|codes[b]) for x in range(10) for a in range(10) for b in range(a,10) if x!=a and x!=b and tuple(sorted((a,b))) not in edge_set)

def matchings(xs):
    if not xs:yield [];return
    a=xs[0]
    for j in range(1,len(xs)):
        b=xs[j]
        for rest in matchings(xs[1:j]+xs[j+1:]):yield [(a,b)]+rest

records=[];best=0;total=0;admissible=0
for pairs in matchings(list(range(10))):
    total+=1;opp={a:b for a,b in pairs}|{b:a for a,b in pairs}
    if any(any(opp[e] in code for e in code) for code in codes.values()):continue
    admissible+=1
    covered=[list(e) for e in EDGES if any(opp[a] in codes[e[1]] for a in codes[e[0]])]
    if len(covered)>best:best=len(covered);records=[]
    if len(covered)==best:records.append({'pairs':pairs,'covered':covered})
result={'codes':{str(k):sorted(v) for k,v in codes.items()},'matchings':total,'admissible':admissible,'maximum_covered_Petersen_edges':best,'best_models':records}
(P/'code_cycles.json').write_text(json.dumps(result,indent=2)+'\n')
print('Two-C5 codes: matchings',total,'admissible',admissible,'maximum edge coverage',best,'of15','maximizers',len(records))
