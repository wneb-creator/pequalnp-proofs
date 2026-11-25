from pathlib import Path
from itertools import combinations
import json, hashlib, sys
base=Path(sys.argv[1])
N=[{7,8,10},{7,9,13},{8,12,13},{7,11,12},{10,11,13},{9,10,12},{8,9,11}]
N += [{p for p in range(7) if t in N[p]} for t in range(7,14)]
results=[]
for name in ["stochastic-p13-residual-one.json","stochastic-p12-same-residual-two.json","stochastic-p12-mixed-residual-two.json"]:
    raw=(base/name).read_bytes();report=json.loads(raw);I=set(report['ineligible']);E=set(range(14))-I;units=report['units'];checked=0;all_subsets=0
    for row in report['first_survivors']:
        residual=[{j for j in range(units) if row['r'][t]>>j&1} for t in range(14)]
        supports=[{t for t in E if j in residual[t]} for j in range(units)]
        assert all(supports)
        assigned={i:set(N[i]) for i in I}
        while True:
            shared=supports+list(assigned.values())
            nxt={i:assigned[i]|{t for x in N[i] for t in E if residual[x]<=residual[t] and any(x in s and t in s for s in shared)} for i in I}
            if nxt==assigned:break
            assigned=nxt
        assert [sum(1<<t for t in assigned[i]) for i in report['ineligible']]==row['assigned_bitmasks']
        assert all(sum(t in assigned[i] for i in I)+int(bool(N[t]&E))<=2+len(residual[t]) for t in E)
        oldmax=newmax=0
        for c in E:
            permitted={x for x in E-{c} if residual[x]<=residual[c] and any(x in s and c in s for s in shared)}
            for count in range(len(permitted)+1):
                for tup in combinations(sorted(permitted),count):
                    X=set(tup);all_subsets+=1
                    free=({*range(7,14)} if c<7 else {*range(7)})-N[c]
                    free &= E-X
                    cost=len(residual[c])+len(X)
                    oldmax=max(oldmax,cost+(8 if free else 7))
                    newmax=max(newmax,cost+(9 if len(free)>=3 else 8 if free else 7))
        assert oldmax==row['max_old_score'] and newmax==row['max_new_score'] and newmax<=14
        checked+=1
    results.append({'file':name,'sha256':hashlib.sha256(raw).hexdigest(),'verified_examples':checked,'all_X_subsets_checked':all_subsets,'complete_enumeration':report['counts_enumerated_nonempty_budget_oldcut_newcut'][0]==report['full_state_count']})
output={'scope':'Independent set-based verification of abstract residual states, closure, budgets and every permissible X subset. Prospective +9 cofactor wrapper remains separate and these are not circuits.','results':results}
Path(sys.argv[2]).write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(results))
