import itertools,json
from pathlib import Path

r=Path('/workspace/pequalnp-proofs/results/orch1884/search')
E=[(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(4,6),(6,8),(8,5),(5,7),(7,4)]
positive=[(1<<a)|(1<<b)for a,b in E]
negative=[25,52,58,69,100,104,138,201,274,277,385,386]
rows=sorted(positive+negative)
PM=sum(1<<i for i,x in enumerate(rows)if x in positive)
NM=sum(1<<i for i,x in enumerate(rows)if x in negative)
BM=sum(1<<i for i,x in enumerate(rows)if x in negative and x not in[100,386])
U=1<<rows.index(386)
base=[sum(1<<i for i,x in enumerate(rows)if x>>v&1)for v in range(9)]
pairs=[(a,b)for a,b in itertools.combinations(range(9),2)if (base[a]|base[b])&U]
def fresh_minimal(v,earlier):
    return v&PM and all((v&PM)!=(w&PM) or (w&NM)&~v for w in earlier)

tested=0;valid=[];functions=set()
for clauses in itertools.combinations(pairs,3):
    ors=[base[a]|base[b]for a,b in clauses]
    h=ors[0]&ors[1]&ors[2]
    if not(h&U)or h&BM or not(h&PM):continue
    for pair in [(0,1),(0,2),(1,2)]:
        tested+=1
        other=next(i for i in range(3)if i not in pair)
        gates=[[1,a,b]for a,b in clauses]+[[0,9+pair[0],9+pair[1]],[0,12,9+other]]
        values=base.copy();ok=True
        for op,a,b in gates:
            v=(values[a]|values[b])if op else(values[a]&values[b])
            if not fresh_minimal(v,values):ok=False;break
            values.append(v)
        if not ok:continue
        bad=[];badpairs=[];edgehits=[]
        for x in range(512):
            w=[bool(x>>v&1)for v in range(9)]
            for op,a,b in gates:w.append((w[a]or w[b])if op else(w[a]and w[b]))
            f=any(x>>a&1 and x>>b&1 for a,b in E)
            if w[-1]and x&25 and not f:bad.append(x)
            if w[-1]and x.bit_count()<=2 and not f:badpairs.append(x)
            if w[-1]and x in positive:edgehits.append(x)
        assert not bad and not badpairs
        if h not in functions:
            functions.add(h);valid.append({'gates':gates,'edge_rows':edgehits,'truth_signature':h,
                                           'full_rows_checked':512,'bad_auxiliary_rows':bad})
report={'family':'Three raw two-input OR clauses followed by two AND gates; five total gates',
        'candidate_OR_pairs':len(pairs),'families_passing_H_profile_before_bypass_checks':tested,
        'all_gates_edge_productive':True,'earlier_wire_positive_profile_bypass_forbidden':True,
        'valid_distinct_H_functions':len(valid),'witnesses':valid,
        'general_five_gate_exclusion_proved':False}
(r/'h5-cnf-family-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k!='witnesses'}))
