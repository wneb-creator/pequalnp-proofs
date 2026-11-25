from pathlib import Path
import json
p=Path(__file__).resolve().parents[1]/'status_review/punctured-four-arc.json'
c=json.loads(p.read_text());private=[5,9,10,11]
keep=[i for i in range(c['raw_inputs']) if i not in private];rename={v:i for i,v in enumerate(keep)}
features=[];maps=[]
for support in [[i] for i in range(c['raw_inputs'])]+c['features']:
    out=sorted(rename[v] for v in support if v in rename)
    if len(out)==0: maps.append(None)
    elif len(out)==1: maps.append(out[0])
    else:
        if out not in features: features.append(out)
        maps.append(len(keep)+features.index(out))
edges=[[rename[u],rename[v]] for u,v in c['edges'] if u in rename and v in rename]
n=len(keep); em=[(1<<u)|(1<<v) for u,v in edges];fm=[sum(1<<v for v in x) for x in features]
value=lambda x:any(x&m==m for m in em)
encode=lambda x:sum(bool(x&m)<<i for i,m in enumerate(fm))
negative=[x for x in range(1<<n) if not value(x) and all(value(x|1<<i) for i in range(n) if not x>>i&1)]
pivotal=[]
for i in range(n):
    matches=[x for x in range(1<<n) if not x>>i&1 and not value(x) and value(x|1<<i) and encode(x)==encode(x|1<<i)]
    assert matches
    pivotal.append({'raw':i,'low':matches[0],'high':matches[0]|1<<i})
assert n==9 and len(features)==3 and len(edges)==10
stages=[]
deleted=set()
old_edge_masks=[(1<<u)|(1<<v) for u,v in c['edges']]
old_value=lambda x:any(x&e==e for e in old_edge_masks)
for variable in private:
    residual_supports=sorted(set(tuple(i for i in s if i not in deleted) for s in c['features']))
    retained=[s for s in residual_supports if len(s)>=2]
    support_masks=[sum(1<<i for i in s) for s in retained]
    enc=lambda x:sum(bool(x&s)<<j for j,s in enumerate(support_masks))
    forbidden=sum(1<<i for i in deleted)
    matches=[x for x in range(1<<c['raw_inputs']) if not x&forbidden and not x>>variable&1 and not old_value(x) and old_value(x|1<<variable) and enc(x)==enc(x|1<<variable)]
    assert matches
    stages.append({'deleted_before':sorted(deleted),'eliminate':variable,'normalized_nontrivial_features':[list(s) for s in retained],'pivotal_low':matches[0],'pivotal_high':matches[0]|1<<variable})
    deleted.add(variable)

out={'scope':'Computational zero-private specialization; four-gate-saving implication is plausible via encoded elimination but not formalized here, and kernel solution does not automatically restore original core.',
'sequential_normalized_pivotal_stages':stages,'raw_inputs':n,'available_inputs':n+len(features),'raw_map':[c['raw_map'][i] for i in keep],
'private_old_raw':private,'private_full':[c['raw_map'][i] for i in private],
'edges':edges,'features':features,'old_input_map':maps,'proposed_necessary_target':11,
'maximal_negatives':negative,'raw_tests':[[m,True] for m in em]+[[m,False] for m in negative],
'raw_pivotal_witnesses':pivotal,'mandatory_raw_reads':n}
Path(__file__).with_name('punctured-four-kernel.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['raw_tests','old_input_map','raw_pivotal_witnesses']},indent=2))
