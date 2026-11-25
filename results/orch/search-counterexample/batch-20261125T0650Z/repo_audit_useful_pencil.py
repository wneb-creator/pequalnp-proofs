import hashlib
import itertools
import json
from pathlib import Path

B=Path('/tmp/oec/pequalnp-pilot-62')
d=json.loads((B/'multi-output-line-neighborhoods.json').read_text())
targets=[t['positive_mask'] for t in d['targets']]
negative=set()
for t in targets:
    rows=[q for q in d['negative_samples'] if not q&t]
    negative.update(q for q in rows if not any(q!=r and q&~r==0 for r in rows))
negative=sorted(negative)
selected=[13+i for i,q in enumerate(negative) if q.bit_count()==4 and not q&targets[0]]
assert len(selected)==54
assert all((negative[r-13]&targets[0])==0 and negative[r-13].bit_count()==4 for r in selected)
assert all(sum(q.bit_count()==4 and not q&t for q in negative)==54 for t in targets)
for m in [1,3,9]:
    moved={sum(1<<((m*i)%13) for i in range(13) if negative[r-13]>>i&1) for r in selected}
    assert moved=={negative[r-13] for r in selected}
estimate=json.loads((B/'multi-output-useful-pencil-estimate.json').read_text())
assert selected==estimate['point_zero_four_cap_rows']
assert estimate['useful_cut_additional_variables']==38
assert estimate['useful_cut_additional_clauses']==38*(54+1+1)==2128
assert estimate['estimated_new_variables']==745242+62+38==745342
assert estimate['estimated_new_clauses']==2722655+1181+2128==2725964
old=(B/'multi_output_exact_pencil_cnf.py').read_text();new=(B/'multi_output_useful_pencil_cnf.py').read_text()
assert old.split('for gate in range(args.or_count):',1)[1].split('if args.exact_pencil:',1)[0]==new.split('for gate in range(args.or_count):',1)[1].split('if args.exact_pencil:',1)[0]
assert old.split('actions = []',1)[1].split('cnf.finish()',1)[0]==new.split('actions = []',1)[1].split('cnf.finish()',1)[0]
out={'reviewer':'repo_audit','status':'PASS source-only useful-pencil cut and offsets; no full CNF generation, solver or Lean run','scope':'13-output canonical promise model only; adds actual rejection on at least one four-cap to exact singleton-support pencil. No whole-function exactness or posted51 conclusion.',
'mathematical_argument':'Restrict the indexed family to OR gates false on at least one four-cap. All separating false factors remain. If this family has no exact pencil, checked no-exact-target guard charging forces at least39 retained gates, contradicting at most38 total. Thus some retained gate has pencil support. Monotonicity forces every accepted singleton outside a false cap, so that cap is disjoint from the exact pencil. Simultaneous Singer translation sends the gate pencil toP0 and preserves the false four-cap. The zero-shift multiplier subgroup preservesP0 and its54 disjoint four-caps.',
'formal_status':'The set-family no-exact corollary is currently UNCOMPILED. Restriction to actual false gates, circuit-support transport and symmetry normalization are independently reviewed mathematical arguments, not claimed new Lean theorems.',
'checks':{'point_zero_cap_rows':selected,'selected_count':54,'positive_sample_offset':13,'all_pencils_cap_count':54,'added_variables_over_simple_cut':38,'added_clauses_over_simple_cut':2128,'estimated_total_variables':745342,'estimated_total_clauses':2725964},
'files':{n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in ['multi_output_useful_pencil_cnf.py','multi-output-useful-pencil-estimate.json','multi_output_exact_pencil_cnf.py']}}
(B/'useful-pencil-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
