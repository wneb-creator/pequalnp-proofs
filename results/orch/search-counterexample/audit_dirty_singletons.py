from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'global-first-or-symmetry.json').read_text())
known=json.loads((base/'multi-output-baseline39.json').read_text())
positive=data['positive_samples'];negative=data['negative_samples']
singleton_rows=[1<<i for i in range(26)]
assert all((a&b).bit_count()<=1 for a,b in combinations(positive,2))
coverage=[sum(bool(n&s) for n in negative) for s in singleton_rows]
assert set(coverage)=={126}
samples=positive+negative+singleton_rows+[0]
input_masks=[sum((p>>i&1)<<j for j,p in enumerate(positive)) for i in range(26)]
baseline=[];masks=input_masks.copy()
for a,b in known['ors']:
    pair=sorted((masks[a+13],masks[b+13]))
    baseline.append(pair);masks.append(pair[0]|pair[1])
acc=input_masks[0]
for p in range(1,13):
    baseline.append(sorted((acc,input_masks[p])));acc|=input_masks[p]
truths=[sum((q>>i&1)<<j for j,q in enumerate(samples)) for i in range(26)]
positive_mask=(1<<52)-1;full=(1<<len(samples))-1
for a,b in baseline:
    terms=[]
    for sig in (a,b):
        chosen=[i for i,w in enumerate(truths) if w&sig==sig]
        assert chosen
        value=full
        for i in chosen:value&=truths[i]
        assert value&positive_mask==sig
        terms.append(value)
    truths.append(terms[0]|terms[1])
output=full
for value in truths:
    if value&positive_mask==positive_mask:output&=value
assert output==positive_mask
singleton_bits=((1<<26)-1)<<520
dirty_counts=[(w&singleton_bits).bit_count() for w in truths[26:]]
assert sum(dirty_counts)>0
assert not any(w>>(len(samples)-1)&1 for w in truths)
bounds=[]
for n in singleton_rows:
    sensitive=[i for i in range(26) if not n>>i&1 and any(p&(n|(1<<i))==p for p in positive)]
    bounds.append(len(sensitive)-1)
assert set(bounds)=={3}
result={
    'status':'Singleton-cut premise checks and51-baseline replay passed.',
    'source_sha256':sha256((base/'global_or_direct_cnf_v3.py').read_bytes()).hexdigest(),
    'all_distinct_positive_meets_have_at_most_one_coordinate':True,
    'singleton_generic_row_coverage_histogram':dict(Counter(coverage)),
    'baseline_positive_checks':52,'baseline_generic_negative_checks':468,
    'baseline_singleton_negative_checks':26,'baseline_empty_negative_checks':1,
    'baseline_ORs_true_on_some_singleton':sum(bool(x) for x in dirty_counts),
    'baseline_total_OR_singleton_true_entries':sum(dirty_counts),
    'baseline_dirty_OR_signature_size_histogram':dict(Counter(dirty_counts)),
    'new_singleton_false_OR_bounds':dict(Counter(bounds)),
    'scope':'Redundant cut for at most50 ORs, justified by the checked CleanOrGeneral lemma; finite replay is not a new Lean proof.',
}
print(json.dumps(result,indent=2))
(base/'dirty-singletons-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
