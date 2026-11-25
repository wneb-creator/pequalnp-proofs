import json
from pathlib import Path
from itertools import combinations
base=Path('/tmp/oec/pequalnp-pilot-152/gap-3754')
answers=[]
for name,budget in [('cycle8',11),('cycle10',14),('cycleleaf',9),('cycletwoleaf',11),('cycletail2',11),('theta333',12),('theta244',13)]:
 spec=json.loads(base.joinpath(name+'.json').read_text());n=spec['n'];edges=[tuple(e) for e in spec['edges']]
 def stats(es):
  def target(x):return any(x>>a&1 and x>>b&1 for a,b in es)
  zs=[x for x in range(1<<n) if not target(x) and all(x>>i&1 or target(x|(1<<i)) for i in range(n))]
  pseudoforest=all(sum(bool(x>>a&1 and x>>b&1) for a,b in es)<=x.bit_count() for x in range(1<<n))
  and_floor=(len(zs)-1).bit_length();or_floor=max(0,len(es)-1) if pseudoforest else None
  return dict(edges=es,maximal_false_count=len(zs),maximal_false_masks=zs,pseudoforest=pseudoforest,conditional_AND_floor=and_floor,conditional_OR_floor=or_floor,conditional_total_floor=and_floor+or_floor if or_floor is not None else None)
 whole=stats(edges);cofactors=[stats([e for e in edges if v not in e]) for v in range(n)]
 caps=[budget-r['conditional_total_floor'] if r['conditional_total_floor'] is not None else None for r in cofactors]
 cover=next(S for k in range(n+1) for S in combinations(range(n),k) if all(a in S or b in S for a,b in edges))
 answers.append(dict(name=name,n=n,budget=budget,standard_clean_upper=len(edges)+len(cover)-1,whole=whole,cofactors=cofactors,conditional_raw_reader_caps=caps))
print(json.dumps(answers,indent=2))
