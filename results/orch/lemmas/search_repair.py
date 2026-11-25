import importlib.util
import random
import sys
from pathlib import Path

spec=importlib.util.spec_from_file_location('search_smt','results/orch/lemmas/search_smt.py')
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
source=sys.argv[1] if len(sys.argv)>1 else '/tmp/oec/pequalnp-pilot-107/counterexample-search.stdout'
a=Path(source).read_text().splitlines()
pos=[i for i,l in enumerate(a) if l.startswith('score')][-1]
c=[tuple(map(int,l.split()[1:])) for l in a[pos+1:pos+20]]
rng=random.Random(107)
for iteration in range(100):
    free={j for j,(op,_,_) in enumerate(c) if op==2}|{18}
    free.update(rng.sample([j for j in range(19) if j not in free],5))
    fixed={j:c[j] for j in range(19) if j not in free}
    print('REPAIR',iteration,'free',sorted(free),flush=True)
    found=m.synthesize(5,None,fixed)
    if found:
        print('FOUND REPAIR',found,flush=True)
        sys.exit(0)
