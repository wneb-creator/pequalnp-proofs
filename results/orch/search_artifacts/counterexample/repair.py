import importlib.util
import json
import random
import subprocess
from pathlib import Path

P=Path('/tmp/oec/pequalnp-pilot-99/counterexample')
spec=importlib.util.spec_from_file_location('synth',P/'synth.py');s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
lines=(P/'search.log').read_text().splitlines();last=max(i for i,l in enumerate(lines) if l.startswith('BEST'))
seed=[]
for line in lines[last+1:last+20]:
    _,op,a,b=line.split();a=int(a);b=int(b);op='&|!'.index(op)
    if op==2:b=a
    else:a,b=sorted((a,b))
    seed.append((op,a,b))
assert len(seed)==19
rng=random.Random(2592)
for trial in range(24):
    free={i for i,g in enumerate(seed) if g[0]==2}
    free.update(rng.sample(range(19),8+trial%3))
    fix={i:g for i,g in enumerate(seed) if i not in free}
    rows=sorted(set([x for x in range(1024) if not s.target(x)]+[(1<<a)|(1<<b) for a,b in s.EDGES]))
    for it in range(5):
        prefix=P/f'repair-{trial}-{it}'
        f,ts,aa,bb=s.encode(rows,1,None,fix);f.save(prefix.with_suffix('.cnf'))
        prefix.with_suffix('.meta.json').write_text(json.dumps({'free':sorted(free),'fix':fix,'rows':rows,'typ':ts,'a':aa,'b':bb}))
        with prefix.with_suffix('.stdout').open('w') as out,prefix.with_suffix('.stderr').open('w') as err:
            r=subprocess.run([s.SOLVER,'--sat','-t','10',str(prefix.with_suffix('.cnf'))],stdout=out,stderr=err)
        print(trial,it,'free',sorted(free),'exit',r.returncode,flush=True)
        if r.returncode!=10:break
        model=set()
        for line in prefix.with_suffix('.stdout').read_text().splitlines():
            if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
        gs=[tuple(next(j for j,v in enumerate(vs) if v in model) for vs in (ts[i],aa[i],bb[i])) for i in range(19)]
        bad=[x for x in range(1024) if s.evaluate(gs,x)!=s.target(x)]
        prefix.with_suffix('.circuit.json').write_text(json.dumps({'gates':gs,'bad':bad},indent=2))
        print('model mismatches',len(bad),flush=True)
        if not bad:print('VERIFIED 19 GATE COUNTEREXAMPLE',flush=True);raise SystemExit
        rows=sorted(set(rows+bad))
