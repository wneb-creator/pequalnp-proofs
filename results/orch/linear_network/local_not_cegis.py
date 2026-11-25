import importlib.util,json,subprocess,random
from pathlib import Path
spec=importlib.util.spec_from_file_location('syn','/tmp/oec/pequalnp-pilot-85/counterexample/synthesize.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base=Path('/tmp/oec/pequalnp-pilot-85/linear_network/local-not-sat');base.mkdir(exist_ok=True)
fixed=json.loads(Path('/tmp/oec/pequalnp-pilot-85/counterexample/best.json').read_text())['gates']
unlocked={0,1,13,14,15,16,17,22,23}
samples={x for x in range(1<<14) if x.bit_count()<=2}
samples.update(json.loads(Path('/tmp/oec/pequalnp-pilot-85/linear_network/maximal-negative.json').read_text()))
solver='/tmp/oec/pequalnp-pilot-85/sat-tool/cadical-rel-3.1.0/build/cadical'
rng=random.Random(9811)
for r in range(10):
 c,schema=m.make(sorted(samples),24,fixed,unlocked)
 c.add(*(schema[0][j][2] for j in sorted(unlocked)))
 p=base/f'round-{r:03d}.cnf';c.write(p)
 (base/f'round-{r:03d}-samples.json').write_text(json.dumps(sorted(samples)))
 (base/f'round-{r:03d}-schema.json').write_text(json.dumps(schema))
 print('round',r,'samples',len(samples),'vars',c.n,'clauses',len(c.clauses),flush=True)
 del c
 log=base/f'round-{r:03d}.solver.log'
 with log.open('w') as f:q=subprocess.run([solver,'-t','120',str(p)],stdout=f,stderr=subprocess.STDOUT)
 print('exit',q.returncode,flush=True)
 if q.returncode!=10:break
 model={int(v) for s in log.read_text().splitlines() if s.startswith('v ') for v in s[2:].split() if int(v)>0}
 gs=m.decode(model,schema);delta=m.evaluate(gs)
 errors=[x for x in range(1<<14) if delta>>x&1]
 assert not samples.intersection(errors)
 result={'gates':gs,'errors':len(errors)}
 (base/f'round-{r:03d}-candidate.json').write_text(json.dumps(result))
 print('errors',len(errors),flush=True)
 if not errors:(base/'FOUND.json').write_text(json.dumps(result));break
 samples.update(errors[:32]);samples.update(rng.sample(errors,min(32,len(errors))))
