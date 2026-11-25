#!/usr/bin/env python3
import concurrent.futures,json,pathlib,subprocess,sys
base=pathlib.Path('/workspace/pequalnp-proofs/results/orch9775/search');tmp=pathlib.Path('/tmp/oec/pequalnp-pilot-103/orch9775')
o=json.loads((base/'compact-orbits.json').read_text())['orbits'];r=json.loads((base.parent/'projection/validated-exclusions.json').read_text())['remaining']
selected=[int(m) for m,ms in o.items() if int(m)!=127 and any(x in r for x in ms)]
jobs=[(tmp/'compact-trim2'/f'case-{m}',tmp/'compact-minimal'/f'case-{m}') for m in selected]
jobs +=[(tmp/f'weak-{m}',tmp/'compact-minimal'/f'weak-{m}') for m in [1290,8488]]
jobs +=[(tmp/f'paired-{m}',tmp/'compact-minimal'/f'paired-{m}') for m in [127,4757,16256]]
def run(job):
 src,out=job
 cp=subprocess.run([sys.executable,str(base/'compact_minimize.py'),str(src),str(out)],capture_output=True,text=True)
 out.with_suffix('.driver.stdout').write_text(cp.stdout);out.with_suffix('.driver.stderr').write_text(cp.stderr)
 assert cp.returncode==0,(src,cp.stderr)
 return json.loads(cp.stdout)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for rr in ex.map(run,jobs):print(json.dumps(rr),flush=True)
