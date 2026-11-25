#!/usr/bin/env python3
import json,pathlib,subprocess,sys
from compact_certificate import core,emit
base=pathlib.Path('/workspace/pequalnp-proofs/results/orch9775/search')
scratch=pathlib.Path('/tmp/oec/pequalnp-pilot-103/orch9775')
orbits=json.loads((base/'compact-orbits.json').read_text())['orbits']
summary=[]
for text in orbits:
 m=int(text)
 if m==127:continue
 src=scratch/'compact-batch'/f'case-{m}'
 for t in range(2):
  dst=scratch/f'compact-trim{t+1}'/f'case-{m}'
  p=subprocess.run([sys.executable,str(base/'compact_trim.py'),str(src),str(dst)],capture_output=True,text=True)
  dst.with_suffix('.trim.stdout').write_text(p.stdout);dst.with_suffix('.trim.stderr').write_text(p.stderr)
  assert p.returncode==0,(m,p.stderr)
  src=dst
 d=core(src);out=base/'compact-certificates'/f'Case{m}'
 out.with_suffix('.json').write_text(json.dumps(d,separators=(',',':'))+'\n')
 out.with_suffix('.lean').write_text(emit(d,str(m)))
 r={'I':m,'k':d['k'],'base':d['base_count'],'learned':len(d['rows']),'facts':len(d['facts']),'bytes':out.with_suffix('.lean').stat().st_size,'source':str(src)}
 summary.append(r);print(json.dumps(r),flush=True)
 (base/'compact-certificates'/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
