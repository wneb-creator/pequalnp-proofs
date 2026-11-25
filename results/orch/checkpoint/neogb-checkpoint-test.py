import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import sympy as s

P=Path('/tmp/oec/pequalnp-pilot-79')
D=P/'neogb-run-checkpoint.py'
ENV={'PATH':'/usr/local/bin:/usr/bin:/bin','LANG':'C.UTF-8','OMP_NUM_THREADS':'2','OPENBLAS_NUM_THREADS':'1'}
spec=importlib.util.spec_from_file_location('cpdriver',D)
driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver)

def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 resource.setrlimit(resource.RLIMIT_AS,(2*2**30,2*2**30))
 resource.setrlimit(resource.RLIMIT_CPU,(30,30))

def run(label,source,*args,expect=0):
 out=P/(label+'.json'); log=P/(label+'.log'); snap=P/(label+'.gz')
 command=[sys.executable,str(D),'-f',str(source),'-o',str(out),'--checkpoint',str(snap),'--info','0','--max-pairs','1',*args]
 with log.open('wb') as f:
  result=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,env=ENV,preexec_fn=limits,timeout=45)
 assert result.returncode==expect,(label,result.returncode,log.read_text())
 return json.loads(out.read_text()) if result.returncode==0 else None,snap

def basis_normal(result):
 return sorted([sorted((tuple(t['exponents']),t['coefficient']) for t in p) for p in result['basis']])

x,y,z=s.symbols('x y z')
for prime in (97,257,65537):
 source=P/f'checkpoint-check-{prime}.msolve'
 source.write_text(f'x,y,z\n{prime}\nx^2+y^2+z^2-1,x*y-z,y*z-x,\n')
 gb=s.groebner([x*x+y*y+z*z-1,x*y-z,y*z-x],x,y,z,order='grevlex',modulus=prime)
 for elim in (0,1):
  tag=f'checkpoint-test-{prime}-e{elim}'
  baseline,_=run(tag+'-full',source,'--eliminate',str(elim))
  partial,snap=run(tag+'-partial',source,'--eliminate',str(elim),'--stop-after-rounds','1')
  assert partial['status']=='PARTIAL' and not partial['is_groebner_basis'] and 'unit_ideal' not in partial
  text=gzip.decompress(snap.read_bytes()).decode()
  lines=text.splitlines(); n=lines.index('x,y,z')
  for raw in ''.join(lines[n+2:]).split(','):
   if raw:
    expr=s.sympify(raw.replace('^','**'),locals={'x':x,'y':y,'z':z})
    assert gb.reduce(expr)[1]==0,(tag,expr)
  resumed,_=run(tag+'-resume',source,'--eliminate',str(elim),'--resume',str(snap))
  assert resumed['status']=='COMPLETE'
  assert basis_normal(baseline)==basis_normal(resumed),tag
  print(tag,'partial membership and resumed reduced basis equal baseline',flush=True)

source=P/'checkpoint-check-97.msolve'
periodic,snap=run('checkpoint-test-periodic',source,'--checkpoint-seconds','0.000000001','--la','44')
assert periodic['status']=='COMPLETE' and snap.exists() and Path(str(snap)+'.previous').exists()
print('periodic save continues and rotates previous',flush=True)
old=snap.read_bytes();oldprevious=Path(str(snap)+'.previous').read_bytes()
failed,_=run('checkpoint-test-cap',source,'--checkpoint',str(snap),'--checkpoint-seconds','0.000000001','--checkpoint-max-mib','0.00001')
assert failed['checkpoint_write_failed'] and failed['status']=='PARTIAL'
assert snap.read_bytes()==old and Path(str(snap)+'.previous').read_bytes()==oldprevious
assert not list(P.glob(snap.name+'.tmp.*'))
print('size-cap failure preserves latest and previous, removes temporary',flush=True)
other=P/'checkpoint-check-mismatch.msolve';other.write_text(source.read_text().replace('-1,','-2,'))
run('checkpoint-test-mismatch',other,'--resume',str(snap),expect=1)
print('original input hash mismatch rejected',flush=True)
unit=P/'checkpoint-check-unit.msolve';unit.write_text('x\n97\nx,x-1,\n')
complete,unit_snap=run('checkpoint-test-early-complete',unit,'--stop-after-rounds','1')
assert complete['status']=='COMPLETE' and complete['unit_ideal']
print('completion before stop remains complete',flush=True)
big=P/'checkpoint-test-big-prior.gz'
with big.open('wb') as f: f.truncate(16*2**20+1)
Path(str(big)+'.previous').write_bytes(b'old previous')
bigresult,_=run('checkpoint-test-big-prior-result',source,'--checkpoint',str(big),'--stop-after-rounds','1')
assert bigresult['status']=='PARTIAL' and not Path(str(big)+'.previous').exists()
assert gzip.decompress(big.read_bytes()).startswith(b'# PARTIAL ')
print('previous compressed snapshot retained only below 16MiB cap',flush=True)
subset,subset_snap=run('checkpoint-test-subset',source,'--stop-after-rounds','1','--checkpoint-max-mib',str(750/2**20))
assert subset['status']=='PARTIAL' and subset['checkpoint_progress_subset']
assert 0 < subset['checkpoint_generators_retained'] < subset['checkpoint_generators_total']
payload=gzip.decompress(subset_snap.read_bytes()).decode()
assert len(payload.encode())<=750 and payload.endswith(',\n')
subset_resume,_=run('checkpoint-test-subset-resume',source,'--resume',str(subset_snap))
baseline,_=run('checkpoint-test-subset-baseline',source)
assert basis_normal(subset_resume)==basis_normal(baseline)
print('whole-polynomial bounded subset resumes to identical baseline',flush=True)
print('ALL CHECKPOINT TESTS PASSED',flush=True)
