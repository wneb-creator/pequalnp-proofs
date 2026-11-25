import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parent
WORKER=ROOT.parent/'worker.py'
FAKE_LAKE=r'''#!/usr/bin/env python3
import json,os,signal,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parent
cfg=json.loads((root/'fake-settings.json').read_text())
def event(role):
 with (root/'events.jsonl').open('a') as f:f.write(json.dumps({'role':role,'pid':os.getpid()})+'\n')
if cfg.get('ignore_term'):signal.signal(signal.SIGTERM,signal.SIG_IGN)
event('lake-start')
(root/'lake-pid').write_text(str(os.getpid()))
if cfg.get('stall_before_helper'):time.sleep(cfg['stall_before_helper'])
(root/'lake-argv.json').write_text(json.dumps(sys.argv[1:]))
if cfg.get('forward_only'):sys.exit(cfg.get('lake_exit',37))
if cfg.get('early_failure'):sys.exit(cfg['early_failure'])
assert sys.argv[1]=='env'
p=subprocess.Popen(sys.argv[2:])
status=p.wait()
event('helper-exited')
time.sleep(cfg.get('lake_delay',0))
event('lake-exit')
sys.exit(cfg.get('lake_exit',status))
'''
FAKE=r'''#!/usr/bin/env python3
import json,os,signal,sys,time
from pathlib import Path
role=sys.argv[1];root=Path(sys.argv[2]);mode=sys.argv[3]
with (root/'events.jsonl').open('a') as f:
 f.write(json.dumps({'role':role,'args':sys.argv[3:],'pid':os.getpid(),'cwd':os.getcwd()})+'\n')
if role=='enter':
 lakepid=int((root/'lake-pid').read_text())
 if Path(f'/proc/{lakepid}').exists():
  print('Lake is still resident at storage enter',file=sys.stderr);sys.exit(93)
if role=='verifier':
 print('verifier stdout exact',flush=True)
 print('verifier stderr exact',file=sys.stderr,flush=True)
if mode=='sleep':time.sleep(30);sys.exit(0)
if mode=='kill9':os.kill(os.getpid(),signal.SIGKILL)
if role=='restore' and mode=='delay':time.sleep(.2);sys.exit(0)
sys.exit(int(mode))
'''
DRIVER=r'''import importlib.machinery,importlib.util,json,sys
from pathlib import Path
p=Path(sys.argv[1]);loader=importlib.machinery.SourceFileLoader('handoff',str(p/'lake'))
spec=importlib.util.spec_from_loader(loader.name,loader);m=importlib.util.module_from_spec(spec);loader.exec_module(m)
c=p/'config.json';d=json.loads(c.read_text())
sys.exit(m.finish(m.handoff(c,d,sys.argv[2:])))
'''


def rows(base):
 p=base/'events.jsonl'
 return [json.loads(line) for line in p.read_text().splitlines()] if p.exists() else []


def await_role(base,role,timeout=5):
 deadline=time.monotonic()+timeout
 while time.monotonic()<deadline:
  if any(x['role']==role for x in rows(base)):return
  time.sleep(.01)
 raise AssertionError(f'{role} did not appear')


def fixture(root,name,verify='0',enter='0',restore='0',**lake_settings):
 base=root/name;base.mkdir()
 for name in ('lake','helper.py'):shutil.copy2(ROOT/name,base/name)
 (base/'fake-lake').write_text(FAKE_LAKE);(base/'fake-lake').chmod(0o755)
 (base/'fake.py').write_text(FAKE);(base/'fake.py').chmod(0o755)
 (base/'driver.py').write_text(DRIVER)
 (base/'fake-settings.json').write_text(json.dumps(lake_settings))
 config={'real_lake':str(base/'fake-lake'),'worker_module':str(WORKER),
  'phase_enter':[str(base/'fake.py'),'enter',str(base),enter],
  'phase_restore':[str(base/'fake.py'),'restore',str(base),restore],
  'handoff_timeout_seconds':5}
 (base/'config.json').write_text(json.dumps(config))
 command=[sys.executable,'-B',str(base/'driver.py'),str(base),str(base/'fake.py'),'verifier',str(base),verify,'arg with spaces','$(literal)']
 return base,command


def main():
 results=[]
 with tempfile.TemporaryDirectory(prefix='hf-',dir='/tmp/oec/pequalnp-pilot-45') as temporary:
  root=Path(temporary)
  for status in ('0','19','kill9'):
   base,command=fixture(root,'success-'+status,verify=status,lake_delay=.1)
   p=subprocess.run(command,cwd=base,capture_output=True,text=True,timeout=10)
   expect=-signal.SIGKILL if status=='kill9' else int(status)
   assert p.returncode==expect,(p.returncode,p.stderr)
   assert p.stdout=='verifier stdout exact\n' and p.stderr=='verifier stderr exact\n'
   events=rows(base);roles=[e['role'] for e in events]
   assert roles.index('lake-exit')<roles.index('enter')<roles.index('verifier')<roles.index('restore')
   assert next(e for e in events if e['role']=='verifier')['args']==[status,'arg with spaces','$(literal)']
   assert all(e.get('cwd',str(base))==str(base) for e in events)
  results.append('Lake is gone before enter; exact verifier argv/cwd/streams and success/nonzero/SIGKILL status')
  for enter,restore,expected in [('23','0',23),('0','17',125)]:
   base,command=fixture(root,f'phase-{enter}-{restore}',enter=enter,restore=restore)
   p=subprocess.run(command,cwd=base,capture_output=True,text=True,timeout=10)
   assert p.returncode==expected,(p.returncode,p.stderr)
   roles=[e['role'] for e in rows(base)]
   assert roles[-1]=='restore'
   assert ('verifier' in roles)==(enter=='0')
  results.append('Enter failure skips verifier; restore failure remains nonzero')
  base,command=fixture(root,'lake-failure',early_failure=31)
  p=subprocess.run(command,cwd=base,capture_output=True,text=True,timeout=10)
  assert p.returncode==31 and not any(e['role']=='enter' for e in rows(base))
  results.append('Lake failure never enters storage')
  base,command=fixture(root,'lake-late-failure',lake_exit=32)
  p=subprocess.run(command,cwd=base,capture_output=True,text=True,timeout=10)
  assert p.returncode==32 and not any(e['role']=='enter' for e in rows(base))
  results.append('Lake failure after helper fork cancels blocked worker before storage')
  base,command=fixture(root,'signal-before-go',lake_delay=.4)
  p=subprocess.Popen(command,cwd=base,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
  await_role(base,'helper-exited')
  p.send_signal(signal.SIGTERM)
  out,err=p.communicate(timeout=10)
  assert p.returncode==-signal.SIGTERM,(p.returncode,out,err)
  assert not any(e['role']=='enter' for e in rows(base))
  results.append('SIGTERM before GO cancels blocked worker without entering storage')
  for during in ('enter','verifier'):
   base,command=fixture(root,'signal-'+during,enter='sleep' if during=='enter' else '0',verify='sleep' if during=='verifier' else '0')
   p=subprocess.Popen(command,cwd=base,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
   await_role(base,during)
   p.send_signal(signal.SIGTERM)
   out,err=p.communicate(timeout=10)
   assert p.returncode==-signal.SIGTERM,(p.returncode,out,err)
   assert rows(base)[-1]['role']=='restore'
  results.append('Outer SIGTERM during enter/verifier reaches worker and waits for restoration')
  base,command=fixture(root,'outer-killed',verify='sleep',restore='delay')
  p=subprocess.Popen(command,cwd=base,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
  await_role(base,'verifier');p.kill()
  out,err=p.communicate(timeout=10)
  assert p.returncode==-signal.SIGKILL
  await_role(base,'restore')
  time.sleep(.3)
  verifier_pid=next(e['pid'] for e in rows(base) if e['role']=='verifier')
  assert not Path(f'/proc/{verifier_pid}').exists()
  results.append('Outer SIGKILL closes socket; worker cancels verifier and restores without orphan hang')
  base,command=fixture(root,'lake-ignores-stop',ignore_term=True,stall_before_helper=30)
  config=json.loads((base/'config.json').read_text())
  config.update(handoff_timeout_seconds=.2,lake_stop_timeout_seconds=.2)
  (base/'config.json').write_text(json.dumps(config))
  started=time.monotonic()
  p=subprocess.run(command,cwd=base,capture_output=True,text=True,timeout=5)
  assert p.returncode==125 and time.monotonic()-started<3
  lakepid=int((base/'lake-pid').read_text())
  assert not Path(f'/proc/{lakepid}').exists()
  assert not any(e['role']=='enter' for e in rows(base))
  results.append('Pre-GO timeout escalates only owned Lake from ignored TERM to KILL without hanging')
  base,command=fixture(root,'forward',forward_only=True)
  literal=['build','arg with spaces','$(literal)','--flag=value']
  p=subprocess.run([str(base/'lake'),*literal],capture_output=True,text=True,timeout=10)
  assert p.returncode==37 and json.loads((base/'lake-argv.json').read_text())==literal
  results.append('Non-verifier Lake commands forward unchanged')
 report={'status':'PASS','checks':results}
 (ROOT/'test-results.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))


if __name__=='__main__':main()
