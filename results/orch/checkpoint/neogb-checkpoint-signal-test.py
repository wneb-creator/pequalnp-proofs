import ctypes as C
import importlib.util
import json
import os
from pathlib import Path
import signal
import sys

P=Path('/tmp/oec/pequalnp-pilot-79')
spec=importlib.util.spec_from_file_location('cpdriver',P/'neogb-run-checkpoint.py')
driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver)
sig=getattr(signal,sys.argv[1])
real_cdll=C.CDLL
class SignalAfterConfigure:
 def __init__(self,function): object.__setattr__(self,'function',function)
 def __setattr__(self,name,value): setattr(self.function,name,value)
 def __call__(self,*args):
  result=self.function(*args)
  assert result==0
  os.kill(os.getpid(),sig)
  return result

def cdll(*args,**kwargs):
 lib=real_cdll(*args,**kwargs)
 if args[0] and str(args[0]).endswith('libneogb-checkpoint.so'):
  lib.neogb_checkpoint_configure=SignalAfterConfigure(lib.neogb_checkpoint_configure)
 return lib
C.CDLL=cdll
label='checkpoint-signal-'+str(int(sig))
sys.argv=[str(P/'neogb-run-checkpoint.py'),'-f',str(P/'checkpoint-check-97.msolve'),'-o',str(P/(label+'.json')),'--checkpoint',str(P/(label+'.gz')),'--info','0','--max-pairs','1']
driver.main()
result=json.loads((P/(label+'.json')).read_text())
assert (P/(label+'.gz')).exists()
assert result['status']==('PARTIAL' if sig==signal.SIGUSR2 else 'COMPLETE')
print('SIGNAL TEST PASSED',signal.Signals(sig).name,flush=True)
