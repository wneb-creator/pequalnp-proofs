import argparse,signal,subprocess,sys
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-45')
BASE_PHASE=[sys.executable,str(BASE/'resource-wrapper/storage_phase.py')]
CORE_PHASE=[sys.executable,str(BASE/'core-phase/core_phase.py')]
def normalized(code):return code if code>=0 else 128-code
class Sequence:
 def __init__(self,action,base_command,core_command):
  self.action=action;self.base=base_command;self.core=core_command;self.active=None;self.cancel_signal=None
 def interrupted(self,number,frame):
  if self.cancel_signal is None:self.cancel_signal=number
  if self.action=='enter' and self.active is not None and self.active.poll() is None:
   try:self.active.send_signal(number)
   except ProcessLookupError:pass
 def run_child(self,command):
  try:
   self.active=subprocess.Popen(command+[self.action])
   if self.action=='enter' and self.cancel_signal is not None:
    try:self.active.send_signal(self.cancel_signal)
    except ProcessLookupError:pass
   # Wait for the active phase to stop before allowing outer restoration.
   return normalized(self.active.wait())
  except OSError as error:
   print(f'storage sequence launch failed: {error}',file=sys.stderr,flush=True);return 127
  finally:self.active=None
 def run(self):
  previous={number:signal.signal(number,self.interrupted) for number in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP,signal.SIGQUIT)}
  try:
   if self.action=='enter':
    for command in (self.base,self.core):
     if self.cancel_signal is not None:return 128+self.cancel_signal
     status=self.run_child(command)
     if self.cancel_signal is not None:return 128+self.cancel_signal
     if status:return status
    return 0
   failure=0
   for command in (self.core,self.base):
    status=self.run_child(command)
    if status and not failure:failure=status
   return failure or (128+self.cancel_signal if self.cancel_signal is not None else 0)
  finally:
   for number,handler in previous.items():signal.signal(number,handler)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('action',choices=('enter','restore'));args=parser.parse_args()
 return Sequence(args.action,BASE_PHASE,CORE_PHASE).run()
if __name__=='__main__':sys.exit(main())
