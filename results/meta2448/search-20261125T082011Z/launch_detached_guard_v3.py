import argparse
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import subprocess

ap=argparse.ArgumentParser()
ap.add_argument('--tag',required=True)
ap.add_argument('--guardian',choices=['guard_synthesis_v11.py','guard_synthesis_v12.py','guard_synthesis_v13.py','guard_synthesis_v14.py'],required=True)
ap.add_argument('--encoder',choices=['synthesize_v10.py','synthesize_v11.py','synthesize_v12.py'],required=True)
ap.add_argument('arguments',nargs=argparse.REMAINDER)
args=ap.parse_args()
assert args.tag and all(c.isalnum() or c in '-_' for c in args.tag)
assert args.arguments and args.arguments[0]=='--'
base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
log=base/(args.tag+'.detached-guardian.log')
metadata=base/(args.tag+'.detached-guardian.json')
assert not log.exists() and not metadata.exists()
command=['python3',str(base/args.guardian),'--tag',args.tag,'--encoder',args.encoder]+args.arguments
with log.open('x') as out:
    process=subprocess.Popen(command,cwd=base,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
try:
    raw=(Path('/proc')/str(process.pid)/'stat').read_text()
    start_ticks=int(raw[raw.rfind(')')+2:].split()[19])
except (FileNotFoundError,ProcessLookupError):start_ticks=None
record={'guardian_pid':process.pid,'guardian_process_start_ticks':start_ticks,'guardian_own_session':True,
        'started_utc':datetime.now(timezone.utc).isoformat(),'command':command,'log':str(log),
        'guardian_sha256':hashlib.sha256((base/args.guardian).read_bytes()).hexdigest(),
        'encoder_sha256':hashlib.sha256((base/args.encoder).read_bytes()).hexdigest(),
        'scope':'Launch metadata only; actual model verdict and guardian completion are separate files.'}
metadata.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
