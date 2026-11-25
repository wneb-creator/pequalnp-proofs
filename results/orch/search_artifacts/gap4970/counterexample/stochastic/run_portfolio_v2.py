import json
import subprocess
import sys
from datetime import datetime,timezone
from pathlib import Path

P=Path(__file__).resolve().parent
plan=[('subk4',120),('irregular11',240),('fano_minus_incident',360),('fano_minus_nonincident',240),('cubic16',240)]
records=[]
for k,(name,seconds) in enumerate(plan):
    if (P/'STOP').exists() or (P.parent.parent/'STOP').exists():break
    prefix=P/(name+'-portfolio1')
    command=[str(P/'search'),str(P/(name+'.dat')),str(seconds),str(prefix),str(497010+k)]
    record={'graph':name,'seconds':seconds,'command':command,'started_utc':datetime.now(timezone.utc).isoformat()}
    with prefix.with_suffix('.stdout').open('w') as out,prefix.with_suffix('.stderr').open('w') as err:
        child=subprocess.Popen(command,stdout=out,stderr=err)
        record['pid']=child.pid;(P/'current-run.json').write_text(json.dumps(record,indent=2)+'\n')
        code=child.wait()
    record['exit_code']=code;record['finished_utc']=datetime.now(timezone.utc).isoformat();records.append(record)
    (P/'portfolio1-results.json').write_text(json.dumps(records,indent=2)+'\n')
    print(name,'exit',code,'finished',record['finished_utc'],flush=True)
    if code!=0 or (P/'STOP').exists() or (P.parent.parent/'STOP').exists():sys.exit(code if code>0 else 1)
print('Portfolio complete; no verified counterexample.',flush=True)
