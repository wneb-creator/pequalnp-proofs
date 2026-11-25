from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import resource
import signal
import subprocess
import time

BASE=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/canonical_extra')
SOURCE=BASE/'CanonicalExtraStandalone.lean'
ENV=Path('/tmp/oec/pequalnp-pilot-78/toolchain/env.sh')
PREFIX=BASE/'standalone-build'
source=SOURCE.read_bytes()
report={'source':str(SOURCE),'source_sha256':hashlib.sha256(source).hexdigest(),
        'started_utc':datetime.now(timezone.utc).isoformat(),
        'address_space_cap_bytes':1024*2**20,'cpu_cap_seconds':240,
        'wall_cap_seconds':300,'lean_threads':1,
        'scope':'Algebra-only standalone31 definitions and24 certified quartic consequences. No main/Defs import; no posted theorem.'}
(BASE/'standalone-build-start.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'event':'START',**report}),flush=True)

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(1024*2**20,1024*2**20))
    resource.setrlimit(resource.RLIMIT_CPU,(240,245))
    resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))

command=['/bin/bash','-c','source "$1" && exec nice -n 5 lake env lean -j1 "$2"',
         'canonical-extra-check',str(ENV),str(SOURCE)]
start=time.monotonic()
with Path(str(PREFIX)+'.stdout').open('w') as stdout,Path(str(PREFIX)+'.stderr').open('w') as stderr:
    process=subprocess.Popen(command,cwd='/workspace/pequalnp-proofs/lean',
                             stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,
                             env={'PATH':'/usr/bin:/bin','TERM':'dumb'},
                             preexec_fn=limits,start_new_session=True)
    try:
        code=process.wait(timeout=300)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid,signal.SIGTERM)
        try:process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGKILL);process.wait()
        code='wall_timeout'
report.update({'completed_utc':datetime.now(timezone.utc).isoformat(),
               'exit':code,'seconds':time.monotonic()-start,
               'peak_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
               'stdout':str(PREFIX)+'.stdout','stderr':str(PREFIX)+'.stderr'})
(BASE/'standalone-build-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'event':'END',**report}),flush=True)
