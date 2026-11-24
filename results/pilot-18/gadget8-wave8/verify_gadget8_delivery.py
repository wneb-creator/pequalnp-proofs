#!/usr/bin/env python3
"""Fresh extraction/recipe check only; never run a solver or checker."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import time

OWN=Path('/tmp/oec/pequalnp-pilot-18/orch/S06')
ARCHIVE=OWN/'gadget8-preservation-v1.tar.gz'
DEST=OWN/'gadget8-preservation-restore-v1'
PIN='a261356299baa8fc7f987a4fb89d96c03e742c0ea7f4fd30ee573768bb9f1b2b'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def info(p):return {'bytes':p.stat().st_size,'sha256':sha(p)}
def save(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def check(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    check(sha(ARCHIVE)==PIN,'archive pin')
    check(not DEST.exists(),'fresh extraction required');DEST.mkdir()
    with tarfile.open(ARCHIVE,'r:gz') as tar:
        members=tar.getmembers();names=[m.name for m in members]
        check(len(names)==len(set(names)),'duplicate archive members')
        check(all(m.isfile() and m.mode==0o644 and m.size<1024**2 and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts and '__pycache__' not in Path(m.name).parts and not m.name.endswith(('.pyc','.pyo','.cnf')) for m in members),'unexpected member type/path/size')
        for member in members:
            p=DEST/member.name;p.parent.mkdir(parents=True,exist_ok=True)
            with p.open('xb') as f:f.write(tar.extractfile(member).read())
    manifest=json.loads((DEST/'MANIFEST.json').read_text())
    check(sha(DEST/'MANIFEST.json')==sha(OWN/'gadget8-preservation-v1-manifest.json'),'manifest external copy')
    check(set(names)==set(manifest['payload'])|{'MANIFEST.json'},'exact tar inventory')
    for name,expected in manifest['payload'].items():check(info(DEST/name)==expected,'payload '+name)
    cmd=[sys.executable,'-B',str(DEST/'scratch/orch/S06/restore_gadget8_archive.py'),str(DEST)]
    start=time.monotonic()
    with (OWN/'gadget8-preservation-restore.stdout').open('xb') as stdout,(OWN/'gadget8-preservation-restore.stderr').open('xb') as stderr:
        r=subprocess.run(cmd,cwd=DEST,stdout=stdout,stderr=stderr,timeout=15)
    execution={'command':cmd,'exit_code':r.returncode,'wall_seconds':time.monotonic()-start,'wall_limit_seconds':15,'solver_or_checker_launched':False}
    save(OWN/'gadget8-preservation-restore.execution.json',execution)
    check(r.returncode==0,'portable restore failed; see full logs')
    restored=json.loads((OWN/'gadget8-preservation-restore.stdout').read_text())
    check(restored['unique_cnf_recipes']==4 and restored['restored_cnf_aliases']==21 and restored['historical_handoff_bindings']==208,'restore counts')
    for original,entry in manifest['source_map'].items():
        expected={k:entry[k] for k in ['bytes','sha256']}
        check(info(Path(original))==expected,'original frozen source changed '+original)
        check(info(DEST/entry['path'])==expected,'restored source differs '+entry['path'])
    proof=DEST/'scratch/orch/S06/gadget8-runner-controls/bad12-pinned/proof.drat'
    rup=DEST/'scratch/orch/S06/gadget8-v1/bad12-pinned.rup'
    check(sha(proof)=='d30c629d500b1e3d6b3b907f7078ff00716e2dce9946d749c15fde52ce1284f5','DRAT pin')
    check(sha(rup)=='b3396378431d05464519a893cc3d70f58b2ccfeb97b0244d7b108a651a2724c6','RUP pin')
    report={'status':'PASS_FRESH_DELIVERY_198_MEMBERS_4_RECIPES_208_HANDOFF_BINDINGS','archive':info(ARCHIVE),'manifest_sha256':sha(DEST/'MANIFEST.json'),'members':len(names),'payloads':len(manifest['payload']),'source_map_bindings':len(manifest['source_map']),'portable_restore':restored,'execution':execution,'full_fixture_drat':info(proof),'full_fixture_rup':info(rup),'verifier_source_sha256':sha(Path(__file__)),'active_production_read_or_included':False,'solver_or_checker_launched':False}
    save(OWN/'gadget8-preservation-delivery-review.json',report)
    print(json.dumps(report,indent=2,sort_keys=True))

if __name__=='__main__':main()
