#!/usr/bin/env python3
"""Package only the two frozen handoffs and explicitly named main review sources."""
import datetime
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT=Path('/tmp/oec/pequalnp-pilot-18')
OWN=ROOT/'orch/S06'
STAGE=OWN/'gadget8-preservation-v1'
ARCHIVE=OWN/'gadget8-preservation-v1.tar.gz'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def info(p):return {'bytes':p.stat().st_size,'sha256':sha(p)}
def save(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def require(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    require(not STAGE.exists() and not ARCHIVE.exists(),'fresh package required')
    STAGE.mkdir()
    selected={}
    def add(p,expected=None):
        require(p.is_file() and not p.is_symlink(),'regular source required '+str(p))
        require(p.is_relative_to(ROOT),'source outside scratch')
        require('__pycache__' not in p.parts and p.suffix not in ['.pyc','.pyo'],'compiled Python excluded')
        actual=info(p)
        if expected is not None:require(actual==expected,'frozen source mismatch '+str(p))
        selected[p]=actual
    for name,pin in [('gadget8-handoff.json','680c4d01926307c859940f8b1ac2f1247b74d878302ff8a2c0e04cd5d26889ed'),('gadget8-runner-review-handoff.json','4b24936c148500cfd88d2d43a0232b4ad22c383d78844d88959f22a284fd5b89')]:
        p=OWN/name;require(sha(p)==pin,'handoff pin');add(p)
        for rel,expected in json.loads(p.read_text())['files'].items():
            require(not Path(rel).is_absolute() and '..' not in Path(rel).parts,'unsafe handoff path')
            add(OWN/rel,expected)
    for p in [ROOT/'orch/MAIN/main-gadget8-review.json',ROOT/'orch/MAIN/gadget8-runner-v1/offline_gadget8_cadical.py',ROOT/'orch/MAIN/gadget8-runner-v1/source.diff',ROOT/'orch/MAIN/gadget8-runner-v1/derivation.json',OWN/'package_gadget8_archive.py',OWN/'restore_gadget8_archive.py']:
        add(p)
    mainreview=json.loads((ROOT/'orch/MAIN/main-gadget8-review.json').read_text())
    require(mainreview['verdict']=='PASS_MAIN_GENERIC_GADGET_ENCODER_VALIDATOR_AND_EXACT_EXTENSION' and mainreview['bound_files']==36 and mainreview['independent_generic12_clauses']==14093,'main review scope')
    require(sha(ROOT/'orch/MAIN/gadget8-runner-v1/offline_gadget8_cadical.py')=='5c196750473896225cb414458a150bccfc5dff3d68ecbeceec2aaf1c7f088b34','runner pin')
    source_map={};omitted={};groups={}
    for src,expected in sorted(selected.items()):
        rel='scratch/'+str(src.relative_to(ROOT));target=STAGE/rel
        source_map[str(src)]={'path':rel,**expected}
        if src.suffix=='.cnf':
            omitted[rel]=expected;groups.setdefault(expected['sha256'],[]).append(rel)
        else:
            target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
            require(info(target)==expected,'copy mismatch')
    family=json.loads((OWN/'gadget8-handoff.json').read_text())['family']
    recipes=[]
    for entry in family:
        name=entry['name'];recipes.append({'name':name,'gates':13 if name in ['generic13','positive13-pinned'] else 12,'pin':{'positive13-pinned':'positive13','bad12-pinned':'bad12'}.get(name,'none'),'sha256':entry['cnf_sha256'],'metadata_sha256':entry['metadata_sha256'],'bytes':entry['bytes'],'aliases':groups.pop(entry['cnf_sha256'])})
    require(not groups and len(recipes)==4,'four unique CNFs only')
    save(STAGE/'CNF_RECIPES.json',{'format':'s06-gadget8-four-cnf-recipes-v1','generator':'scratch/orch/S06/build_gadget8.py','generator_sha256':'3ca5274e1a394aff25e8f633bfc07ca5dd9ed2163b43db321dfba218e6b1ac17','method':'Import exact archived source with bytecode disabled; call build(k), append pins(meta,circuit_controls()[index]) for pinned fixtures, serialize cnf.raw(); metadata recomputed and compared byte-exact. No solver/checker.','recipes':recipes})
    (STAGE/'README.md').write_text('''# Eight-input gadget source and finite-control preservation

This package freezes the generic eight-input AND/OR construction encoder,
validator, four CNF recipes, all scalar/model/runner controls, complete fixture
RUP and binary DRAT certificates with checker logs, main encoder review, and
S06 independent runner-delta review. All original source and historical report
bytes remain unchanged. Historical "not launched" records refer to their own
timestamps. Main launched generic12 later; its runtime and launch record are
intentionally outside this package. No active production directory was read.

The generic12 target has996 variables,14093 clauses and17 exact boundary rows.
A valid12-gate gadget gives an explicit21-gate full11 circuit. Gadget UNSAT
would exclude only this construction route, never the full gap or shard.
Only the fully pinned bad12 fixture has checked UNSAT certificates here.
The exact positive13 fixture extends to22 gates and is correctly rejected by
the runner. All15 synthetic runner controls reject; their logs are explicitly
marked and are not searches or certificates.

After extracting into a fresh directory, run:

    python3 -B scratch/orch/S06/restore_gadget8_archive.py .

This verifies every payload, imports the byte-identical encoder, reconstructs
all four unique CNFs and their fixture/synthetic snapshot aliases, compares
every metadata byte, and rechecks all208 historical handoff bindings. It uses
only Python's standard library and runs no solver or checker. Source paths in
historical logs are provenance; archive-relative paths are in MANIFEST.json.
CNF_RECIPES.json binds every omitted CNF to its exact generation recipe.

No executable binaries are included. The preserved binary DRAT is certificate
data. Solver/checker binary SHA256 pins and exact commands occur in the runner
source and full result records; obtain those exact binaries separately for
optional replay. The4,198-byte DRAT was checked by the pinned DSR, and the
separate6,492-byte RUP was checked with --forward --rup-only. Full logs remain
byte-exact, including whitespace and intentionally empty stderr files.

The reviewed runner retains original absolute workspace/tool pins. Replaying
the original bounded controls requires recreating that workspace layout or a
separately reviewed relocation. Portable CNF restoration needs no relocation
of source code: it calls the encoder's pure build/pins APIs and leaves its
hard-coded CLI output-directory restriction untouched. No test reruns or
production are part of archive restoration. Lean acceptance remains separate.
''')
    payload={str(p.relative_to(STAGE)):info(p) for p in sorted(STAGE.rglob('*')) if p.is_file()}
    manifest={'format':'s06-gadget8-preservation-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload':payload,'omitted_cnfs':omitted,'source_map':source_map,'historical_handoff_bindings':208,'active_production_included':False,'scope':'All generic8 preparation/finite controls/reviews only. Four unique CNFs reconstructed; no runtime or global/Lean claim.'}
    save(STAGE/'MANIFEST.json',manifest)
    shutil.copyfile(STAGE/'MANIFEST.json',OWN/'gadget8-preservation-v1-manifest.json')
    with ARCHIVE.open('xb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as compressed:
            with tarfile.open(fileobj=compressed,mode='w',format=tarfile.PAX_FORMAT) as tar:
                for p in sorted(STAGE.rglob('*')):
                    if not p.is_file():continue
                    data=p.read_bytes();item=tarfile.TarInfo(str(p.relative_to(STAGE)))
                    item.size=len(data);item.mode=0o644;item.mtime=0;item.uid=item.gid=0;item.uname=item.gname=''
                    tar.addfile(item,io.BytesIO(data))
    print(json.dumps({'status':'BUILT_NO_ACTIVE_OUTPUTS','archive':str(ARCHIVE),'archive_info':info(ARCHIVE),'manifest_sha256':sha(STAGE/'MANIFEST.json'),'payloads':len(payload),'tar_members':len(payload)+1,'source_map_bindings':len(source_map),'unique_cnf_recipes':len(recipes),'omitted_cnf_aliases':len(omitted)},sort_keys=True))

if __name__=='__main__':main()
