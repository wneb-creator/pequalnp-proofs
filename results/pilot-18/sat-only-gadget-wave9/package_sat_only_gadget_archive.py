#!/usr/bin/env python3
"""Freeze only explicit source/control/review inventories; exclude production."""
import datetime
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import time

ROOT=Path('/tmp/oec/pequalnp-pilot-18');OWN=ROOT/'orch/S06'
STAGE=OWN/'sat-only-gadget-preservation-v1';ARCHIVE=OWN/'sat-only-gadget-preservation-v1.tar.gz'
RESTORE=OWN/'sat-only-gadget-preservation-restore-v1'
def info(p):return {'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def save(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def check(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    check(not STAGE.exists() and not ARCHIVE.exists() and not RESTORE.exists(),'fresh destinations required')
    STAGE.mkdir();selected={}
    def add(p,expected=None):
        check(p.is_relative_to(ROOT) and p.is_file() and not p.is_symlink(),'regular allowed source')
        check('__pycache__' not in p.parts and p.suffix not in ['.pyc','.pyo'],'no compiled Python')
        actual=info(p)
        if expected is not None:check(actual==expected,'frozen source changed '+str(p))
        selected[p]=actual
    six=OWN/'sat-only-gadget-handoff.json';five=ROOT/'orch/S05/kissat-sat-only-review-handoff.json'
    check(info(six)['sha256']=='2a00340c4181f01e3c9a705cfe1871b33639ef208402dcbcf72016b02f578567','S06 handoff pin')
    check(info(five)['sha256']=='a7442833708c0264e301ab11336eac87c5660d77aad8dc9ab3a6fbc0cb3d08a8','S05 handoff pin')
    add(six);add(five)
    for name,expected in json.loads(six.read_text())['files'].items():add(ROOT/name,expected)
    for entry in json.loads(five.read_text())['artifacts']:add(Path(entry['path']),{k:entry[k] for k in ['bytes','sha256']})
    main_review=ROOT/'orch/MAIN/main-sat-only-gadget-review.json';add(main_review)
    review=json.loads(main_review.read_text())
    check(review['status']=='PASS_MAIN_SAT_ONLY_GADGET_RUNNER_SOURCE_AND_BINDINGS' and review['handoff_sha256']==info(six)['sha256'],'main review binding')
    generators={7:(ROOT/'orch/S05/build_gadget7.py','6bc53c66e01a9f7a3fbcede34ddba0893209636be60d4a1ea18505970b5b1c16'),8:(OWN/'build_gadget8.py','3ca5274e1a394aff25e8f633bfc07ca5dd9ed2163b43db321dfba218e6b1ac17')}
    families={}
    for gadget,(source,pin) in generators.items():
        check(info(source)['sha256']==pin,'generator pin');add(source)
        directory=source.parent/f'gadget{gadget}-v1';family=directory/'family.json';add(family)
        entries=json.loads(family.read_text())['family']
        wanted=[entry for entry in entries if entry['name'] in (["generic11","positive12-pinned","bad11-pinned"] if gadget==7 else ["generic12","positive13-pinned","bad12-pinned"])]
        check(len(wanted)==3,'three relevant CNFs per gadget')
        for entry in wanted:
            cnf=directory/(entry['name']+'.cnf');meta=cnf.with_suffix('.json')
            check(info(cnf)['sha256']==entry['cnf_sha256'] and info(meta)['sha256']==entry['metadata_sha256'],'family source pin')
            add(cnf);add(meta);families[entry['cnf_sha256']]=(gadget,entry)
    add(Path(__file__));add(OWN/'restore_sat_only_gadget_archive.py')
    source_map={};omitted={};groups={}
    for source,expected in sorted(selected.items()):
        rel='scratch/'+str(source.relative_to(ROOT));source_map[str(source)]={'path':rel,**expected}
        if source.suffix=='.cnf':omitted[rel]=expected;groups.setdefault(expected['sha256'],[]).append(rel)
        else:
            target=STAGE/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);check(info(target)==expected,'copied bytes')
    recipes=[]
    for ch,aliases in sorted(groups.items()):
        gadget,entry=families[ch];name=entry['name'];source,pin=generators[gadget]
        meta=json.loads((source.parent/f'gadget{gadget}-v1'/(name+'.json')).read_text())
        recipes.append({'name':name,'gadget':gadget,'gates':meta['gate_count'],'pin':'positive' if name.startswith('positive') else ('bad' if name.startswith('bad') else 'none'),'generator':'scratch/'+str(source.relative_to(ROOT)),'generator_sha256':pin,'sha256':ch,'bytes':entry['bytes'],'metadata_sha256':entry['metadata_sha256'],'aliases':aliases})
    check(len(recipes)==6,'six relevant recipes')
    save(STAGE/'CNF_RECIPES.json',{'method':'Import exact archived generator; build(gates), append its control-circuit pin units as specified, serialize raw and recompute metadata. No solver/checker.','recipes':recipes})
    save(STAGE/'BINARY_PINS.json',{'binaries_omitted':True,'solver':{'original_path':str(ROOT/'solver/kissat-4.0.4-linux-amd64'),'sha256':'21da5d984e38b74f620f14c62442f834f27b9158decdb722540d97f98aac93a1'},'no_proof_generation':True,'no_checker_invoked':True,'note':'Original parent lifecycle also contains dormant CaDiCaL/checker constants; only its phase/binding/serialization helpers are reused by this wrapper.'})
    (STAGE/'README.md').write_text('''# SAT-only gadget7/gadget8 runner and independent controls

This package freezes runnerfd05c032, parent lifecycleaa5d13, both pinned
validators, both CNF generators for portable recipes, all S06/S05 tiny
controls and reviews, main's source/binding review and both encoder reviews.
Historical pending/not-launched statements refer to their own timestamps.
Both later production runs and launch records are excluded and unread.
Main preserves completed production separately. Gadget7's wider source
and proof-control archive is a separate S05 delivery.

The runner invokes pinned Kissat with --sat --no-color --statistics and
exactly one positional CNF, without a proof path. Solver UNSAT always means
UNCERTIFIED_UNSAT_NO_PROOF/statusUNKNOWN/exit2. Only pinned validation of
every128/256 gadget input, every2048 full input, both gate limits, consistent
gate counts and allfour provenance hashes permits exit10 VALIDATED_SAT.
No exact21 positive fixture exists. The positive12/13 controls validate
full22 circuits and correctly reject; synthetic report baselines are not
models. S06's6 real controls+24 rejections and S05's6 real controls+52
rejections are preserved with complete stdout/stderr and status records.

Extract into a fresh directory, then run:

    python3 -B scratch/orch/S06/restore_sat_only_gadget_archive.py .

Only Python's standard library is needed. The command checks all payloads,
restores six unique CNFs and every copied fixture snapshot using unchanged
generator APIs, checks metadata bytes, verifies72 S06+65 S05 handoff
bindings and every source mapping, and replays four retained positive
models through the archived full validators. It starts no solver/checker.

CNFs are omitted as reproducible bulk; CNF_RECIPES.json binds all aliases.
No executable binary or compiled Python cache is included. Binary hashes
are in BINARY_PINS.json and original records. Source files retain exact
original paths and bytes; replaying the original runner/controls needs
the original workspace layout and exact Kissat binary or a separately
reviewed relocation. Portable restoration requires no source edits and
does not import or execute the pinned runtime wrapper/lifecycle module.

The6 relevant CNFs are the two generic construction targets and four
pinned positive/negative fixtures. The unused larger generic variants
remain in the separate gadget source archives. All preserved UNSAT
observations here are intentionally uncertified UNKNOWN, never exhaustive
gadget/global results. Lean acceptance remains separate.
''')
    payload={str(p.relative_to(STAGE)):info(p) for p in sorted(STAGE.rglob('*')) if p.is_file()}
    manifest={'format':'s06-sat-only-gadget-preservation-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload':payload,'source_map':source_map,'omitted_cnfs':omitted,'active_production_read_or_included':False,'scope':'Frozen exact runner/lifecycle/validators/controls/reviews only; no production or accepted global/Lean result.'}
    save(STAGE/'MANIFEST.json',manifest);shutil.copyfile(STAGE/'MANIFEST.json',OWN/'sat-only-gadget-preservation-manifest.json')
    with ARCHIVE.open('xb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as compressed:
            with tarfile.open(fileobj=compressed,mode='w',format=tarfile.PAX_FORMAT) as tar:
                for p in sorted(STAGE.rglob('*')):
                    if not p.is_file():continue
                    data=p.read_bytes();m=tarfile.TarInfo(str(p.relative_to(STAGE)));m.size=len(data);m.mode=0o644;m.mtime=0;tar.addfile(m,io.BytesIO(data))
    RESTORE.mkdir()
    with tarfile.open(ARCHIVE,'r:gz') as tar:
        members=tar.getmembers();check(len(members)==len(payload)+1 and {m.name for m in members}==set(payload)|{'MANIFEST.json'},'archive member inventory')
        for m in members:
            check(m.isfile() and m.mode==0o644 and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts,'regular safe member')
            data=tar.extractfile(m).read();check(data==(STAGE/m.name).read_bytes(),'archive roundtrip');p=RESTORE/m.name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    command=[sys.executable,'-B',str(RESTORE/'scratch/orch/S06/restore_sat_only_gadget_archive.py'),str(RESTORE)];start=time.monotonic()
    with (OWN/'sat-only-gadget-preservation-restore.stdout').open('xb') as stdout,(OWN/'sat-only-gadget-preservation-restore.stderr').open('xb') as stderr:
        result=subprocess.run(command,stdout=stdout,stderr=stderr,cwd=RESTORE,timeout=15)
    execution={'command':command,'exit_code':result.returncode,'wall_seconds':time.monotonic()-start,'wall_limit_seconds':15,'solver_or_checker_launched':False}
    save(OWN/'sat-only-gadget-preservation-restore.execution.json',execution);check(result.returncode==0,'portable restore failed; see full logs')
    restored=json.loads((OWN/'sat-only-gadget-preservation-restore.stdout').read_text())
    for source,expected in selected.items():check(info(source)==expected,'source changed during packaging')
    review={'status':'PASS_SAT_ONLY_PORTABLE_ARCHIVE_AND_FULL_BINDING_RESTORE','archive':info(ARCHIVE),'manifest_sha256':info(STAGE/'MANIFEST.json')['sha256'],'members':len(payload)+1,'payloads':len(payload),'source_map_bindings':len(source_map),'portable_restore':restored,'active_production_read_or_included':False,'solver_or_checker_launched':False}
    save(OWN/'sat-only-gadget-preservation-review.json',review);print(json.dumps(review,indent=2,sort_keys=True))

if __name__=='__main__':main()
