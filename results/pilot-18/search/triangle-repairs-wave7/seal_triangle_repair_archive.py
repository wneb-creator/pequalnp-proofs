"""Seal only frozen repair evidence and finished pilot logs; no worker action."""
from pathlib import Path, PurePosixPath
import gzip
import hashlib
import io
import json
import re
import tarfile

ROOT=Path('/tmp/oec/pequalnp-pilot-18');HERE=ROOT/'orch/S02'
STAGE=HERE/'triangle-repairs-preservation-stage/S02-triangle-repairs'
OUT=HERE/'triangle-repairs-preservation-v1'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
assert not OUT.exists() and not (STAGE/'MANIFEST.json').exists()
bindings=json.loads((STAGE/'copy-bindings.json').read_text())['files']
for row in bindings:
    source=Path(row['source']);raw=source.read_bytes()
    assert not source.is_relative_to(ROOT/'best3-rescheduled-pilot')
    assert raw==(STAGE/row['archive']).read_bytes() and sha(raw)==row['sha256'] and len(raw)==row['bytes']
repro=HERE/'triangle-repairs-package-reconstruction';result=json.loads((repro/'validation.json').read_text())
assert result['verdict']=='PASS_EXACT_EIGHT_CNF_RECONSTRUCTION' and result['file_count']==26 and result['CNFs']==8
assert len(result['commands'])==3 and all(r['exit_code']==0 for r in result['commands'])
assert not result['solver_launched'] and not result['network_used'] and not result['Lean_built']
for row in result['files']:
    assert sha((repro/row['family']/row['file']).read_bytes())==row['sha256']
validation=STAGE/'validation';validation.mkdir()
for p in sorted(repro.iterdir()):
    if p.is_file():
        assert p.name=='validation.json' or p.suffix in ('.stdout','.stderr')
        (validation/p.name).write_bytes(p.read_bytes())
for stem in ['triangle-repairs-assembly','triangle-repairs-reconstruct-help','triangle-repairs-package-reconstruction']:
    for suffix in ['.stdout.txt','.stderr.txt']:
        (validation/(stem+suffix)).write_bytes((HERE/(stem+suffix)).read_bytes())
negative=validation/'negative-controls';negative.mkdir()
controls=HERE/'triangle-repairs-reconstruction-controls'
assert json.loads((controls/'validation.json').read_text())['verdict']=='PASS'
for p in sorted(controls.iterdir()):
    if p.is_file():(negative/p.name).write_bytes(p.read_bytes())
(STAGE/'seal_triangle_repair_archive.py').write_bytes(Path(__file__).read_bytes())
rows=[]
patterns=[r'github_pat_[A-Za-z0-9_]{30,}',r'gh[pousr]_[A-Za-z0-9_]{20,}',
          r'[?&]lease=[A-Za-z0-9_-]{16,}',r'-----BEGIN [A-Z ]*PRIVATE KEY-----']
for p in sorted(STAGE.rglob('*')):
    assert not p.is_symlink()
    if p.is_dir():continue
    assert p.is_file() and p.suffix!='.cnf'
    raw=p.read_bytes();text=raw.decode()
    assert not any(re.search(pattern,text) for pattern in patterns),'Sensitive value indicator; no content printed'
    rows.append({'path':str(p.relative_to(STAGE)),'bytes':len(raw),'sha256':sha(raw)})
manifest={'scope':'Prepared original/best3/rescheduled candidate families; only three finished best3 UNKNOWN pilots have runtime records.',
          'files':rows,'raw_CNF_members':0,'solver_binaries':0,'rescheduled_runtime_included':False}
(STAGE/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
OUT.mkdir();archive=OUT/'S02-triangle-repairs.tar.gz'
with archive.open('xb') as f:
    with gzip.GzipFile(filename='',fileobj=f,mode='wb',mtime=0) as gz:
        with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT) as tar:
            for p in sorted(STAGE.rglob('*')):
                if not p.is_file():continue
                raw=p.read_bytes();info=tarfile.TarInfo('S02-triangle-repairs/'+str(p.relative_to(STAGE)))
                info.size=len(raw);info.mode=0o644;info.uid=0;info.gid=0;info.mtime=0
                tar.addfile(info,io.BytesIO(raw))
with tarfile.open(archive,'r:gz') as tar:
    members=tar.getmembers()
    assert len(members)==len(rows)+1 and len({m.name for m in members})==len(members)
    for m in members:
        path=PurePosixPath(m.name)
        assert m.isfile() and not path.is_absolute() and '..' not in path.parts and path.parts[0]=='S02-triangle-repairs'
        assert tar.extractfile(m).read()==(STAGE/Path(*path.parts[1:])).read_bytes()
(OUT/'manifest.json').write_bytes((STAGE/'MANIFEST.json').read_bytes())
(OUT/'README.md').write_bytes((STAGE/'README.md').read_bytes())
report={'verdict':'PASS_SELF_PORTABLE_PACKAGE_EXACT_RECONSTRUCTION_AND_ROUNDTRIP',
        'archive_sha256':sha(archive.read_bytes()),'archive_bytes':archive.stat().st_size,
        'archive_regular_members':len(members),'manifest_sha256':sha((OUT/'manifest.json').read_bytes()),
        'exact_copies':len(bindings),'reconstruction_CNF_files':8,'reconstruction_files':26,
        'reconstruction_generator_exit0':3,'reconstruction_negative_controls':2,
        'one_gate_exhaustive_controls':2,'gate_descriptions_per_control':12362,'output_checks_per_control':420308,
        'exact_candidates_found':0,'finished_best3_pilots':3,'finished_outcomes':{'UNKNOWN':3},
        'full_solver_stdout_stderr_pairs':3,'full_controller_stdout_stderr_pairs':1,
        'original_family_runtime_included':False,'rescheduled_runtime_included':False,
        'raw_CNF_members':0,'credential_value_indicators':0,'lease_value_indicators':0,
        'active_outputs_read':False,'solver_launched':False,'repository_artifacts_changed':False,
        'blocking_findings':[],'scope':'Main independent preservation review remains required. No exact21 witness, global/shard exhaustion or posted-checker acceptance.'}
(OUT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
