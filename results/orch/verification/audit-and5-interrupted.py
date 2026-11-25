from pathlib import Path
import datetime
import gzip
import hashlib
import json

root = Path(__file__).resolve().parents[1]
base = root / 'search/petersen-and5-interrupted'
manifest_bytes = (base/'manifest.json').read_bytes()
manifest = json.loads(manifest_bytes)
def digest(path):
    h=hashlib.sha256(); n=0
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024), b''):
            h.update(block); n+=len(block)
    return n,h.hexdigest()
assert manifest['classification']=='INTERRUPTED_NO_VERDICT'
assert len(manifest['files'])==17
assert {r['path'] for r in manifest['files']}|{'manifest.json'} == {p.name for p in base.iterdir() if p.is_file()}
for r in manifest['files']:
    assert digest(base/r['path'])==(r['bytes'],r['sha256'])
classification=json.loads((base/'classification.json').read_text())
assert classification['ordered_gzip_parts']==['proof.drat.gz.part-000']
gz=base/classification['ordered_gzip_parts'][0]
assert digest(gz)==(classification['gzip_stream_bytes'],classification['gzip_stream_sha256'])
h=hashlib.sha256(); size=0
with gzip.open(gz,'rb') as f:
    for block in iter(lambda:f.read(1024*1024),b''):
        h.update(block);size+=len(block)
assert (size,h.hexdigest())==(classification['raw_drat_bytes'],classification['raw_drat_sha256'])
status=json.loads((base/'status.json').read_text())
launch=json.loads((base/'launch.json').read_text())
stop=json.loads((base/'coordinator-stop.json').read_text())
pid=json.loads((base/'pid.json').read_text())
assert all(status[k]==v for k,v in launch.items())
assert status==json.loads((base/'petersen-and5-launcher.log').read_text())
assert status['returncode']==-15 and status['status']=='PROCESS_FAILURE'
assert status['cpu_affinity']==[3] and status['address_limit_bytes']==status['proof_file_limit_bytes']==2**30
assert status['proof_bytes']==size and status['maxrss_kib']==78512
assert stop['signal']=='SIGTERM' and stop['pid']==pid['solver']
dt=lambda s:datetime.datetime.fromisoformat(s)
assert dt(status['start_utc']) < dt(stop['utc']) <= dt(status['end_utc'])
assert abs((dt(status['end_utc'])-dt(status['start_utc'])).total_seconds()-status['wall_seconds'])<0.01
assert 366 < status['wall_seconds'] < 367
argv=status['argv']
assert argv[1:7]==['-t','900','--seed=0','--binary=true','-w',str(Path(argv[-1]).parent/'model.out')]
assert Path(argv[-2]).name=='problem.cnf' and Path(argv[-1]).name=='proof.drat'
encoding=json.loads((base/'encoding.json').read_text())
assert encoding==json.loads((base/'free-or-and5-generation.log').read_text())
assert digest(base/'problem.cnf')[1]==encoding['cnf_sha256']
with (base/'problem.cnf').open() as f:
    header=f.readline().split(); clauses=0
    assert header==['p','cnf',str(encoding['variables']),str(encoding['clauses'])]
    for line in f:
        lits=list(map(int,line.split()))
        assert lits and lits[-1]==0 and all(0<abs(v)<=encoding['variables'] for v in lits[:-1])
        clauses+=1
assert clauses==175408
log=(base/'solver.stdout-stderr.txt').read_text()
answers=[line for line in log.splitlines() if line.startswith('s ')]
assert not any(line in ['s SATISFIABLE','s UNSATISFIABLE'] for line in answers)
assert 'Version 2.1.2' in log and "found 'p cnf 41085 175408' header" in log
assert log.rstrip().endswith('c raising signal 15 (SIGTERM)')
result=dict(verdict='PASS: archive integrity and interrupted status only',manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),manifest_entries=17,raw_drat_bytes=size,raw_drat_sha256=h.hexdigest(),gzip_full_crc_and_hash=True,solver_returncode=-15,wall_seconds=status['wall_seconds'],peak_rss_kib=status['maxrss_kib'],solver_status_lines=answers,cnf_variables=encoding['variables'],cnf_clauses=clauses,scope='No independent semantic encoding review, solver rerun, DRAT verification, SAT/UNSAT verdict or Lean result. Partial DRAT is incomplete.')
(root/'verification/audit-and5-interrupted.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
