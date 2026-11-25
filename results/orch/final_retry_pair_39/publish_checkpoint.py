"""Copy the separate retry checkpoint without touching previous archives."""
import datetime,gzip,hashlib,json,shutil
from pathlib import Path

base=Path(__file__).parent
source=base/'checkpoint'
dest=Path('/workspace/pequalnp-proofs/results/orch/final_retry_pair_39')
dest.mkdir(exist_ok=True)
for path in sorted(source.rglob('*')):
    if not path.is_file():continue
    relative=path.relative_to(source)
    target=dest/relative
    target.parent.mkdir(parents=True,exist_ok=True)
    if path.suffix=='.cnf':
        target=target.with_suffix('.cnf.gz')
        with path.open('rb') as incoming,target.open('wb') as outgoing:
            with gzip.GzipFile(filename='',mode='wb',fileobj=outgoing,mtime=0) as compressed:
                shutil.copyfileobj(incoming,compressed)
    else:shutil.copy2(path,target)
for name in ['run.py','publish_checkpoint.py','full-controller.log','independent-review.txt']:
    if (base/name).is_file():shutil.copy2(base/name,dest/name)
state='RUNNING'
if (source/'summary.json').exists():
    summary=json.loads((source/'summary.json').read_text())
    if summary['results']:state=summary['results'][-1]['status']
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(dest/'README.md').write_text('''# Final retry of pair39\n\nThis separate checkpoint preserves the earlier frozen archives unchanged. It tests the remaining pair of right-side stars10 and12, keeping the other17 gates fixed and allowing a7-gate tail for total24. The retry adds a FULL circuit cone constraint: every primary and every nonoutput gate must have a reader. In particular the frozen prefix aggregate must be used, which was not required by the original local model.\n\nThe reviewed compact single-reader blocking rules and reviewed capacity bound are included. The capacity helper receives the FULL24-gate schema; tail ordering and prefix-aware blocking receive the sliced tail schema. A complete25-gate positive control passed before the600-second retry budget began. Every SAT candidate is validated on all16,384 assignments.\n\nAny UNSAT result excludes only this strengthened model and MUST NOT change the earlier41/42 original-family exclusion count. It is external SAT evidence, not a Lean proof. No unrestricted lower bound follows.\n\nFull solver stdout/stderr, controller output, exact commands, samples, decoder schemas, source snapshots/hashes, metadata and results are retained. CNF files are losslessly compressed as .cnf.gz; metadata records each original uncompressed SHA256. No proof certificate is claimed from the solver log alone.\n\nSnapshot UTC: '''+now+'\nState: '+state+'\n')
manifest={str(p.relative_to(dest)):hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(dest.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'}
p=dest/'artifact-manifest.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'state':state,'files':len(manifest),'manifest_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                  'snapshot_utc':now},indent=2))
