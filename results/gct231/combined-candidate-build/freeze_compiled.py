from pathlib import Path
import json,hashlib,shutil,datetime
src=Path('/tmp/oec/pequalnp-pilot-75/gct231/integration')
out=Path('/workspace/pequalnp-proofs/results/gct231/combined-candidate-build')
assert not out.exists()
record=json.loads((src/'combined-build01.json').read_text())
assert record['exit_code']==0 and record['reason'] is None and record['source_unchanged']
manifest=json.loads((src/'assembly-manifest.json').read_text())
assert record['source_sha256']==manifest['candidate_sha256']
source=Path(record['source'])
assert hashlib.sha256(source.read_bytes()).hexdigest()==record['source_sha256']
out.mkdir()
files=['L_gct_231_CombinedCandidate.lean','Named1528Snapshot.lean','assembly-manifest.json','declaration-index.json','assembly.log','assemble.py','build_candidate.py','combined-build01.log','combined-build01.json','combined-build01-frozen.json','root-assembly-review.json','independent_review.py','independent-review.log']
for name in files:
    assert (src/name).is_file(),name
    shutil.copy2(src/name,out/name)
(out/'components').mkdir()
for item in manifest['components']:
    p=Path(item['path'])
    assert hashlib.sha256(p.read_bytes()).hexdigest()==item['source_sha256']
    shutil.copy2(p,out/'components'/(item['component']+p.suffix))
shutil.copy2(src/'freeze_compiled.py',out/'freeze_compiled.py')
(out/'README.md').write_text('# Compiled preservation candidate\n\nThis frozen candidate preserves the prior 1528-line named body and six independently checked components. It is a partial preservation artifact: the posted existential theorem remains absent. The named file was not changed by this branch.\n\nThe exact source compiled successfully with Lean 4.36.0, one worker, a 450-second limit and a 6-GiB RSS limit. `combined-build01.json` records the source hash, elapsed time, memory, exit code, and completion timestamp. `combined-build01.log` is the full compiler log. Root and an independent child reviewed body preservation, imports, namespaces, options, and forbidden constructs; their complete results are included.\n\n`components/` contains the exact inputs under stable labels. Their original paths and hashes are recorded in `assembly-manifest.json`; source inner bodies are preserved bytewise. The three subsequently reviewed endpoint additions are not part of this compiled V1 candidate. They appear in the distinct V2 candidate to be built by the root agent under the named path.\n')
checks=[]
for p in sorted(out.rglob('*')):
    if p.is_file():checks.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(out)))
(out/'SHA256SUMS').write_text('\n'.join(checks)+'\n')
for p in out.rglob('*'):
    if p.is_file():p.chmod(0o444)
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archive':str(out),'files':len(checks)+1,'manifest_sha256':hashlib.sha256((out/'SHA256SUMS').read_bytes()).hexdigest(),'candidate_sha256':record['source_sha256'],'build':record}
(src/'compiled-archive.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
