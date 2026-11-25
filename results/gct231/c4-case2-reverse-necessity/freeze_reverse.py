from pathlib import Path
import json,hashlib,shutil,datetime,re
base=Path('/tmp/oec/pequalnp-pilot-75/gct231');src=base/'case2-necessity';out=Path('/workspace/pequalnp-proofs/results/gct231/c4-case2-reverse-necessity')
assert not out.exists();out.mkdir()
build=json.loads((src/'reverse-build01.json').read_text());audit=json.loads((src/'reverse-audit01.json').read_text());assert build['exit_code']==audit['exit_code']==0
s=(src/'Case2NecessaryResultantsBoth.lean').read_text();assert hashlib.sha256(s.encode()).hexdigest()==build['source_sha256']
assert (src/'Case2NecessaryResultantsBothAudit.lean').read_text().startswith(s)
assert s==(src/'Case2NecessaryResultants.lean').read_text()+'\n'+(src/'ReverseAdditions.txt').read_text()
assert re.findall(r'\[([^\]]+)\]',(src/'reverse-audit01.log').read_text()[-1000:])[-2:]==['propext,\n Classical.choice,\n Quot.sound']*2
for name in ['Case2NecessaryResultantsBoth.lean','Case2NecessaryResultantsBothAudit.lean','ReverseAdditions.txt','build.py','reverse-build01.log','reverse-build01.json','reverse-build01-frozen.json','reverse-audit01.log','reverse-audit01.json','reverse-audit01-frozen.json','freeze_reverse.py']:
 shutil.copy2(src/name,out/name)
shutil.copy2(base/'case2-reverse-necessity-review.json',out/'case2-reverse-necessity-review.json')
(out/'README.md').write_text('''# Reverse case2 necessary resultants

The standalone checked source preserves the entire previously frozen forward necessity source bytewise and appends `ReverseAdditions.txt`. From the same five explicit scalar equations it derives two V-first raw fixed-degree resultants equal to zero. It uses no division or slope nonzero premise. Coefficients, degree bounds, and common-root scope were independently reviewed by finite_cases.

The exact source compiled in23.18seconds, peak2,808,316KiB. Its exact-source audit passed in16.49seconds with only propext, Classical.choice, Quot.sound for both new principal theorems. Full logs and frozen build metadata are included. The original six-equation source mapping and its review are in the separate c4-case2-necessity archive.

This source does not prove the raw-to-projective quotient identities or normalized norm equalities, and does not settle GCT-231.
''')
checks=[]
for p in sorted(out.rglob('*')):
 if p.is_file():checks.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(out)))
(out/'SHA256SUMS').write_text('\n'.join(checks)+'\n')
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archive':str(out),'source_sha256':build['source_sha256'],'manifest_sha256':hashlib.sha256((out/'SHA256SUMS').read_bytes()).hexdigest(),'files':len(checks)+1}
(src/'reverse-archive.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
