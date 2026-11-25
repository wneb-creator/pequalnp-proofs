from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
base=Path('/workspace/pequalnp-proofs/results/gct231/triangle-axis-lean')
root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat())
manifest=base/'sha256.json';assert sha(manifest)=='c05cc0f79fc27076354256d2cfb5438f7a3d00246292b9cf31607f1325bc7255'
m=json.loads(manifest.read_text());files={p.name:p for p in base.iterdir() if p.is_file() and p!=manifest};assert len(files)==15 and set(files)==set(m)
for name,p in files.items():
 assert not p.is_symlink() and sha(p)==m[name]
 raw=p.read_bytes();raw.decode('utf8');assert b'\x00' not in raw and not raw.startswith((b'\x7fELF',b'MZ'))
print('Exact15-file coverage/all hashes/text-only; bytes including manifest',sum(p.stat().st_size for p in files.values())+manifest.stat().st_size)
source=base/'ThreeByThreeAxisCertificate.lean';assert sha(source)=='f453366b19430a626696520b30cdcbefbd2131b6aa4cc32606fa2c7beeb89a22'
assert source.read_bytes()==(base/'ThreeByThreeAxisCertificate.original.lean').read_bytes()==(root/'triangle_concept/ThreeByThreeAxisCertificate.lean').read_bytes()
txt=source.read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',txt)
assert txt.count('(h0 :')==txt.count('(h1 :')==txt.count('(h2 :')==txt.count('(h3 :')==1
command='#print axioms PEqualNP.Outside.L_gct_231_aux.TriangleAxis.reduced_system_inconsistent'
audit=(base/'AxiomAudit.lean').read_text();assert audit.startswith(txt) and audit[len(txt):].strip()==command
aliases=(base/'ThreeByThreeAxisCertificate.deprecated-import.lean').read_text();assert aliases==txt.replace('Mathlib.Basic.Complex.Basic','Mathlib.Data.Complex.Basic')
for stem in ['build02','axiom-audit']:
 d=json.loads((base/(stem+'.run.json')).read_text());assert d['status']=='PASS' and d['returncode']==0
 assert d['seconds_limit']==240 and d['resident_memory_mib_limit']==4096 and d['rss_sample_seconds']==0.5
 assert d['peak_group_rss_kib']<4096*1024
assert (base/'build02.log').read_text()==''
assert set(re.findall(r'propext|Classical.choice|Quot.sound',(base/'axiom-audit.log').read_text()))=={'propext','Classical.choice','Quot.sound'}
expected="'PEqualNP.Outside.L_gct_231_aux.TriangleAxis.reduced_system_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert ' '.join((base/'axiom-audit.log').read_text().split())==expected
assert 'deprecated' in (base/'build01.log').read_text().lower()
print('Original source byte equality, exact one-command axiom driver, four explicit hypotheses, and diagnostic alias-only delta: PASS')
print('Final empty-log build exit0 and separate standard-three-only axiom audit agree with preserved monitor metadata: PASS')
print('Scope: checked contradiction for the four displayed polynomial equations only; source-to-chart coverage and the main gap remain separate. No compile rerun.')
print('Finish UTC',datetime.now(timezone.utc).isoformat());print('PASS')
