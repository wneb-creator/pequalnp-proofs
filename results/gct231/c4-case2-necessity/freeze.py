from pathlib import Path
import json,hashlib,shutil,datetime,re
base=Path('/tmp/oec/pequalnp-pilot-75/gct231');src=base/'case2-necessity';out=Path('/workspace/pequalnp-proofs/results/gct231/c4-case2-necessity')
assert not out.exists()
build=json.loads((src/'build03.json').read_text());audit=json.loads((src/'audit01.json').read_text())
assert build['exit_code']==audit['exit_code']==0
s=(src/'Case2NecessaryResultants.lean').read_text();assert hashlib.sha256(s.encode()).hexdigest()==build['source_sha256']
assert (src/'Case2NecessaryResultantsAudit.lean').read_text().startswith(s)
a=(src/'audit01.log').read_text();assert re.findall(r'\[([^\]]+)\]',a[-2500:])[-5:]==['propext,\n Classical.choice,\n Quot.sound']*5
# Recover exact failed snapshots for the recorded failed-build hashes.
s2=s.replace('  constructor\n  · linear_combination hqe\n  constructor\n  · linear_combination hle\n  · linear_combination hce','  exact ⟨hqe, hle, hce⟩')
assert hashlib.sha256(s2.encode()).hexdigest()==json.loads((src/'build02.json').read_text())['source_sha256']
s1=s2.replace('theorem chart_nonzero (P B sat : ℂ)','theorem chart_nonzero (P B U V sat : ℂ)').replace('chart_nonzero P B sat hF', 'chart_nonzero P B U V sat hF').replace('set_option maxHeartbeats 600000 in\nset_option maxRecDepth 4096 in\ntheorem eliminants_vanish','set_option maxHeartbeats 600000 in\ntheorem eliminants_vanish')
for n in ['affinePolynomial','qEliminant','lEliminant','cEliminant']:s1=s1.replace('noncomputable def '+n,'def '+n)
assert hashlib.sha256(s1.encode()).hexdigest()==json.loads((src/'build01.json').read_text())['source_sha256']
(src/'FailedBuild01.lean').write_text(s1);(src/'FailedBuild02.lean').write_text(s2)
out.mkdir();(out/'failed').mkdir();(out/'inputs').mkdir()
for name in ['Case2NecessaryResultants.lean','Case2NecessaryResultantsAudit.lean','Case2NecessaryElimination.lean','generate.py','combine.py','build.py','reduction-certificates.json','build03.log','build03.json','build03-frozen.json','audit01.log','audit01.json','audit01-frozen.json','freeze.py']:
 shutil.copy2(src/name,out/name)
for name in ['FailedBuild01.lean','FailedBuild02.lean','build01.log','build01.json','build02.log','build02.json']:
 shutil.copy2(src/name,out/'failed'/name)
for name in ['case2_necessity_review.py','case2-necessity-independent-review.json','case2-necessity-independent-review.log','case2-necessity-independent-review-final.log']:
 shutil.copy2(base/name,out/name)
shutil.copy2(base/'ResultantCommonRoot.lean',out/'inputs'/'ResultantCommonRoot.lean')
shutil.copy2(base/'fresh/c4-nonzero-reduced-2.json',out/'inputs'/'original-six-equations.json')
data=json.loads((base/'c4-case2-resultants.json').read_text());data['reductions']=data['reductions'][:4]
(out/'inputs/reduced-first-stage.json').write_text(json.dumps(data,indent=2)+'\n')
(out/'README.md').write_text('''# Exact case2 necessary elimination

`Case2NecessaryResultants.lean` is a checked scoped bridge from the six explicit reduced case2 equations to nonzero P, B, curve-leading factor and chart determinant, and to two raw bounded polynomial resultants equal to zero. The field is complex. No slope nonzero assumption or leading-coefficient division is used. The exact original equation mapping and elementary ring reduction certificates were independently reviewed.

The source includes the separately checked generic common-root resultant helper exactly once. Its remaining namespace is `PEqualNP.Outside.L_gct_231_aux.Case2Necessity`. The source compiled successfully in15.31seconds with peak2,795,124KiB. A separate exact-source audit compiled in18.88seconds and reported only propext, Classical.choice, Quot.sound for the five principal theorems. Full logs and metadata are retained.

This does not identify the raw resultants with the divided projective quotient, does not derive the two normalized univariate norm hypotheses in the separate projective-norm certificate, and does not settle GCT-231. Those connecting equalities remain outside this source.

The first failed build lacked noncomputable tags and a recursion limit; the second encountered expensive definitional unification at the final tuple. The final proof uses three scalar ring-normalized goals instead. Exact failed source snapshots are reconstructed and hash-checked against their build metadata, and preserved under failed/.
''')
checks=[]
for p in sorted(out.rglob('*')):
 if p.is_file():checks.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(out)))
(out/'SHA256SUMS').write_text('\n'.join(checks)+'\n')
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archive':str(out),'source_sha256':build['source_sha256'],'manifest_sha256':hashlib.sha256((out/'SHA256SUMS').read_bytes()).hexdigest(),'files':len(checks)+1}
(src/'archive.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
