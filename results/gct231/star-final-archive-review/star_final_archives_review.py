from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
repo=Path('/workspace/pequalnp-proofs/results/gct231');scratch=Path('/tmp/oec/pequalnp-pilot-75/gct231/triangle-kernel-zero')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1<<20),b''):h.update(chunk)
 return h.hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
configs=[('star-pencil-audit','2dc229d89e1c0541f2a4325018abf5fd94d96c8749ec5ed870391b7d5d0d51ce',14,238870,'StarPencilWithExtension.lean','StarPencilAudit.lean','star-axiom-audit',49.444782572001714,4350560,180,6144),('star-pencil-compact','7521e2e55be9ea1d9b42641fde9cbcbf9270d8a06c352965501804a556913b86',24,245053,'StarPencilCompressedWithExtension.lean','StarPencilCompressedAudit.lean','star-compressed-audit',13.765645906001737,2932228,90,4096)]
ns='PEqualNP.Outside.L_gct_231_aux.StarPencil.';names=['r_eq_zero_of_coefficients','coefficients_force_standard_star','standard_star_triangle_extension_impossible'];queries=['#print axioms '+ns+n for n in names]
ext=(repo/'star-pencil-audit/StandardStarTriangleExtension.lean').read_text();extbody=ext[ext.index('namespace '):]
assert sha(repo/'star-pencil-audit/StandardStarTriangleExtension.lean')=='6489a8b3eb7ba20ea65c77dfb5f2c2dc34bcfb13926bc94f51b20864ed84f7b7'
for name,mh,count,size,combinedname,auditname,prefix,secs,rss,limit,memory in configs:
 base=repo/name;man=base/'sha256.json';assert sha(man)==mh;expected=json.loads(man.read_text());files={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file() and p!=man};assert len(files)==count and set(files)==set(expected)
 assert sum(p.stat().st_size for p in files.values())+man.stat().st_size==size
 for filename,p in files.items():
  assert sha(p)==expected[filename] and not p.is_symlink();b=p.read_bytes();b.decode('utf8');assert b'\x00' not in b and not b.startswith((b'\x7fELF',b'MZ'))
  if (scratch/filename).exists():assert b==(scratch/filename).read_bytes(),filename
 if name=='star-pencil-audit':
  classification=repo/'star-pencil-classification/StarPencilClassification.lean';assert sha(classification)=='7bdbee0dc04cb54742c6a0e3a60c474cbd5a9bc50dc1df6529bca5899db32603'
 else:
  classification=base/'StarPencilClassificationCompressed.lean';assert sha(classification)=='fc97915621bef10f7bab6d5f77eeb8d566786fadc27fcca5d7b5d00896ad6963'
 combined=(base/combinedname).read_text();audit=(base/auditname).read_text();original=classification.read_text()
 assert combined.startswith(original) and combined[len(original):].strip()==extbody.strip()
 assert audit.startswith(combined) and [l for l in audit[len(combined):].splitlines() if l.strip()]==queries
 run=json.loads((base/(prefix+'.run.json')).read_text());assert run['status']=='PASS' and run['returncode']==0 and run['wall_seconds']==secs and run['peak_group_rss_kib']==rss
 assert run['seconds_limit']==limit and run['resident_memory_mib_limit']==memory and run['rss_sample_seconds']==.5
 log=(base/(prefix+'.log')).read_text();records=re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]",log);assert len(records)==3
 for (actual,axioms),n in zip(records,names):assert actual==ns+n and [v.strip() for v in axioms.split(',')]==['propext','Classical.choice','Quot.sound']
 assert re.sub(r"'([^']+)' depends on axioms: \[([^]]+)\]",'',log).strip()==''
 readme=(base/'README.md').read_text();assert 'seven' in readme and 'five' in readme and ('full gap' in readme or 'full gap statement' in readme)
 print(name,'exactmanifest/source/driver/full standard3axiom logs/status/text-only PASS;entries',count,'inclusivebytes',size,flush=True)
compact=repo/'star-pencil-compact';prov=json.loads((compact/'intermediate-provenance.json').read_text())
for filekey,hashkey in [('omitted_reconstructible_linear_solver_input','input_sha256'),('omitted_linear_solver_basis','basis_sha256')]:
 name=prov[filekey];assert not (compact/name).exists();assert sha(scratch/name)==prov[hashkey]
assert (scratch/prov['omitted_linear_solver_basis']).stat().st_size==prov['basis_bytes']==152190159
assert (compact/'star-compressed-source-review.log').read_text().rstrip().endswith('PASS')
print('Omitted large intermediate input/basis hashes verified by streaming; neither included inarchive or used asLean premise. Historical111153-byte README comparison refers to preserved initialsnapshot; checked precompression source is111187bytes.',flush=True)
print('Scope: compact proof checks the same explicit scalar hypotheses; no geometric coverage/main theorem added. No compiler/solver rerun. Frozen originals unchanged.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
