from pathlib import Path,PurePosixPath
import sys,json,hashlib,io,tarfile,gzip,datetime,subprocess
sys.path.insert(0,str(Path(__file__).parent))
from wave5_delivery_helpers import R,sha,Review
O=R/'orch/S08/combined-141-shuffle-preservation-v1';O.mkdir(exist_ok=True)
F=R/'orch/S08/combined-141-shuffle-review';review=json.loads((F/'review.json').read_text())
assert sha((F/'review.json').read_bytes())=='5146eb7ac9871706deee49391118489790dfaedd3ad7113a73b9d5e256826de3'
payload={};origins={};byhash={};omitted={};mapping={}
def add(p,name):
 b=p.read_bytes();h=sha(b)
 if b.startswith(b'\x7fELF'):
  omitted[str(p)]={'bytes':len(b),'sha256':h,'disposition':'omitted_ELF','reason':'Executable excluded; source/build logs/commands and exact reviewed binary hashes retained.'};return None
 assert name not in payload;payload[name]=b;origins[name]=str(p);byhash.setdefault((h,len(b)),name);return name
for p in sorted(F.rglob('*')):
 if p.is_file():assert not p.is_symlink();add(p,'review/'+str(p.relative_to(F)))
mandatory={
 str(R/'orch/S05/triangle589-best3-direct21-v1/direct-seeds.txt'):'dependencies/packs/best3/direct-seeds.txt',
 str(R/'orch/S05/triangle589-best3-direct21-v1/direct-seeds.json'):'dependencies/packs/best3/direct-seeds.json',
 str(R/'validate_raw_candidate.py'):'dependencies/validate_raw_candidate.py',
 str(R/'lean-setup/validate_sat_candidate.py'):'dependencies/lean-setup/validate_sat_candidate.py',
 str(R/'lean-setup/stochastic/stochastic_tools.py'):'dependencies/stochastic_tools.py',
 str(R/'orch/MAIN/all-negative-engine-v1/circuit_anneal_allnegative.cpp'):'dependencies/circuit_anneal_allnegative.cpp',
 str(R/'orch/MAIN/all-negative-engine-v1/parent.cpp'):'dependencies/parent40.cpp',
 str(R/'orch/S02/shuffle-engine-v1/circuit_anneal_shuffle.cpp'):'dependencies/circuit_anneal_shuffle.cpp'}
for path,row in review['bindings'].items():
 p=Path(path);assert p.is_relative_to(R);b=p.read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],path
 if b.startswith(b'\x7fELF'):
  if path not in omitted:add(p,'unused-binary/'+p.name)
  mapping[path]=omitted[path];continue
 key=(row['sha256'],row['bytes'])
 if path in mandatory:name=add(p,mandatory[path])
 elif key in byhash:name=byhash[key]
 else:name=add(p,'bound/'+str(p.relative_to(R)))
 mapping[path]={'bytes':len(b),'sha256':sha(b),'disposition':'payload','archive_path':name}
# Include full outer review logs, the reviewer source, and fake-engine input needed to understand rejection.
for n in ['review_combined_shuffle.py','combined-141-shuffle-review-run.stdout','combined-141-shuffle-review-run.stderr','wave5_delivery_helpers.py']:
 add(R/'orch/S08'/n,'review-driver/'+n)
for n in ['fake_claimed_candidate.py','deliberately_inexact_candidate.json']:
 p=R/'orch/S08/all-negative-engine-review'/n
 if (sha(p.read_bytes()),p.stat().st_size) not in byhash:add(p,'control-fixtures/'+n)
add(R/'orch/S02/best4-shuffle-preservation-handoff.json','companions/S02-best4-shuffle-preservation-handoff.json')
add(Path(__file__),'preserve_combined_shuffle.py')
(O/'source-bindings.json').write_text(json.dumps(mapping,indent=2)+'\n');add(O/'source-bindings.json','source-bindings.json')
repro={'engine':'review/snapshot/main/circuit_anneal_allnegative_shuffle.cpp','shuffle_control':'review/independent_shuffle.cpp','pack':'dependencies/packs/best3/direct-seeds.txt','parent141':'dependencies/circuit_anneal_allnegative.cpp','parent40':'dependencies/parent40.cpp','shuffle40':'dependencies/circuit_anneal_shuffle.cpp','wrapper':'review/snapshot/wrapper/stochastic_tools_shuffle.py','wrapper_parent':'dependencies/stochastic_tools.py','wrapper_derivation':'review/snapshot/wrapper/stochastic_tools_shuffle.derivation.json','review':'review/review.json','source_sha256':'6717226e0fb1e0ed3a260e23aa0f162d2f8b3591a425798528194878d5f32bf7','binary_sha256':'e67583803d64fcf68d585e58833eb2b9c13b246d420385e2cf0dd8cbac8eac6d','wrapper_sha256':'99c843f9a450c37c1c283d00684015269bd2eca091da3488e8d5811b6d934944'}
(O/'portable-reproduction.json').write_text(json.dumps(repro,indent=2)+'\n');add(O/'portable-reproduction.json','portable-reproduction.json')
verifier=r'''from pathlib import Path
import sys,json,hashlib,difflib
root=Path(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parent)
sha=lambda b:hashlib.sha256(b).hexdigest()
def get(n):
 p=Path(n);assert not p.is_absolute() and '..' not in p.parts
 p=root/p;assert p.is_file() and not p.is_symlink();return p.read_bytes()
m=json.loads(get('manifest.json'));assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(m['files'])|{'manifest.json'}
for n,row in m['files'].items():
 b=get(n);assert len(b)==row['bytes'] and sha(b)==row['sha256'] and not b.startswith(b'\x7fELF')
binding=json.loads(get('source-bindings.json'));r=json.loads(get('review/review.json'))
assert sha(get('review/review.json'))=='5146eb7ac9871706deee49391118489790dfaedd3ad7113a73b9d5e256826de3'
assert set(binding)==set(r['bindings'])
for n,row in r['bindings'].items():
 b=binding[n];assert row['bytes']==b['bytes'] and row['sha256']==b['sha256']
 if b['disposition']=='payload':raw=get(b['archive_path']);assert sha(raw)==row['sha256'] and len(raw)==row['bytes']
 else:assert b['disposition']=='omitted_ELF'
p=json.loads(get('portable-reproduction.json'))
def changes(a,b):
 a=a.decode().splitlines(True);b=b.decode().splitlines(True)
 return [(t,a[i:j],b[k:l]) for t,i,j,k,l in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes() if t!='equal']
assert len(changes(get(p['parent141']),get(p['engine'])))==6
assert changes(get(p['parent141']),get(p['engine']))==changes(get(p['parent40']),get(p['shuffle40']))
s=get(p['wrapper_parent']).decode();d=json.loads(get(p['wrapper_derivation']))
for row in d['changes']:assert s.count(row['before'])==1;s=s.replace(row['before'],row['after'])
assert s.encode()==get(p['wrapper']) and len(d['changes'])==2
assert sha(get(p['engine']))==p['source_sha256'] and sha(get(p['wrapper']))==p['wrapper_sha256']
print(json.dumps({'verdict':'PASS_PORTABLE_HASH_INVENTORY_DIRECT_REVIEW_BINDINGS_AND_EXACT_SOURCE_PORT','payloads':len(m['files']),'review_bindings':len(binding),'engine_blocks':6,'wrapper_insertions':2,'workers_started':False}))
'''
# The standalone verifier must test the ELF marker bytes, not a literal slash sequence.
verifier=verifier.replace("b'\\x7fELF'","b'\x7fELF'")
(O/'verify_package.py').write_text(verifier);add(O/'verify_package.py','verify_package.py')
readme='''Combined141-row engine, optional shuffle and wrapper: frozen independent review

This source/control companion is separate from S02 archive6fa86672bdf0b3eb7e909d995f6d5fda13475c5085187eb759ac32ddd8c6da42, which excludes main's141-row integration and S08's combined review. Preserve that earlier package for S02's full repair-family/40-row-engine provenance. This package preserves the exact integrated141 engine, wrapper, all finite main and S08 control logs/snapshots, inherited wrapper controls, source diffs/parents, and every direct binding of review5146eb7ac9871706deee49391118489790dfaedd3ad7113a73b9d5e256826de3. source-bindings.json maps duplicate evidence to exact payload aliases; executable binaries are omitted with hashes and byte counts.

Engine source6717226e0fb1e0ed3a260e23aa0f162d2f8b3591a425798528194878d5f32bf7, binarye67583803d64fcf68d585e58833eb2b9c13b246d420385e2cf0dd8cbac8eac6d, wrapper99c843f9a450c37c1c283d00684015269bd2eca091da3488e8d5811b6d934944. Six exact S02 engine blocks ported into the reviewed141 parent; two wrapper insertions parse/forward the optional default-off flag. All141 fitness masks/scoring, scalar acceptance and independent validator/lifecycle are unchanged. Flag provenance is command argv; it is not a separate result boolean.

Main1000-DAG controls checked43,008,000 intermediate and2,048,000 output values, plus2,048,000 random scalar/vector comparisons. Independent S08 UBSan264-DAG control checked11,354,112 intermediate truth bits,540,672 output bits,37,224 fitness bits, bijection/liveness/determinism and10 malformed inputs. Three finite301-iteration wrapper controls cross three restart boundaries; default-off results/snapshots match the parent except clock. Enabled snapshots receive independent full2048 evaluation, and the actual new wrapper rejects a deliberately falsely labelled candidate via the unchanged validator. Its expected error traceback and full stdout/stderr are retained.

Only completed finite controls are included. No production output directory or launch/result stream was read for this package. Historical pending/not-launched fields describe the prelaunch snapshots and do not deny later main launches. No exact21 witness, runtime result, performance gain, exhaustive search, Lean proof or posted acceptance is claimed. Generic --self-test returns before shuffle, so the dedicated independent control is the relevant shuffle test.

Extract this archive and run the standard-library verifier from anywhere:
  python -B PATH_TO_EXTRACTED_ROOT/verify_package.py
It checks every payload, every direct review binding, and exact engine/wrapper derivations; it starts no worker and needs no old scratch paths.

For an optional finite C++ replay, from the extracted root, build into a separate output directory so verification inventory remains unchanged:
  g++ -std=c++17 -O1 -g -fsanitize=undefined -fno-sanitize-recover=all -Wall -Wextra -Werror review/independent_shuffle.cpp -o /tmp/oec/pequalnp-pilot-18/orch/S08/replayed-shuffle-control
  /tmp/oec/pequalnp-pilot-18/orch/S08/replayed-shuffle-control dependencies/packs/best3/direct-seeds.txt
The output path must be fresh. This package did not rerun those already completed tests. Rebuilding the optimized engine uses the same C++17/O3/Wall/Wextra/Werror flags and source in review/snapshot/main. Binary identity across different compilers is not promised. Original wrapper/review-driver scripts retain historical absolute workspace paths; logs and the independent C++ test are portable. Parent141 full preservation archiveedfb85398c9f9522470de2e782a75fca862b034e7726b16fcd7216ac7050c6f0 is retained separately.
'''
(O/'README.md').write_text(readme);add(O/'README.md','README.md')
Review('combined-shuffle-preservation-scan').scan(payload)
manifest={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Source/finite-control companion; no production runtime outputs or proof/exhaustion claim.','prefix':'S08-combined-141-shuffle-v1','files':{n:{'bytes':len(b),'sha256':sha(b),'source_path':origins[n]} for n,b in sorted(payload.items())},'omitted_ELF_binaries':omitted,'direct_review_bindings':len(mapping),'active_output_read':False,'solver_or_Lean_run':False}
mb=(json.dumps(manifest,indent=2)+'\n').encode();(O/'manifest.json').write_bytes(mb)
buffer=io.BytesIO()
with gzip.GzipFile(fileobj=buffer,mode='wb',mtime=0,filename='') as gz:
 with tarfile.open(fileobj=gz,mode='w') as tf:
  for n,b in sorted({**payload,'manifest.json':mb}.items()):
   item=tarfile.TarInfo(manifest['prefix']+'/'+n);item.mode=0o644;item.mtime=0;item.size=len(b);tf.addfile(item,io.BytesIO(b))
tar=O/'S08-combined-141-shuffle-v1.tar.gz';tar.write_bytes(buffer.getvalue())
restored={};extract=O/'roundtrip';extract.mkdir(exist_ok=False)
with tarfile.open(tar,'r:gz') as tf:
 for item in tf.getmembers():
  pp=PurePosixPath(item.name);assert item.isfile() and not pp.is_absolute() and '..' not in pp.parts
  n=str(pp.relative_to(manifest['prefix']));assert n not in restored;restored[n]=tf.extractfile(item).read();out=extract/n;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(restored[n])
assert restored=={**payload,'manifest.json':mb}
for n,b in payload.items():assert Path(origins[n]).read_bytes()==b
with (O/'verify.stdout').open('wb') as a,(O/'verify.stderr').open('wb') as b:p=subprocess.run([sys.executable,'-B',str(extract/'verify_package.py')],stdout=a,stderr=b,timeout=15)
assert p.returncode==0,(O/'verify.stderr').read_text()
result={'verdict':'PASS_SOURCE_INVENTORY_HASHES_ROUNDTRIP_AND_PORTABLE_VERIFIER','archive_sha256':sha(tar.read_bytes()),'archive_bytes':tar.stat().st_size,'manifest_sha256':sha(mb),'regular_members':len(restored),'payloads':len(payload),'review_bindings':len(mapping),'omitted_ELF_count':len(omitted),'portable_verifier':json.loads((O/'verify.stdout').read_text()),'verify_exit_code':p.returncode,'active_outputs_read':False,'new_build_solver_checker_Lean_run':False}
(O/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
