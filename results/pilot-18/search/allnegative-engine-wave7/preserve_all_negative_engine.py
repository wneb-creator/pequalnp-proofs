from pathlib import Path,PurePosixPath
import sys,json,io,tarfile,gzip,datetime,subprocess
sys.path.insert(0,str(Path(__file__).parent))
from wave5_delivery_helpers import R,W,sha,Review
O=R/'orch/S08/all-negative-engine-preservation-v1';O.mkdir(exist_ok=True)
payload={};sources={};omitted=[]
def add(name,p):
 assert name not in payload
 b=p.read_bytes()
 if b.startswith(b'\x7fELF'):
  omitted.append({'archive_path_if_included':name,'source_path':str(p),'bytes':len(b),'sha256':sha(b),'reason':'Compiled binary excluded; source/build commands/binary hash retained.'});return
 payload[name]=b;sources[name]=str(p)
for group,root in [('review',R/'orch/S08/all-negative-engine-review'),('production-plan-review',R/'orch/S08/all-negative-production-plan-review')]:
 for p in sorted(root.rglob('*')):
  if p.is_file():assert not p.is_symlink();add(group+'/'+str(p.relative_to(root)),p)
for n in ['all-negative-engine-review-run.stdout','all-negative-engine-review-run.stderr','review_all_negative_engine.py','wave5_delivery_helpers.py']:
 add('review-driver/'+n,R/'orch/S08'/n)
for group,root,names in [
 ('dependencies/packs/best3',R/'orch/S05/triangle589-best3-direct21-v1',['direct-seeds.txt','direct-seeds.json']),
 ('dependencies/packs/legacy',R/'orch/S05/dirty22-seed-pack',['seeds.txt','seeds.json']),
 ('dependencies',R,['validate_raw_candidate.py','lean-setup/stochastic/stochastic_tools.py','lean-setup/validate_sat_candidate.py']),
 ('candidate-improvement',R/'orch/MAIN/allnegative-best4',['source.json','scalar-review.json'])]:
 for n in names:add(group+'/'+n,root/n)
add('dependencies/parent-engine-independent-review.json',R/'orch/S08/direct21-engine-review/review.json')
add('preserve_all_negative_engine.py',Path(__file__))
assert sha(payload['review/review.json'])=='23a3c36f8a714214fbe4df4cff142820cfef6d091d9401793f74c255442253c2'
assert sha(payload['production-plan-review/review.json'])=='62f416117e7717595e76c3db9d054f4754d01c5aa1ee25be92f2f1fbd784ba40'
assert sha(payload['review/snapshot/main/circuit_anneal_allnegative.cpp'])=='18efdd149487dfee83693dd0781a17316ba0fda9d68c43c6c70c73f96a77250b'
assert len(omitted)==3
# Bind only the immutable, explicitly authorized partial candidate, not its active run directory.
b=payload['candidate-improvement/source.json'];assert sha(b)=='b6da8ac6962d7836f2e5546423f5ed3846b7165fbe1ae47e58b8e470955101b0'
c=json.loads(b);m=json.loads(payload['candidate-improvement/scalar-review.json'])
assert c['status']=='BEST_PARTIAL_NOT_A_WITNESS' and c['fitness_domain']=='16_edges_plus_all_125_negative_inputs' and c['size']==21 and c['gate_wire_offset']==13
edges=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
fn=[];fp=[];boundary=[]
for x in range(2048):
 w=[bool(x>>i&1) for i in range(11)]+[False,True]
 for op,a,b in c['gates']:
  assert op in ['and','or'] and 0<=a<len(w) and 0<=b<len(w)
  w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
 target=any(x>>a&1 and x>>b&1 for a,b in edges);out=w[c['output']]
 assert out==(target or (x&21)==21)
 if target and not out:fn.append(x)
 if not target and out:
  fp.append(x)
  if all((x>>v&1) or any((x|(1<<v))>>a&1 and (x|(1<<v))>>b&1 for a,b in edges) for v in range(11)):boundary.append(x)
live=set();todo=[c['output']]
while todo:
 wire=todo.pop()
 if wire>=13 and wire not in live:live.add(wire);todo.extend(c['gates'][wire-13][1:])
assert fn==[] and fp==[21,29,85,149] and boundary==[29,85,149] and len(live)==21
assert m['source_sha256']==sha(payload['candidate-improvement/source.json']) and m['false_negatives']==fn and m['false_positives']==fp and m['minimal_extras']==[21] and m['exact_target'] is False
cr={'verdict':'PASS_INDEPENDENT_FULL2048_INEXACT_BEST4','source_sha256':sha(payload['candidate-improvement/source.json']),'main_review_sha256':sha(payload['candidate-improvement/scalar-review.json']),'full_input_checks':2048,'false_negatives':fn,'false_positives':fp,'minimal_extras':[21],'boundary_false_positives':boundary,'live_gates':len(live),'function':'F OR (x0 AND x2 AND x4)','exact_target':False,'scope':'Immutable snapshot only. No active run output read or final production result inferred.'}
(O/'best4-independent-review.json').write_text(json.dumps(cr,indent=2)+'\n');add('candidate-improvement/S08-independent-review.json',O/'best4-independent-review.json')
readme='''Frozen 141-row candidate engine and independent review

Source SHA256 18efdd149487dfee83693dd0781a17316ba0fda9d68c43c6c70c73f96a77250b.
Reviewed optimized binary SHA256 7d802a63b218449bd58178785a917a363edecedace5f65201344804dec3a3870.
Independent review 23a3c36f8a714214fbe4df4cff142820cfef6d091d9401793f74c255442253c2.
Production-plan review 62f416117e7717595e76c3db9d054f4754d01c5aa1ee25be92f2f1fbd784ba40.

The archive includes current/parent C++ sources and exact diff; original build and all finite main/S08 control logs; source and metadata for both seed packs; unchanged wrapper, raw validator and normalizer; full hash-bound reviews; and prelaunch plan. Three ELF binaries are omitted with sizes/hashes in the manifest; their source and build commands remain. Compiler output does not imply portable byte-identical binaries on other toolchains. The historical main-review says independent review pending and production not launched: these fields describe its frozen prelaunch time and are superseded by the S08 review and later main launch, respectively.

The sole production-derived addition is the explicitly supplied immutable best4 snapshot b6da8ac6962d7836f2e5546423f5ed3846b7165fbe1ae47e58b8e470955101b0 and both scalar reviews. Independent 2048-input evaluation gives zero FN and FP [21,29,85,149], exactly F OR (x0 AND x2 AND x4), 21 live gates. It remains inexact. No active worker directory, evolving log, or final production result is included or inferred. Main's one-iteration control is UNKNOWN; deliberately false-candidate control is expected ERROR/validator exit2 and its full traceback is retained.

Fitness uses 16 minimal positive edges plus all125 negative inputs. Zero edge-FN/full-FP is equivalent to exactness for valid monotone gates; the unchanged engine and independent validator still check all2048 inputs before accepting a candidate. FN is edge-only, FP is now full-negative count, and energy includes the live-gate fraction. Main evidence includes2,048,000 scalar comparisons; S08 independently tested1,073,152 scalar inputs underUBSan plus word/mask/operator boundaries, weighted scores, four exact22 controls, the exact binary's finite selftest and actual wrapper rejection. No performance guarantee, exhaustive search, exact21 witness, Lean theorem or posted acceptance is claimed.

Finite source-control reproduction after extracting this archive, from its root:
  mkdir rebuild
  g++ -std=c++17 -O1 -g -fsanitize=undefined -fno-sanitize-recover=all -Wall -Wextra -Werror review/independent_review_controls.cpp -o rebuild/independent_review_controls
  rebuild/independent_review_controls dependencies/packs/best3/direct-seeds.txt dependencies/packs/legacy/seeds.txt
  g++ -std=c++17 -O3 -Wall -Wextra -Werror review/snapshot/main/circuit_anneal_allnegative.cpp -o rebuild/circuit_anneal_allnegative
  rebuild/circuit_anneal_allnegative --pack dependencies/packs/best3/direct-seeds.txt --output rebuild/selftest.json --seed134231 --self-test
The final selftest option must be written as two tokens: --seed 134231. Only finite selftests are shown; production commands are historical evidence and are not reproduction steps. Original wrapper/controller commands retain their absolute workspace paths. The independent C++ control above is portable within the extracted directory tree. Archive verification hashes all payloads; it does not execute commands.
'''.replace('--seed134231','--seed 134231').replace('The final selftest option must be written as two tokens: --seed 134231. ','')
(O/'README.md').write_text(readme);add('README.md',O/'README.md')
# Bind compiler identity without compiling or executing another control.
with (O/'compiler-version.stdout').open('wb') as out,(O/'compiler-version.stderr').open('wb') as err:
 cp=subprocess.run(['g++','--version'],stdout=out,stderr=err,timeout=5)
assert cp.returncode==0
for n in ['compiler-version.stdout','compiler-version.stderr']:add('toolchain/'+n,O/n)
Review('all-negative-engine-preservation-scan').scan(payload)
manifest={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Frozen engine/controls/reviews and one explicitly immutable inexact best4 snapshot; no active runtime outputs.','prefix':'S08-all-negative-engine-v1','files':[{'path':n,'bytes':len(b),'sha256':sha(b),'source_path':sources[n]} for n,b in sorted(payload.items())],'omitted_ELF_binaries':omitted,'active_outputs_read':False,'exact21_found':False,'compiled_Lean_or_posted_checker_run':False}
mb=(json.dumps(manifest,indent=2)+'\n').encode();(O/'manifest.json').write_bytes(mb)
raw=io.BytesIO()
with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0,filename='') as gz:
 with tarfile.open(fileobj=gz,mode='w') as tf:
  for name,data in sorted({**payload,'manifest.json':mb}.items()):
   info=tarfile.TarInfo(manifest['prefix']+'/'+name);info.size=len(data);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(data))
tar=O/'S08-all-negative-engine-v1.tar.gz';tar.write_bytes(raw.getvalue())
restored={}
with tarfile.open(tar,'r:gz') as tf:
 for member in tf.getmembers():
  path=PurePosixPath(member.name);assert member.isfile() and not path.is_absolute() and '..' not in path.parts
  rel=str(path.relative_to(manifest['prefix']));assert rel not in restored;restored[rel]=tf.extractfile(member).read()
assert restored=={**payload,'manifest.json':mb}
for row in manifest['files']:
 assert Path(row['source_path']).read_bytes()==restored[row['path']]
for row in omitted:assert sha(Path(row['source_path']).read_bytes())==row['sha256']
validation={'verdict':'PASS_REGULAR_ARCHIVE_EXACT_INVENTORY_HASHES_AND_SOURCE_ROUNDTRIP','archive':str(tar),'archive_sha256':sha(tar.read_bytes()),'archive_bytes':tar.stat().st_size,'manifest_sha256':sha(mb),'regular_members':len(restored),'payloads':len(payload),'source_copies':len(sources),'omitted_ELF_count':len(omitted),'best4_independent_all_inputs':2048,'runtime_outputs_included':'Only explicitly supplied immutable best4 snapshot; no active directories read.','solver_production_or_Lean_run':False}
(O/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
print(json.dumps(validation,indent=2))
