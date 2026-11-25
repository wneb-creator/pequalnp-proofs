from pathlib import Path
import json,hashlib,shutil,subprocess,sys,struct,collections
S=Path(__file__).resolve().parent;D=Path('/workspace/pequalnp-proofs/results/orch/lemmas');out=S/'fresh-meta3773-five-helper-final-summary.json';err=S/'fresh-meta3773-five-helper-summary-stderr.log'
with out.open('wb')as o,err.open('wb')as e:subprocess.run([sys.executable,str(S/'fresh_meta3773_five_helper_summary.py')],cwd=S,stdout=o,stderr=e,check=True)
j=json.loads(out.read_text());rows=j['strata'];table=[];complete=[]
for m in [31,47,55,62]:
 group=[r for r in rows if r['helper_mask']==m];table.append('| '+str(m)+' | '+' | '.join(str(r['finished_prefix'])+'/'+str(r['orbit_count'])for r in group)+' |');
 if all(r['finished']for r in group):complete.append(m)
cache=[]
for p in sorted(S.glob('fresh-meta3773-five-1-*-deadstates.bin')):
 data=p.read_bytes();off=0;n=0;keys=set()
 while off<len(data):
  if off+2>len(data):break
  sz=struct.unpack('<H',data[off:off+2])[0]
  if off+2+sz>len(data):break
  key=data[off+2:off+2+sz];f,c,h,z,R=struct.unpack('<BBBBH',key[:6]);assert z==0 and 1<=h<=3 and R<1<<13 and 2<=f<=21 and c<=8 and sz==6+8*f+2*c;F=struct.unpack('<'+'Q'*f,key[6:6+8*f]);C=struct.unpack('<'+'H'*c,key[6+8*f:]);assert F==tuple(sorted(F)) and C==tuple(sorted(C)) and all(v<1<<41 for v in F)and all(v<1<<13 for v in C);assert key not in keys;keys.add(key);off+=2+sz;n+=1
 cache.append({'file':p.name,'complete_keys':n,'complete_bytes':off,'trailing_uncommitted_bytes':len(data)-off,'sha256':hashlib.sha256(data).hexdigest()})
(S/'fresh-meta3773-five-helper-suffix-caches.json').write_text(json.dumps({'model_name':'fresh-meta3773-five-point-types.json','model_sha256':hashlib.sha256((S/'fresh-meta3773-five-point-types.json').read_bytes()).hexdigest(),'cache_records':cache},indent=2)+'\n'); note='''# Five-helper strata in the one-triple five-point patch

The model fixes the reduced five-point graph and the seven outside OR features described in `fresh_meta3773_ONE_TRIPLE_HIGH_HELPERS.md`. Five actually used helpers leave an excess read budget of three. Four helper-set orbits remain under the twelve automorphisms of the representative point set `{0,1,2,3,6}`. Mask bits follow the feature order in `fresh-meta3773-five-point-types.json`.

Each table entry gives completed primitive-multiset representatives over the total in that stratum. The columns count extra primitive occurrences. The remaining excess is available for repeated internal gates.

| Helper mask | 0 | 1 | 2 | 3 |
| --- | ---: | ---: | ---: | ---: |
'''+ '\n'.join(table)+'\n\n'+f"The search completed {j['completed_representatives']} of {j['all_representatives']} representatives, across {j['completed_strata']} fully completed strata. "+('It completed every stratum for helper mask'+('s 'if len(complete)>1 else ' ')+', '.join(map(str,complete))+'. ' if complete else '')+'''No completed representative produced a 20-gate reduced circuit. Unfinished prefixes and untouched strata are inconclusive. The table concerns only five-helper replacements of the selected point stars. It supplies a computational diagnostic with no Lean certificate or bound on arbitrary circuits.

`fresh_meta3773_five_helper_summary.py` constructs the automorphisms directly from the line neighborhoods and helper supports and counts multisets under each installed-helper stabilizer. It verifies every completed ordinal against the full stdout/stderr chunk logs. The progress files count completed representatives only. A cone checkpoint inside the next representative records which earlier cones have been visited. The last stored cone is replayed when the search resumes.

The final optimized recurrence retains minimal positive and maximal negative row patterns on the available primitive multiset. Monotonicity implies the discarded obligations. Among duplicate patterns it retains the lowest row index. It also drops tokens always zero on the retained positive rows or always one on the retained negative rows: assigning those tokens their indicated constants preserves every required acceptance or rejection before simplifying the formula. It uses the earlier component splitter up to sixteen components and the earlier multiset recurrence outside that range. The code is independently reviewed, and the 56 direct comparisons, the generated 13–19-token positive controls and the 19-token ordinary star control pass. The preceding 12-component solver remains a way to reproduce each result.

The optional checkpoint wrapper records only complete failed suffixes having at least one unit of internal excess. Each length-prefixed binary record gives the full ordered tuple of primitive truth tables, the raw-vertex mask, sorted possible carrier slots and remaining internal excess. Records use explicit little-endian fixed field widths. The wrapper reuses an exact key only, ignores and truncates an interrupted trailing record, and excludes root states from this cache. The cache inventory validates every complete serialized key and binds each file hash. The cache keys belong to these exact archived row and model conventions. The original checkpoint wrapper and its short-write-checked revision are both preserved. The inventory verifies that the fixed model data hash is `54d3b8cf7a11e73b8e48f37f18952e026c5375475337e9c83ad3bdaaaa4c0d10`. These cache files improve interrupted runs. Starting with empty caches or using the preceding non-checkpointed solver reproduces the same model.

For a fresh run, use the previously archived model inputs and sources from the high-helper packet. Compile `fresh_meta3773_readonce_wide.cpp` and `fresh_meta3773_component_sixteen.cpp` together into `fresh-meta3773-sixteen.so` with `g++ -std=c++17 -O3 -shared -fPIC`. The previously described `fresh-meta3773-readonce-ext.so` is also required. Run `python fresh_meta3773_five_sixteen.py 1 mask dup`, choosing a mask and column from the table. Substitute `fresh_meta3773_five_checkpoint.py` to record complete failed suffix states for reuse following interruptions.
''';(S/'fresh_meta3773_ONE_TRIPLE_FIVE_HELPERS.md').write_text(note)
files='fresh_meta3773_freeze_five.py fresh_meta3773_ONE_TRIPLE_FIVE_HELPERS.md fresh_meta3773_five_helper_summary.py fresh-meta3773-five-helper-final-summary.json fresh-meta3773-five-helper-summary-stderr.log fresh-meta3773-five-helper-suffix-caches.json fresh_meta3773_component_sixteen.cpp fresh_meta3773_five_sixteen.py fresh_meta3773_component_test_sixteen.py fresh_meta3773_component_extended_checks_sixteen.py fresh-meta3773-sixteen-test.log fresh-meta3773-sixteen-test2.log fresh-meta3773-sixteen-build.log fresh_meta3773_five_checkpoint.py fresh_meta3773_five_checkpoint_initial.py fresh_meta3773_five_final_chunks.py fresh-meta3773-five-final-scheduler.log fresh-meta3773-five-final-scheduler-resumed.log'.split();src={S/f for f in files}
for m in [31,47,55,62]:
 for pat in ['*.log','*progress.json','*cone.json','*deadstates.bin']:src.update(S.glob('fresh-meta3773-five-1-'+str(m)+'-'+pat))
art=[]
for p in sorted(src):
 assert p.is_file()and not p.is_symlink();v=p.read_bytes();t=D/p.name;assert not t.exists()or t.read_bytes()==v;shutil.copyfile(p,t);art.append({'file':p.name,'bytes':len(v),'sha256':hashlib.sha256(v).hexdigest()})
q=S/'fresh-meta3773-five-helper-publish.json';q.write_text(json.dumps({'scope':'partially searched one-triple five-helper strata only; incomplete prefixes are inconclusive; no Lean/global claim','files':art},indent=2)+'\n');print('FROZEN',len(art),sum(e['bytes']for e in art),hashlib.sha256(q.read_bytes()).hexdigest(),j['completed_representatives'],j['completed_strata'],complete)
