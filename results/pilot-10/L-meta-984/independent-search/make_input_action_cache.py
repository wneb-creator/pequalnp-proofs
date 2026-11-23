from pathlib import Path
import json,re,hashlib
BASE=Path('/tmp/oec/pequalnp-pilot-10')
OUT=BASE/'independent-search/984'
summary=[]
for graph in range(31):
 mp=BASE/f'proof-strategy/meta984/quotient{graph}.meta.json'
 rp=BASE/f'independent-theory/meta984/benes/routes{graph}.json'
 source=BASE/f'fresh-full-proof/meta984/fast31_v2/G{graph}.data.fragment.lean'
 meta=json.loads(mp.read_text());routes=json.loads(rp.read_text());k=meta['k']
 keys=sorted(int(w,16) for w in meta['inputs_hex'])
 assert len(set(keys))==len(keys)<=8
 parsed=[int(x.strip(),0) for x in re.search(r'def G'+str(graph)+r'_initial : List Nat := \[([^]]*)\]',source.read_text()).group(1).split(',')]
 assert parsed==keys
 permutations=[];codes=[]
 for auto, inv in enumerate(meta['row_inverse_perms']):
  mapping=inv+[k+x for x in inv]
  values=[sum(((w>>s)&1)<<d for d,s in enumerate(mapping)) for w in keys]
  indices=[keys.index(v) for v in values]
  assert sorted(indices)==list(range(len(keys)))
  for w,want in zip(keys,values):
   actual=w
   for distance,h in zip(routes['distances'],routes['networks'][auto]['lo_hex']):
    lo=int(h,16)
    swap=((actual>>distance)^actual)&lo
    actual=actual^swap^(swap<<distance)
   assert actual==want
  code=sum(index<<(3*j) for j,index in enumerate(indices))
  assert [((code>>(3*j))&7) for j in range(len(keys))]==indices
  permutations.append(indices);codes.append(code)
 assert permutations[0]==list(range(len(keys)))
 packed=sum(code<<(3*len(keys)*a) for a,code in enumerate(codes))
 result={'graph':graph,'keys_hex':[hex(x) for x in keys],'key_count':len(keys),'index_bits':3,'auto_code_bits':3*len(keys),'permutations':permutations,'auto_codes':codes,'packed_auto_codes_hex':hex(packed),'meta_sha256':hashlib.sha256(mp.read_bytes()).hexdigest(),'routes_sha256':hashlib.sha256(rp.read_bytes()).hexdigest(),'validation':'Every cache value equals the original row-inverse permutation action and independently evaluated Benes XOR stages. Keys exactly match emitted G_initial.'}
 (OUT/f'input_action_cache_{graph}.json').write_text(json.dumps(result,indent=2)+'\n')
 (OUT/f'input_action_cache_{graph}.fragment.lean').write_text(f'def G{graph}_inputActions : Nat := {hex(packed)}\n')
 summary.append({'graph':graph,'keys':len(keys),'autos':len(codes),'literal_bytes':len(hex(packed))})
print(json.dumps({'graphs':31,'autos':sum(x['autos'] for x in summary),'literal_bytes':sum(x['literal_bytes'] for x in summary),'total_key_values_checked':sum(x['autos']*x['keys'] for x in summary),'scope':'Computational cache-data agreement only; generic cached-action theorem and concrete Lean checks supplied separately.'}))
(OUT/'input_action_cache_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
