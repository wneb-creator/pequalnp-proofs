from pathlib import Path
import re,json,ast,hashlib,time
BASE=Path('/tmp/oec/pequalnp-pilot-10')
HERE=BASE/'fresh-full-proof/meta984'
OUT=BASE/'independent-search/984'
started=time.monotonic()
def definitions(text):
 return {re.match(r'def (\w+)',p).group(1):p for p in re.split(r'(?m)(?=^def )',text) if p.startswith('def ')}
def natlist(defn):return ast.literal_eval(defn.split(':=',1)[1].strip().replace('#[','['))
def nat(defn):return int(defn.split(':=',1)[1].strip(),0)
def cases(defn):
 return {int(a):int(b,0) for a,b in re.findall(r'\| (\d+) => (0x[0-9a-f]+|\d+)',defn)}
def field(x,width,index):return (x>>(width*index))&((1<<width)-1)
shared_path=HERE/'benes-compact/shared.fragment.lean'
shared=definitions(shared_path.read_text());pool=natlist(shared['bPool'])
expand_stages=[(int(d),int(shift),int(mask,0)) for d,shift,mask in re.findall(r'if d ≤ (\d+) then \(x \|\|\| \(x <<< (\d+)\)\) &&& (0x[0-9a-f]+)',shared['bExpand'])]
assert len(expand_stages)==7 and all(a==b for a,b,_ in expand_stages)
maskbits=int(re.search(r'fld codes (\d+)',shared['bMasks']).group(1))
def expand(x,d):
 for threshold,shift,mask in expand_stages:
  if d<=threshold:x=(x|(x<<shift))&mask
 return x
def route(w,masks,distances):
 for mask,d in zip(masks,distances):
  swap=((w>>d)^w)&mask
  w=w^swap^(swap<<d)
 return w
records=[];totalstates=0;totalstages=0
hashes={str(shared_path.relative_to(BASE)):hashlib.sha256(shared_path.read_bytes()).hexdigest()}
for graph in range(31):
 path=HERE/f'fast31_v2/G{graph}.data.fragment.lean';text=path.read_text();ds=definitions(text)
 hashes[str(path.relative_to(BASE))]=hashlib.sha256(path.read_bytes()).hexdigest()
 old=definitions((HERE/f'fast31/G{graph}.data.fragment.lean').read_text())
 name=f'G{graph}'
 N=cases(ds[name+'_N']);pbs=cases(ds[name+'_pb']);packed=cases(ds[name+'_records'])
 # v2 may remove only CHD cases at empty layers, and must preserve all active-layer data.
 for suffix in ['N','pb','records','initial','benes','act','S','actions','ori','coords','rankPool','Z','idx']:
  assert ds[name+'_'+suffix]==old[name+'_'+suffix],(graph,suffix)
 for suffix in ['buckets','flag','seedBits','seeds']:
  assert {s:v for s,v in cases(old[name+'_'+suffix]).items() if N.get(s,0)>0}==cases(ds[name+'_'+suffix]),(graph,suffix)
 meta=json.loads((BASE/f'proof-strategy/meta984/quotient{graph}.meta.json').read_text())
 routes=json.loads((BASE/f'independent-theory/meta984/benes/routes{graph}.json').read_text())
 cap,stride,ob,pairpack,mb,ab=re.search(r'qParentAction (\d+) (\d+) (\d+) (0x[0-9a-f]+) (\d+) (\d+)',ds[name+'_S']).groups()
 cap,stride,ob,mb,ab=map(int,[cap,stride,ob,mb,ab]);pairpack=int(pairpack,0)
 k=meta['k'];initial=natlist(ds[name+'_initial']);netpack=nat(ds[name+'_benes'])
 assert initial==sorted(int(w,16) for w in meta['inputs_hex'])
 masks=[]
 for auto,network in enumerate(routes['networks']):
  decoded=[]
  for j,d in enumerate(routes['distances']):
   index=field(netpack,maskbits,15*auto+j);assert index<len(pool)
   val=expand(pool[index],d);assert val==int(network['lo_hex'][j],16)
   decoded.append(val);totalstages+=1
  inv=meta['row_inverse_perms'][auto]
  expected_sources=inv+[k+x for x in inv]+list(range(2*k,256))
  for dest,src in enumerate(expected_sources):
   assert route(1<<src,decoded,routes['distances'])==1<<dest
  assert route(((1<<k)-1)<<k,decoded,routes['distances'])==((1<<k)-1)<<k
  masks.append(decoded)
 assert all(x==0 for x in masks[0])
 group=len(masks)
 assert int(re.search(r'List.range (\d+)',ds[name+'_actions']).group(1))==group-1
 fast=json.loads((OUT/f'fast_pool_{graph}.json').read_text())
 assert natlist(ds[name+'_coords'])==fast['coordinate_array']
 assert natlist(ds[name+'_rankPool'])==fast['rank_codes']
 assert re.search(r'G'+str(graph)+r'_coords (\d+) G'+str(graph)+r'_rankPool',ds[name+'_Z']).group(1)==str(fast['rank_width'])
 decoded_layers={cap:[tuple(initial)]}
 buckets=cases(ds[name+'_buckets']);flags=cases(ds[name+'_flag']);seedbits=cases(ds[name+'_seedBits']);seeds=cases(ds[name+'_seeds'])
 def get_index(s,ws):
  p=11400714819323198549
  h=sum(pow(w%p+317,3,p)+1 for w in ws)%4294967291
  code=field(seeds.get(s,0),seedbits.get(s,0),h%buckets[s])
  return code-flags[s] if code>=flags[s] else pow(h+code+317,3,p)%N[s]
 for s in range(cap,-1,-1):
  if s<cap:
   rows=[]
   for j in range(N.get(s,0)):
    record=field(packed.get(s,0),pbs.get(s,0)+mb+ab,j)
    parent=record&((1<<pbs.get(s,0))-1)
    code=field(record,mb,1) if False else (record>>pbs.get(s,0))&((1<<mb)-1)
    auto=record>>(pbs.get(s,0)+mb)
    assert parent<len(decoded_layers[s+1]) and auto<group
    ws=list(decoded_layers[s+1][parent])
    if code==0:raw=ws
    elif code<=stride:
     assert code-1<len(ws);raw=[ws[code-1]]+ws
    else:
     q=code-stride-1;pair=field(pairpack,2*ob,q//8);a=pair&((1<<ob)-1);b=pair>>ob
     assert a<b<len(ws)
     gate=(ws[a]&ws[b]) if (q//4)%2==0 else (ws[a]|ws[b])
     raw=[gate]+([ws[a]] if q%2 else [])+([ws[b]] if (q//2)%2 else [])+[w for z,w in enumerate(ws) if z!=a and z!=b]
    rows.append(tuple(sorted(route(w,masks[auto],routes['distances']) for w in raw)) if auto else tuple(sorted(raw)))
   decoded_layers[s]=rows
  original_path=BASE/f'proof-strategy/meta984/quotient{graph}.layer{s}.jsonl'
  original=[tuple(int(w,16) for w in json.loads(line)) for line in original_path.read_text().splitlines()]
  assert len(original)==N.get(s,0)==len(decoded_layers[s]),(graph,s,'count')
  assert len(set(decoded_layers[s]))==len(original) and set(decoded_layers[s])==set(original),(graph,s,'state')
  for j,ws in enumerate(decoded_layers[s]):assert get_index(s,ws)==j,(graph,s,j,'CHD')
 totalstates+=sum(N.values())
 record={'graph':graph,'states':sum(N.values()),'autos':group,'stages':15*group,'data_sha256':hashes[str(path.relative_to(BASE))]}
 records.append(record);print(json.dumps(record),flush=True)
result={'verdict':'PASS','scope':'Independent computational agreement of all31 compact Fast+Benes data fragments with original quotient states, row maps, fast score pools, and CHD indices. No full Lean proof claimed.','graphs':31,'states':totalstates,'mask_stages':totalstages,'permutation_basis_checks':sum(x['autos'] for x in records)*256,'seconds':time.monotonic()-started,'records':records,'source_hashes':hashes}
(OUT/'fast_benes_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['records','source_hashes']}),flush=True)
