from pathlib import Path
import json,re,ast,hashlib
base=Path('results/orch9775');src=base/'lemmas/CompactPacking.lean';s=src.read_text();masks=ast.literal_eval(next(l for l in s.splitlines() if l.startswith('def packedMasks')).split(':=')[1]);assert len(masks)==36 and len(set(masks))==36
facts=[('live','vn'),('lab','vnv'),('res','nv'),('common','vv'),('gate','ee'),('reader','ben'),('es','bev'),('avoid','vmn'),('see','vvmn'),('diff','nvv')]
schemes=[('self','vn'),('earlier','vn'),('labCommon','vvn'),('someRes','v'),('allRes','vn'),('exposure','vm'),('exactAt','vvm'),('avoidLive','vmn'),('seeLive','vvmn'),('avoidNot','vvmn'),('seeLab','vvvmn'),('diffX','nvv'),('diffC','nvv'),('adjacentCommon','vvv'),('resCommon','vvn'),('residual','vvnn'),('readerAny','be'),('readerLive','ben'),('readerLab','benvb'),('eqLab','beevb'),('gateEq','been'),('pairedExact','vvvvm')]
def decode(n,table):
 tag=n%32;assert tag<len(table);name,types=table[tag];out=[name]
 assert n>>(5+6*len(types))==0
 for i,t in enumerate(types):
  v=(n>>(5+6*i))&63
  if t=='v':assert v<14
  elif t=='e':assert v<19
  elif t=='b':assert v in [0,1];v=bool(v)
  elif t=='m':assert v<len(masks);v=masks[v]
  out.append(v)
 return out
checks=[]
for p in sorted((base/'search/compact-packed').glob('*.lean')):
 d=json.loads(p.with_suffix('.json').read_text());lines=p.read_text().splitlines();a=next(l for l in lines if l.startswith('def a'));r=next(l for l in lines if l.startswith('def r'))
 av=ast.literal_eval(re.search(r'\(\[(.*?)\] : List Nat\)',a).group(0).split(' : List Nat')[0][1:]);rv=ast.literal_eval(re.search(r'\(\[(.*?)\] : List Nat\)',r).group(0).split(' : List Nat')[0][1:]);assert [decode(n,facts) for n in av]==d['facts'];assert [decode(n,schemes) for n in rv]==d['schemes']
 checks.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'facts':len(av),'schemes':len(rv),'I':d['I'],'k':d['k']})
r={'verdict':'PASS','decoder_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'decoder_bytes':src.stat().st_size,'files':checks,'total_facts':sum(x['facts']for x in checks),'total_schemes':sum(x['schemes']for x in checks),'scope':'Independent bitfield decoder and actual emitted Nat arrays checked against original semantic constructor JSON; kernel certificate checks still required.'};(base/'packing-independent.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items()if k!='files'});print('files',len(checks))
