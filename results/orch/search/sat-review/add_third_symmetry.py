import argparse
import hashlib
import json
from itertools import combinations_with_replacement
from pathlib import Path

parser=argparse.ArgumentParser(description='Append verified third-gate stabilizer clauses without changing the input CNF.')
parser.add_argument('cnf')
parser.add_argument('mapping')
parser.add_argument('output')
parser.add_argument('--certificate',default='/tmp/oec/pequalnp-pilot-70/sat-review/third-symmetry-certificate.json')
args=parser.parse_args()
source=Path(args.cnf);mapping_path=Path(args.mapping);output=Path(args.output)
if source.resolve()==output.resolve() or mapping_path.resolve()==output.with_suffix('.map.json').resolve():
 raise SystemExit('Output must be separate from the source files')
meta=json.loads(mapping_path.read_text())
cert_path=Path(args.certificate);cert_bytes=cert_path.read_bytes();cert=json.loads(cert_bytes)
assert isinstance(meta,dict) and isinstance(cert,dict)
assert 'prefix' in meta
if meta['prefix'] is not None:
 raise SystemExit('Third-gate symmetry requires a global-prefix instance; fixed-prefix completeness is not certified')
assert meta['ninputs']==14 and meta['edges']==cert['edges']
assert meta['gates']>=3 and len(meta['structure'])==meta['gates']
assert not meta.get('third_stabilizer_symmetry')
structure=meta['structure']
for i,g in enumerate(structure):
 assert len(g['left'])==len(g['right'])==14+i
 assert all(isinstance(v,int) and 0<v<=meta['nv'] for v in g['left']+g['right']+[g['op']])
first,second,third=structure[:3]
edge_set={frozenset(e) for e in cert['edges']}
autos=cert['automorphisms']
for p in autos:
 assert sorted(p)==list(range(14))
 assert {frozenset((p[a],p[b])) for a,b in cert['edges']}==edge_set
pairs=list(combinations_with_replacement(range(16),2))
def act(p,pair):return tuple(sorted(p[x] if x<14 else x for x in pair))
extra=[]
for record in cert['prefixes']:
 f=tuple(record['first']);s=tuple(record['second'])
 assert f[0]==0 and 0<f[1]<14 and 0<=s[0]<s[1]<15
 stabilizer=[i for i,p in enumerate(autos) if act(p,f)==f and act(p,s)==s]
 assert stabilizer==record['stabilizer_indices']
 forbidden=[pair for pair in pairs if min(act(autos[i],pair) for i in stabilizer)!=pair]
 assert forbidden==list(map(tuple,record['forbidden_pairs']))
 for a,b in forbidden:
  extra.append([-first['left'][0],-first['right'][f[1]],-second['left'][s[0]],-second['right'][s[1]],-third['left'][a],-third['right'][b]])
assert len(extra)==cert['additional_clauses']
with source.open() as src:
 header=src.readline().split()
 assert len(header)==4 and header[:2]==['p','cnf']
 variables,count=map(int,header[2:]);assert variables==meta['nv'] and count==meta['clauses']
 with output.open('w') as dst:
  dst.write(f'p cnf {variables} {count+len(extra)}\n')
  actual=0
  for line in src:
   tokens=list(map(int,line.split()))
   assert tokens and tokens[-1]==0 and all(0<abs(v)<=variables for v in tokens[:-1])
   dst.write(line if line.endswith('\n') else line+'\n');actual+=1
  assert actual==count
  for c in extra:dst.write(' '.join(map(str,c))+' 0\n')
meta['clauses']=count+len(extra)
meta['third_stabilizer_symmetry']={'version':1,'scope':'joint global normal form over all canonical prefixes','added_clauses':len(extra),'certificate_sha256':hashlib.sha256(cert_bytes).hexdigest()}
output.with_suffix('.map.json').write_text(json.dumps(meta,separators=(',',':'))+'\n')
print(json.dumps({'source':str(source),'output':str(output),'variables':variables,'base_clauses':count,'added_clauses':len(extra),'clauses':count+len(extra)}))
