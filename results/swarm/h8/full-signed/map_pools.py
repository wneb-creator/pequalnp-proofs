"""Map native deduplicated pool IDs to checked Lean source columns and rows."""
import argparse
import ast
import hashlib
import json
import re
import struct
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', required=True, type=Path)
parser.add_argument('--metadata', required=True, type=Path)
parser.add_argument('--pools', required=True, type=Path)
parser.add_argument('--cofactors', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
args.output.mkdir(parents=True,exist_ok=True)
meta = json.loads(args.metadata.read_text())
cofactors = json.loads(args.cofactors.read_text())
coords = cofactors['extended_input_coordinates']
assert coords == [9,7,5,8,6,4,2,0,3,1]
for v,iso in enumerate(meta['isomorphisms']):
    item = cofactors['maps'][v]
    assert item['fixed_original_vertex'] == v
    assert item['h9_to_original'] == iso[:9]
    assert item['extended_bit_positions'] == [coords[i] for i in iso[:9]]

def source(file,name):
    text=(args.repo/'lean/PEqualNP/Outside'/file).read_text()
    return ast.literal_eval(re.search(r'^def '+name+r'[^\n]*:= (.+)$',text,re.M).group(1))

cols0=source('L_meta_670.lean','sgC')
cols1=source('L_meta_6581.lean','rootSCols')
assert len(cols0)==106 and len(cols1)==215
cols=list(dict.fromkeys(cols0+cols1))
assert len(cols)==321
raw=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
full=(1<<1024)-1
unique={}
for item in meta['metadata']:
    v=item['vertex']
    iso=item['isomorphism']
    if item['column']=='whole-signed-H9':
        sourcecode=2
        sourceindex=0
        zero=1<<v
        one=0
        z=0
    else:
        col=tuple(item['source'])
        assert col==cols[item['column']]
        z,o,q,s,bound=col
        sourcecode=1 if col in cols1 else 0
        sourceindex=(cols1 if sourcecode else cols0).index(col)
        zero=item['zero']
        one=item['one']
    domain=sum(1<<r for r in range(1024) if not(r&zero) and r&one==one)
    bank={0,domain}|{w&domain for w in raw}
    if z//512:
        t=z//512-1
        a,b=raw[iso[t//9%9]],raw[iso[t%9]]
        extra=(a&b) if t//81==0 else (a|b) if t//81==1 else (a&~b) if t//81==2 else (~a&b)
        bank.add(extra&domain)
    bank|={domain^w for w in list(bank)}
    key=(domain,tuple(sorted(bank)))
    candidate=[v,sourcecode,sourceindex,item['bound'],zero,one]
    if key not in unique or candidate[3]>unique[key][3] or (candidate[3]==unique[key][3] and candidate[1]>unique[key][1]):
        unique[key]=candidate

blob=args.pools.read_bytes()
offset=4
assert struct.unpack_from('<I',blob)[0]==len(unique)==1185
records=[]
for domain,bank in unique:
    native_domain=int.from_bytes(blob[offset:offset+128],'little')
    bound,n=struct.unpack_from('<II',blob,offset+128)
    offset+=136
    native_bank=tuple(int.from_bytes(blob[offset+128*j:offset+128*(j+1)],'little') for j in range(n))
    offset+=128*n
    assert (native_domain,native_bank)==(domain,bank)
    assert bound==unique[domain,bank][3]
    records.append(unique[domain,bank])
assert offset==len(blob)
result=dict(schema=['vertex','source_code','source_index','bound','zero_mask','one_mask'],
            sources={'0':'L_meta_670.sgC','1':'L_meta_6581.rootSCols','2':'L_meta_6581.nineFloor'},
            source_indices='zero-based; whole source_index 0',
            pools_sha256=hashlib.sha256(blob).hexdigest(),
            isomorphisms=meta['isomorphisms'],records=records)
(args.output/'native-pool-map.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
permutation=[sum(((row>>i)&1)<<coords[i] for i in range(10)) for row in range(1024)]
inverse=[0]*1024
for r,s in enumerate(permutation):inverse[s]=r
assert len(set(permutation))==1024
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
for r,s in enumerate(permutation):
    assert all(bool(r>>i&1)==bool(s>>coords[i]&1) for i in range(10))
    assert any(r>>a&1 and r>>b&1 for a,b in edges)==any(s>>coords[a]&1 and s>>coords[b]&1 for a,b in edges)
(args.output/'native-extended-row-permutation.json').write_text(json.dumps(dict(pin_bit_positions=coords,standard_to_extended=permutation,extended_to_standard=inverse),separators=(',',':'))+'\n')
print(json.dumps(dict(status='PASS',pools=len(records),source_counts={str(i):sum(r[1]==i for r in records) for i in range(3)},pool_sha256=result['pools_sha256'])))
