from pathlib import Path
import json,re,hashlib
p=Path('/tmp/oec/pequalnp-pilot-14');d=json.loads((p/'status-review'/'Data414.json').read_text());pairs=d['pairs'];subset=[i for i,(x,y)in enumerate(pairs)if x>>4&1 and y>>4&1];assert len(subset)==94
sel=[subset[i%94]for i in range(252)];raw=[]
for v in range(9):
 vals=[sum(((pairs[j][side]>>v)&1)<<i for i,j in enumerate(sel))for side in range(2)];raw.append(vals)
s=(p/'toolchain'/'SlimCompact1007.lean').read_text();old={int(i):(int(a,0),int(b,0))for i,a,b in re.findall(r'def raw(\d+) : Sig := \((0x[0-9a-f]+), (0x[0-9a-f]+)\)',s)};j=next(j for j in range(158)if all(any(((x>>j)^(x>>(j+94)))&1 for x in old[i])for i in[0,3,5,6]));print('duplicate witness',j,j+94,'rows',len(subset))
out={'pairs':[pairs[i]for i in subset],'indices':subset,'selector':sel,'raw':[[hex(a),hex(b)]for a,b in raw],'duplicate':[j,j+94]};(p/'lower-bound'/'PositiveData.json').write_text(json.dumps(out,indent=2))
lines=['namespace PEqualNP.Outside.L_meta_670_aux.PositiveBase','open Base1007']
for i,(a,b)in enumerate(raw):
 if i!=4:lines.append(f'def input{i} : Sig := ({hex(a)}, {hex(b)})')
lines.append('def inputs : List Sig := ['+','.join(f'input{i}'for i in range(9)if i!=4)+']')
lines.append(f'def good (a : Sig) : Prop := a.1.getLsbD {j} = a.1.getLsbD {j+94} ∧ a.2.getLsbD {j} = a.2.getLsbD {j+94}')
lines.append('end PEqualNP.Outside.L_meta_670_aux.PositiveBase')
(p/'lower-bound'/'PositiveDataBody.lean').write_text('\n'.join(lines)+'\n')
