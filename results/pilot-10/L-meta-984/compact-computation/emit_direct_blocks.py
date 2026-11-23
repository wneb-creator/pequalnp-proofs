from pathlib import Path
import json,re,hashlib
BASE=Path('/tmp/oec/pequalnp-pilot-10/independent-search/984')
SRC=BASE/'direct_v2';OUT=BASE/'direct_v3';OUT.mkdir(exist_ok=True)
BLOCK=256
(OUT/'helpers.fragment.lean').write_text((SRC/'helpers.fragment.lean').read_text())
summary=[]
for graph in [28]+[i for i in range(31) if i!=28]:
 name=f'C{graph}';data=json.loads((SRC/f'{name}.data.json').read_text())
 newrecords=f'def {name}_records : Nat → List Nat\n'
 for s,l in sorted(data['layers'].items(),key=lambda p:int(p[0])):
  records=int(l['records'],0);width=l['recordBits'];count=l['N']
  blocks=[(records>>(width*j))&((1<<(width*min(BLOCK,count-j)))-1) for j in range(0,count,BLOCK)]
  for j in range(count):
   assert ((blocks[j//BLOCK]>>(width*(j%BLOCK)))&((1<<width)-1))==((records>>(width*j))&((1<<width)-1))
  l['record_blocks_hex']=[hex(x) for x in blocks]
  newrecords+=f'  | {s} => ['+', '.join(hex(x) for x in blocks)+']\n'
 newrecords+='  | _ => []\n\n'
 text=(SRC/f'{name}.data.fragment.lean').read_text()
 text,count=re.subn(r'(?ms)^def '+name+r'_records : Nat → Nat\n.*?(?=^def )',lambda _:newrecords,text)
 assert count==1
 old=f'(fld ({name}_records s) ({name}_recordBits s) j)'
 new=f'(fld (({name}_records s).getD (j / {BLOCK}) 0) ({name}_recordBits s) (j % {BLOCK}))'
 assert text.count(old)==1;text=text.replace(old,new)
 path=OUT/f'{name}.data.fragment.lean';path.write_text(text)
 data['record_block_size']=BLOCK
 (OUT/f'{name}.data.json').write_text(json.dumps(data,indent=2)+'\n')
 for suffix in ['aux.fragment.lean','decoder.fragment.lean']:(OUT/f'{name}.{suffix}').write_text((SRC/f'{name}.{suffix}').read_text())
 summary.append({'graph':graph,'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest(),'block_size':BLOCK,'states':sum(x['N'] for x in data['layers'].values())})
 print(json.dumps(summary[-1]),flush=True)
(OUT/'summary.json').write_text(json.dumps(sorted(summary,key=lambda x:x['graph']),indent=2)+'\n')
print(json.dumps({'status':'PASS','total_data_bytes':sum(x['bytes'] for x in summary),'block_size':BLOCK,'states':sum(x['states'] for x in summary)}),flush=True)
