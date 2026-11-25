from pathlib import Path
import json
j=Path('/tmp/oec/pequalnp-pilot-79');old=json.loads((j/'meta3773-synthesis-data.json').read_text());rows=old['rows']+[1<<i for i in range(26)]
assert len(rows)==782
nw=(len(rows)+63)//64
inputs=[[sum(((m>>i)&1)<<(k%64)for k,m in enumerate(rows)if k//64==w)for w in range(nw)]for i in range(26)]
text=str(len(rows))+' '+str(nw)+'\n'+'\n'.join(' '.join(map(str,w))for w in inputs)+'\n'
(j/'meta3773-synthesis-singleton-data.txt').write_text(text)
print(json.dumps({'original_rows':len(old['rows']),'singleton_rows':26,'total_rows':len(rows),'words':nw}))
