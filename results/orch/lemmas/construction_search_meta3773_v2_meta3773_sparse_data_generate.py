from pathlib import Path
import json
j=Path('/tmp/oec/pequalnp-pilot-79');old=json.loads((j/'meta3773-synthesis-data.json').read_text());D={0,1,3,9}
pairs=[(1<<a)|(1<<b)for a in range(26)for b in range(a+1,26)if not(a<13<=b and(a+b-13)%13 in D)]
assert len(pairs)==273
rows=old['rows']+[1<<i for i in range(26)]+pairs;assert len(rows)==1055;nw=(len(rows)+63)//64
inputs=[[sum(((m>>i)&1)<<(k%64)for k,m in enumerate(rows)if k//64==w)for w in range(nw)]for i in range(26)]
text=str(len(rows))+' '+str(nw)+'\n'+'\n'.join(' '.join(map(str,w))for w in inputs)+'\n'
(j/'meta3773-synthesis-sparse-data.txt').write_text(text)
print(json.dumps({'original_rows':len(old['rows']),'singleton_rows':26,'nonedge_pair_rows':len(pairs),'total_rows':len(rows),'words':nw}))
