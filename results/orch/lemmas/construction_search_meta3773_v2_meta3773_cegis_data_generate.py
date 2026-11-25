from pathlib import Path
import json,sys
j=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9}
pos=[(1<<p)|(1<<(13+l))for p in range(13)for l in range(13)if(p+l)%13 in D]
singles=[1<<i for i in range(26)]
pairs=[(1<<a)|(1<<b)for a in range(26)for b in range(a+1,26)if not(a<13<=b and(a+b-13)%13 in D)]
assert(len(pos),len(singles),len(pairs))==(52,26,273)
extra=[]
if len(sys.argv)>1:extra=json.loads((j/sys.argv[1]).read_text())['counterexamples']
assert len(set(extra))==len(extra)
rows=pos+singles+pairs+extra;nw=(len(rows)+63)//64
inputs=[[sum(((m>>i)&1)<<(k%64)for k,m in enumerate(rows)if k//64==w)for w in range(nw)]for i in range(26)]
text=str(len(rows))+' '+str(nw)+' 52 52 351\n'+'\n'.join(' '.join(map(str,w))for w in inputs)+'\n'
(j/'meta3773-synthesis-cegis-data.txt').write_text(text)
(j/'meta3773-synthesis-cegis-rows.json').write_text(json.dumps({'positive':pos,'sparse_negative':singles+pairs,'counterexamples':extra,'rows':rows},indent=2)+'\n')
print(json.dumps({'positive':52,'singleton_negative':26,'pair_negative':273,'counterexamples':len(extra),'total':len(rows),'words':nw,'scope':'ABSTRACT until all808 original tests pass independently'}))
