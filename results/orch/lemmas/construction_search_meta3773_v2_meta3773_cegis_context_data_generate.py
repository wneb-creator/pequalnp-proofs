from pathlib import Path
import json,sys
j=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};old=json.loads((j/'meta3773-synthesis-data.json').read_text())
pos=old['positive'];singles=[1<<i for i in range(26)];pairs=[(1<<a)|(1<<b)for a in range(26)for b in range(a+1,26)if not(a<13<=b and(a+b-13)%13 in D)]
assert(len(pos),len(singles),len(pairs))==(52,26,273)
extra=[]
if len(sys.argv)>1:extra=json.loads((j/sys.argv[1]).read_text())['counterexamples']
assert len(set(extra))==len(extra)and all(x in old['negative_maximal']for x in extra)
scored=pos+singles+pairs+extra;rows=scored+old['negative_maximal'];nw=(len(rows)+63)//64
inputs=[[sum(((m>>i)&1)<<(k%64)for k,m in enumerate(rows)if k//64==w)for w in range(nw)]for i in range(26)]
text=str(len(rows))+' '+str(nw)+' 52 52 351 '+str(len(scored))+'\n'+'\n'.join(' '.join(map(str,w))for w in inputs)+'\n'
(j/'meta3773-synthesis-cegis-context-data.txt').write_text(text)
(j/'meta3773-synthesis-cegis-context-rows.json').write_text(json.dumps({'positive':pos,'sparse_negative':singles+pairs,'counterexamples':extra,'scored_rows':len(scored),'rows':rows},indent=2)+'\n')
print(json.dumps({'positive':52,'singleton_negative':26,'pair_negative':273,'counterexamples':len(extra),'scored':len(scored),'total_context':len(rows),'words':nw,'scope':'ABSTRACT scored goal until all808 original tests pass independently'}))
