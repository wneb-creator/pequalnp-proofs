from pathlib import Path
import itertools,json,sys
job=Path('/tmp/oec/pequalnp-pilot-79')
D={0,1,3,9}
edges=[[p,l]for p in range(13)for l in range(13)if(p+l)%13 in D]
positive=[(1<<p)|(1<<(13+l))for p,l in edges]
negative_full=[]
for k in range(4):
 for s in itertools.combinations(range(13),k):
  t=[l for l in range(13)if all((p+l)%13 not in D for p in s)]
  a=sum(1<<p for p in s);b=sum(1<<l for l in t)
  negative_full.extend([a|(b<<13),b|(a<<13)])
unique=sorted(set(negative_full))
negative_maximal=[m for m in unique if not any(m!=n and m&n==m for n in unique)]
rows=positive+negative_maximal;nw=(len(rows)+63)//64
inputs=[[sum(((m>>i)&1)<<(j%64) for j,m in enumerate(rows)if j//64==w) for w in range(nw)]for i in range(26)]
d={'D':sorted(D),'edges':edges,'positive':positive,'negative_full':negative_full,'negative_maximal':negative_maximal,'rows':rows,'words':nw,'inputs':inputs}
old=json.loads((job/'meta3773-synthesis-data.json').read_text())
assert d==old
text=str(len(rows))+' '+str(nw)+'\n'+'\n'.join(' '.join(map(str,w))for w in inputs)+'\n'
assert text==(job/'meta3773-synthesis-data.txt').read_text()
print(json.dumps({'data_matches':True,'positive':len(positive),'negative_full':len(negative_full),'negative_maximal':len(negative_maximal),'words':nw}))
