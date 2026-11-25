from pathlib import Path
import json
base=Path('/tmp/oec/pequalnp-pilot-65/finite-search')
witness=json.loads((base/'plane65-witness.json').read_text());gs=witness['gates'];out=witness['output']
adj=[sum(1<<j for j in range(13) if (i-j)%13 in [0,1,3,9]) for i in range(13)]
pos=[(1<<i)|(1<<(13+j)) for i in range(13) for j in range(13) if adj[i]>>j&1]
neg=json.loads((base/'plane-maxind.json').read_text());rows=[1,1<<13]+pos+neg
target=sum(1<<i for i in range(2,54))
inputs=[sum(1<<r for r,s in enumerate(rows) if s>>i&1) for i in range(26)]
def ev(drop,repl):
    w=inputs[:];dx=[int(i==13) for i in range(26)];dy=[int(i==0) for i in range(26)]
    for j,(op,a,b) in enumerate(gs):
        if j==drop:w.append(w[repl]);dx.append(dx[repl]);dy.append(dy[repl]);continue
        if op=='or':w.append(w[a]|w[b]);dx.append(dx[a]|dx[b]);dy.append(dy[a]|dy[b])
        else:w.append(w[a]&w[b]);dx.append((w[a]&1)&dx[b]|dx[a]&(w[b]&1));dy.append(((w[a]>>1)&1)&dy[b]|dy[a]&((w[b]>>1)&1))
    bad=(w[out]^target).bit_count();d=dx[out]+dy[out]
    return bad,d
scores=[]
for j in range(len(gs)):
    for r in range(26+j):scores.append((*ev(j,r),j,r))
scores.sort()
print(json.dumps({'candidates':len(scores),'best':scores[:30]}))
(base/'drop-one-results.json').write_text(json.dumps(scores,indent=2)+'\n')
