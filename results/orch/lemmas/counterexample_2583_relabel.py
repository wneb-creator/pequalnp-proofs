from pathlib import Path
import json

base=Path('/tmp/oec/pequalnp-pilot-128')
data=json.loads(Path('results/orch/lemmas/counterexample_2583_data.json').read_text())
vectors=[tuple(v) for v in data['coordinates']]
index={v:i for i,v in enumerate(vectors)}
A=[[0,0,1],[0,1,0],[1,2,0]]
aug=[row[:]+[int(i==j) for j in range(3)] for i,row in enumerate(A)]
for col in range(3):
    pivot=next(i for i in range(col,3) if aug[i][col])
    aug[col],aug[pivot]=aug[pivot],aug[col]
    scalar=pow(aug[col][col],-1,3)
    aug[col]=[(v*scalar)%3 for v in aug[col]]
    for i in range(3):
        if i!=col:
            scalar=aug[i][col]
            aug[i]=[(a-scalar*b)%3 for a,b in zip(aug[i],aug[col])]
B=[list(row) for row in zip(*(row[3:] for row in aug))]
def image(M,v):
    result=tuple(sum(a*b for a,b in zip(row,v))%3 for row in M)
    scale=pow(next(a for a in result if a),-1,3)
    return tuple(a*scale%3 for a in result)
perm=[13+index[image(B,v)] for v in vectors]+[index[image(A,v)] for v in vectors]
assert sorted(perm)==list(range(26))
E={tuple(e) for e in data['edges']}
assert {tuple(sorted((perm[a],perm[b]))) for a,b in E}==E
lines=(base/'counterexample-2583-one-missing-edge.txt').read_text().splitlines()
original=[(p[1],int(p[2]),int(p[3])) for line in lines[1:64] if (p:=line.split())]
renaming={i:perm[i] for i in range(26)}
remaining=set(range(63));ordered=[]
while remaining:
    ready=[i for i in remaining if original[i][1] in renaming and original[i][2] in renaming]
    assert ready
    i=min(ready,key=lambda i:(max(renaming[original[i][1]],renaming[original[i][2]]),min(renaming[original[i][1]],renaming[original[i][2]]),original[i][0],i))
    op,a,b=original[i];a,b=sorted((renaming[a],renaming[b]))
    renaming[26+i]=26+len(ordered);ordered.append((op,a,b));remaining.remove(i)
assert renaming[88]==88
assert ordered[0]==('or',0,1)
assert all(max(ordered[i][1:])<=max(ordered[i+1][1:]) for i in range(62))
errors=[]
for mask,target in data['boundary_rows']:
    w=[bool(mask&(1<<i)) for i in range(26)]
    for op,a,b in ordered:
        assert a<len(w) and b<len(w)
        w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
    if w[-1]!=bool(target):errors.append(mask)
assert len(errors)==1
out=base/'counterexample-2583-canonical-one-edge.txt'
out.write_text('errors 1 false_negative 1 false_positive 0 iteration 0\n'+''.join(f'{26+i} {op} {a} {b}\n' for i,(op,a,b) in enumerate(ordered))+'error_masks: '+str(errors[0])+'\n')
print(out)
print('First gate:',ordered[0],'; missing edge:',[i for i in range(26) if (errors[0]>>i)&1])
print('Point/line permutation:',perm)
