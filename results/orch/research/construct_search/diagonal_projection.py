import json,itertools,collections
from pathlib import Path
root=Path('/tmp/oec/pequalnp-pilot-78')

def rref(A,p):
    A=[[x%p for x in row] for row in A];r=0
    for j in range(len(A[0])):
        k=next((k for k in range(r,len(A)) if A[k][j]),None)
        if k is None:continue
        A[k],A[r]=A[r],A[k];v=pow(A[r][j],-1,p);A[r]=[(x*v)%p for x in A[r]]
        for k in range(len(A)):
            if k!=r:
                v=A[k][j];A[k]=[(x-v*y)%p for x,y in zip(A[k],A[r])]
        r+=1
        if r==len(A):break
    return tuple(tuple(row) for row in A[:r])

for p in [5,7]:
    planes=json.loads((root/f'finitefield/f{p}-2planes.json').read_text())
    fibers=collections.defaultdict(list);kernels=collections.Counter();diaglines=collections.Counter()
    for index,(A,B) in enumerate(planes):
        D=[[v[i] for i in [0,4,7,9]] for v in [A,B]];R=rref(D,p)
        if len(R)==2:fibers[R].append(index)
        elif len(R)==1:
            for i in range(4):
                if D[0][i] or D[1][i]:
                    K=[(D[1][i]*a-D[0][i]*b)%p for a,b in zip(A,B)];break
            kernels[rref([K],p)[0]]+=1;diaglines[R[0]]+=1
    print('FIELD',p,'rank2planes',sum(map(len,fibers.values())),'diagimages',len(fibers),'fibers',dict(collections.Counter(map(len,fibers.values()))),'rank1hollowkernels',len(kernels),'kernelmultiplicity',dict(collections.Counter(kernels.values())),'diaglines',len(diaglines),flush=True)
    print('KERNELS',list(kernels.items()),flush=True)
    print('DIAGLINES',list(diaglines.items()),flush=True)
    (root/f'construct_search/f{p}-diagonal-images.json').write_text(json.dumps([{'rows':R,'preimages':ids} for R,ids in fibers.items()]))
