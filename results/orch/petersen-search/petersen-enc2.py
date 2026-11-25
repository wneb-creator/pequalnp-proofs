import argparse
import json
from pathlib import Path

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]

def target(x):
    return any((x >> a & 1) and (x >> b & 1) for a, b in EDGES)

def seed_samples():
    patterns = []
    for first in [0, 1]:
        for x in range(1024):
            if (x & 1) != first:
                continue
            if target(x):
                if all(not target(x ^ (1 << v)) for v in range(1, 10) if x >> v & 1):
                    patterns.append(x)
            elif all(target(x | (1 << v)) for v in range(1, 10) if not x >> v & 1):
                patterns.append(x)
    return sorted(set(patterns + [x for x in range(1024) if not target(x)] +
                      [1023] + [1023 ^ (1 << i) for i in range(10)]))

def encode(n, s, rows):
    width = 2 ** n + n + s + 2
    def v(kd, j, a):
        return (kd * (s + 1) + j) * width + a + 1
    clauses = []
    add = clauses.append
    for j in range(s):
        add([v(0,j,o) for o in range(4)])
    for e in [1,2]:
        for j in range(s):
            add([v(e,j,k) for k in range(n+j+1)])
    for e in [1,2]:
        for j in range(s):
            for r in rows:
                for k in range(n+j+1):
                    sel, val = v(e,j,k), v(e+3,j,r)
                    if k < n:
                        add([-sel, val if r >> k & 1 else -val])
                    elif k < n+j:
                        old = v(3,k-n,r)
                        add([-sel,-val,old]); add([-sel,val,-old])
                    else:
                        add([-sel,-val])
    for j in range(s):
        for r in rows:
            a,b,c,d = [v(0,j,o) for o in range(4)]
            w,u,t = v(3,j,r),v(4,j,r),v(5,j,r)
            for cl in [[-a,-w,u],[-a,-w,t],[-a,w,-u,-t],
                       [-b,w,-u],[-b,w,-t],[-b,-w,u,t],
                       [-c,w],[-d,w,u],[-d,-w,-u]]:
                add(cl)
    add([v(6,0,k) for k in range(n+s+1)])
    for r in rows:
        g = target(r)
        for k in range(n+s+1):
            o = v(6,0,k)
            if k < n:
                if bool(r >> k & 1) != g:
                    add([-o])
            elif k < n+s:
                w = v(3,k-n,r)
                add([-o,w if g else -w])
            elif g:
                add([-o])
    if s:
        add([v(6,0,n+s-1),v(7,s-1,0)])
    for j in range(s):
        p,t,a,b=v(7,j,0),v(0,j,2),v(1,j,n+j),v(2,j,n+j)
        for cl in [[-p,t],[-p,a],[-p,b],[p,-t],[p,-a],[p,-b]]:
            add(cl)
    for j in range(s-1):
        add([-v(7,j+1,0),v(7,j,0)])
    for j in range(s):
        for i in range(j):
            add([-v(7,i,0),-v(1,j,n+i)])
            add([-v(7,i,0),-v(2,j,n+i)])
    for j in range(s):
        for k in range(n+j+1):
            for l in range(k+1):
                add([-v(1,j,k),-v(2,j,l),v(7,j,0)] + ([v(0,j,3)] if l==k else []))
    for j in range(s-1):
        add([v(1,j+1+t,n+j) for t in range(s-1-j)] +
            [v(2,j+1+t,n+j) for t in range(s-1-j)] + [v(7,j,0)])
    for j in range(s):
        for k in range(n+j+1):
            add([-v(0,j,3),-v(1,j,k),v(2,j,k)])
    for j in range(s):
        for i in range(j):
            add([-v(0,j,3),-v(0,i,3),-v(1,j,n+i)])
    for j in range(s-1):
        base=[v(7,j,0),v(1,j+1,n+j),v(2,j+1,n+j)]
        for a in range(n+j+1):
            for b in range(a):
                add([-v(1,j,a),-v(1,j+1,b)]+base)
            for c in range(n+j+1):
                for d in range(c):
                    add([-v(1,j,a),-v(1,j+1,a),-v(2,j,c),-v(2,j+1,d)]+base)
                common=[-v(1,j,a),-v(1,j+1,a),-v(2,j,c),-v(2,j+1,c)]
                add(common+[-v(0,j,1)]+base)
                add(common+[-v(0,j+1,0)]+base)
    return clauses, width

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--gates',type=int,default=18)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--samples',type=Path)
    args=parser.parse_args()
    samples=json.loads(args.samples.read_text()) if args.samples else seed_samples()
    assert all(isinstance(x,int) and 0<=x<1024 for x in samples)
    rows=[r+1024*(1-(r&1)) for r in samples]
    clauses,width=encode(11,args.gates,rows)
    maxvar=max(abs(l) for c in clauses for l in c)
    with args.out.open('w') as f:
        f.write(f'p cnf {maxvar} {len(clauses)}\n')
        for c in clauses:
            f.write(' '.join(map(str,c))+' 0\n')
    metadata={'n':11,'s':args.gates,'width':width,'samples':samples,'rows':rows,
              'variables':maxvar,'clauses':len(clauses),
              'dimacs_variable':'(kd*(s+1)+j)*width+a+1',
              'kinds':{'0':'operation: a0=AND,a1=OR,a2=TRUE,a3=NOT',
                       '1':'first source selection','2':'second source selection',
                       '3':'gate value on row a','4':'first source value on row a',
                       '5':'second source value on row a','6':'output source selection (j=0)',
                       '7':'padding flag (a=0)'},
              'source':'Exact clause order of LinkN2.enc2; no extra constraints.'}
    args.out.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps({'samples':len(samples),'clauses':len(clauses),'variables':maxvar,
                      'bytes':args.out.stat().st_size}))

if __name__=='__main__':
    main()
