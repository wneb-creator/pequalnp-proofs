import argparse
import json
from pathlib import Path

P=Path('/tmp/oec/pequalnp-pilot-99/counterexample')
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):return any((x>>a&1) and (x>>b&1) for a,b in EDGES)

def make(n,s,rows):
    wd=2**n+n+s+1
    def ix(kd,j,a):return (kd*(s+1)+j)*wd+a+1
    cs=[]
    # fOpN
    for j in range(s):cs.append([ix(0,j,k) for k in range(4)])
    # fSrcAlo
    for e in [1,2]:
        for j in range(s):cs.append([ix(e,j,k) for k in range(n+j+1)])
    # fSrcEq
    for e in [1,2]:
        for j in range(s):
            for r in rows:
                for k in range(n+j+1):
                    sel=ix(e,j,k);val=ix(e+3,j,r)
                    if k<n:cs.append([-sel,val if r>>k&1 else -val])
                    elif k<n+j:
                        wire=ix(3,k-n,r)
                        cs.append([-sel,-val,wire]);cs.append([-sel,val,-wire])
                    else:cs.append([-sel,-val])
    # fGateN
    for j in range(s):
        for r in rows:
            o=[ix(0,j,k) for k in range(4)];v=ix(3,j,r);a=ix(4,j,r);b=ix(5,j,r)
            cs.extend([[-o[0],-v,a],[-o[0],-v,b],[-o[0],v,-a,-b],
                       [-o[1],v,-a],[-o[1],v,-b],[-o[1],-v,a,b],
                       [-o[2],v],[-o[3],-v,-a],[-o[3],v,a]])
    # fOutAlo
    cs.append([ix(6,0,k) for k in range(n+s+1)])
    # fOutEq
    for r in rows:
        goal=target(r)
        for k in range(n+s+1):
            out=ix(6,0,k)
            if k<n:
                if bool(r>>k&1)!=goal:cs.append([-out])
            elif k<n+s:cs.append([-out,ix(3,k-n,r) if goal else -ix(3,k-n,r)])
            elif goal:cs.append([-out])
    # At least one NOT, no other restriction.
    cs.append([ix(0,j,3) for j in range(s)])
    return cs,ix

def decode(n,s,ix,model):
    # Choose a NOT wherever selected, preserving the final NOT-existence clause.
    gs=[]
    for j in range(s):
        kinds=[k for k in range(4) if ix(0,j,k) in model]
        op=3 if 3 in kinds else kinds[0]
        a=next(k for k in range(n+j+1) if ix(1,j,k) in model)
        b=next(k for k in range(n+j+1) if ix(2,j,k) in model)
        gs.append((op,a,b))
    out=next(k for k in range(n+s+1) if ix(6,0,k) in model)
    bad=[]
    for r in range(2**n):
        w=[bool(r>>i&1) for i in range(n)]
        for op,a,b in gs:
            aa=w[a] if a<len(w) else False;bb=w[b] if b<len(w) else False
            w.append(aa and bb if op==0 else aa or bb if op==1 else True if op==2 else not aa)
        value=w[out] if out<len(w) else False
        if value!=target(r):bad.append(r)
    return {'gates':gs,'output':out,'bad':bad}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--name',default='canonical');ap.add_argument('--gates',type=int,default=19);ap.add_argument('--allrows',action='store_true');ap.add_argument('--solution',default='');ap.add_argument('--fixfile',default='');ap.add_argument('--rowsfile',default='');ap.add_argument('--atmost3',action='store_true');ap.add_argument('--exactly1',action='store_true');ap.add_argument('--exactly2',action='store_true');args=ap.parse_args()
    n=10;s=args.gates
    rows=list(range(1024)) if args.allrows else sorted(set([r for r in range(1024) if not target(r)]+[(1<<a)|(1<<b) for a,b in EDGES]))
    if args.rowsfile:rows=json.loads(Path(args.rowsfile).read_text())
    assert all(isinstance(r,int) and 0<=r<1024 for r in rows)
    cs,ix=make(n,s,rows)
    assert sum([args.atmost3,args.exactly1,args.exactly2])<=1
    if args.atmost3:
        for a in range(s):
            for b in range(a):
                for cc in range(b):
                    for d in range(cc):cs.append([-ix(0,a,3),-ix(0,b,3),-ix(0,cc,3),-ix(0,d,3)])
    if args.exactly1:
        for a in range(s):
            for b in range(a):cs.append([-ix(0,a,3),-ix(0,b,3)])
    if args.exactly2:
        for a in range(s):
            for b in range(a):
                for cc in range(b):cs.append([-ix(0,a,3),-ix(0,b,3),-ix(0,cc,3)])
        for j in range(s):cs.append([-ix(0,j,3)]+[ix(0,k,3) for k in range(s) if k!=j])
    if args.solution:
        model=set()
        for line in Path(args.solution).read_text().splitlines():
            if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
        result=decode(n,s,ix,model);print(json.dumps(result,indent=2));return
    if args.fixfile:
        data=json.loads(Path(args.fixfile).read_text())
        for j,(op,a,b) in enumerate(data['gates']):cs.extend([[ix(0,j,op)],[ix(1,j,a)],[ix(2,j,b)]])
        cs.append([ix(6,0,data['output'])])
    mx=max(abs(v) for c in cs for v in c)
    path=P/(args.name+'.cnf')
    with path.open('w') as f:
        f.write(f'p cnf {mx} {len(cs)}\n')
        for c in cs:f.write(' '.join(map(str,c))+' 0\n')
    (P/(args.name+'.meta.json')).write_text(json.dumps({'n':n,'s':s,'rows':rows,'wd':2**n+n+s+1,'clauses':len(cs),'max_var':mx,'atmost3':args.atmost3,'exactly1':args.exactly1,'exactly2':args.exactly2},indent=2))
    print(path,'variables',mx,'clauses',len(cs),'rows',len(rows))

if __name__=='__main__':main()
