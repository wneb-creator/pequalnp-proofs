import argparse
import json
import subprocess
from pathlib import Path

P=Path(__file__).resolve().parent
SOLVER='/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical'
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(r):return any(r>>a&1 and r>>b&1 for a,b in EDGES)

def make(n,s,rows,normalized=True):
    wd=2**n+n+s+1
    def ix(kd,j,a):return (kd*(s+1)+j)*wd+a+1
    cs=[];sections={}
    def mark(name):sections[name]=len(cs)
    mark('fOp')
    for j in range(s):cs.append([ix(0,j,k) for k in range(3)])
    mark('fSrcAlo')
    for e in (1,2):
        for j in range(s):cs.append([ix(e,j,k) for k in range(n+j+1)])
    mark('fSrcEq')
    for e in (1,2):
        for j in range(s):
            for r in rows:
                for k in range(n+j+1):
                    sel=ix(e,j,k);val=ix(e+3,j,r)
                    if k<n:cs.append([-sel,val if r>>k&1 else -val])
                    elif k<n+j:
                        wire=ix(3,k-n,r);cs.extend([[-sel,-val,wire],[-sel,val,-wire]])
                    else:cs.append([-sel,-val])
    mark('fGate')
    for j in range(s):
        for r in rows:
            o=[ix(0,j,k) for k in range(3)];v=ix(3,j,r);a=ix(4,j,r);b=ix(5,j,r)
            cs.extend([[-o[0],-v,a],[-o[0],-v,b],[-o[0],v,-a,-b],[-o[1],v,-a],[-o[1],v,-b],[-o[1],-v,a,b],[-o[2],v]])
    mark('fOutAlo');cs.append([ix(6,0,k) for k in range(n+s+1)])
    mark('fOutEq')
    for r in rows:
        for k in range(n+s+1):
            out=ix(6,0,k)
            if k<n:
                if bool(r>>k&1)!=target(r):cs.append([-out])
            elif k<n+s:cs.append([-out,ix(3,k-n,r) if target(r) else -ix(3,k-n,r)])
            elif target(r):cs.append([-out])
    if normalized:
        mark('fOut')
        if s:cs.append([ix(6,0,n+s-1),ix(7,s-1,0)])
        mark('fPad')
        for j in range(s):
            p=ix(7,j,0);t=ix(0,j,2);a=ix(1,j,n+j);b=ix(2,j,n+j)
            cs.extend([[-p,t],[-p,a],[-p,b],[p,-t],[p,-a],[p,-b]])
        mark('fPre')
        for j in range(s-1):cs.append([-ix(7,j+1,0),ix(7,j,0)])
        mark('fPadRd')
        for j in range(s):
            for i in range(j):cs.extend([[-ix(7,i,0),-ix(1,j,n+i)],[-ix(7,i,0),-ix(2,j,n+i)]])
        mark('fOrd')
        for j in range(s):
            for k in range(n+j+1):
                for l in range(k+1):cs.append([-ix(1,j,k),-ix(2,j,l),ix(7,j,0)])
        mark('fUsed')
        for j in range(s-1):cs.append([ix(1,j+1+t,n+j) for t in range(s-1-j)]+[ix(2,j+1+t,n+j) for t in range(s-1-j)]+[ix(7,j,0)])
        mark('fLex')
        for j in range(s-1):
            esc=[ix(7,j,0),ix(1,j+1,n+j),ix(2,j+1,n+j)]
            for a in range(n+j+1):
                for b in range(a):cs.append([-ix(1,j,a),-ix(1,j+1,b)]+esc)
                for c in range(n+j+1):
                    for d in range(c):cs.append([-ix(1,j,a),-ix(1,j+1,a),-ix(2,j,c),-ix(2,j+1,d)]+esc)
                    cs.append([-ix(1,j,a),-ix(1,j+1,a),-ix(2,j,c),-ix(2,j+1,c),-ix(0,j,1)]+esc)
                    cs.append([-ix(1,j,a),-ix(1,j+1,a),-ix(2,j,c),-ix(2,j+1,c),-ix(0,j+1,0)]+esc)
    mark('end');return cs,ix,sections

def decode(n,s,ix,model):
    gs=[]
    for j in range(s):
        op=next(k for k in range(3) if ix(0,j,k) in model)
        a=next(k for k in range(n+j+1) if ix(1,j,k) in model)
        b=next(k for k in range(n+j+1) if ix(2,j,k) in model);gs.append([op,a,b])
    out=next(k for k in range(n+s+1) if ix(6,0,k) in model);bad=[]
    for r in range(1<<n):
        w=[bool(r>>i&1) for i in range(n)]
        for op,a,b in gs:
            av=w[a] if a<len(w) else False;bv=w[b] if b<len(w) else False
            w.append(av and bv if op==0 else av or bv if op==1 else True)
        if (w[out] if out<len(w) else False)!=target(r):bad.append(r)
    return {'gates':gs,'output':out,'bad':bad}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=19);ap.add_argument('--name',default='petersen19-enc2');ap.add_argument('--unrestricted',action='store_true');ap.add_argument('--fix',default='');ap.add_argument('--solve',action='store_true');ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--solution',default='');ar=ap.parse_args()
    n=10;s=ar.gates;ind=[r for r in range(1024) if not target(r)];mis=[r for r in ind if all(target(r|(1<<i)) for i in range(n) if not r>>i&1)]
    rows=sorted(set(mis+[sum(1<<i for i in e) for e in EDGES]));assert len(ind)==76 and len(mis)==15 and len(rows)==30
    cs,ix,sections=make(n,s,rows,not ar.unrestricted)
    if ar.solution:
        model={int(v) for l in Path(ar.solution).read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};print(json.dumps(decode(n,s,ix,model),indent=2));return
    if ar.fix:
        fixed=json.loads(Path(ar.fix).read_text())
        for j,(op,a,b) in enumerate(fixed['gates']):cs.extend([[ix(0,j,op)],[ix(1,j,a)],[ix(2,j,b)]])
        cs.append([ix(6,0,fixed['output'])])
    mx=max(abs(v) for c in cs for v in c);base=P/ar.name
    with base.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {mx} {len(cs)}\n')
        for c in cs:f.write(' '.join(map(str,c))+' 0\n')
    base.with_suffix('.meta.json').write_text(json.dumps({'n':n,'s':s,'rows':rows,'mis':mis,'edges':EDGES,'independent_count':len(ind),'clauses':len(cs),'max_var':mx,'normalized':not ar.unrestricted,'sections':sections},indent=2)+'\n')
    print('FORMULA',mx,len(cs),'ROWS',len(rows),flush=True)
    if not ar.solve:return
    with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:
        run=subprocess.run([SOLVER,'--lrat','--binary','-t',str(ar.seconds),str(base.with_suffix('.cnf')),str(base.with_suffix('.lrat'))],stdout=out,stderr=err)
    print('EXIT',run.returncode,flush=True)
    if run.returncode==10:
        model={int(v) for l in base.with_suffix('.stdout').read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};result=decode(n,s,ix,model);base.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2)+'\n');print('MODEL WRONG ROWS',len(result['bad']),flush=True)

if __name__=='__main__':main()
