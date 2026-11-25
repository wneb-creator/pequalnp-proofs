import argparse,json,re,time
from pathlib import Path
from synth_circuit import INPUTS,TARGET,FULL,check

def ev(o,a,b,w):
    return w[a]&w[b] if o==0 else w[a]|w[b] if o==1 else FULL^w[a]

def run(seed,out):
    assert all(o!=2 for o,a,b in seed)
    start=time.monotonic();trials=0;feasible=0
    for i in range(len(seed)):
        n=10+i
        options=[(o,a,b) for o in [0,1] for a in range(n) for b in range(a+1,n)]+[(2,a,0) for a in range(n)]
        for first in options:
            if first==tuple(seed[i]):continue
            c=[tuple(g) for g in seed];c[i]=first
            w=INPUTS[:]
            for o,a,b in c:w.append(ev(o,a,b,w))
            for j in range(i+1,len(seed)):
                lo=w[:10+j]+[0];hi=w[:10+j]+[FULL]
                for o,a,b in c[j+1:]:
                    lo.append(ev(o,a,b,lo));hi.append(ev(o,a,b,hi))
                trials+=1
                if (lo[-1]&~TARGET) or (TARGET&~hi[-1]):continue
                feasible+=1;care=hi[-1]^lo[-1];wanted=TARGET&care
                m=10+j
                candidates=[(2,a,0) for a in range(m)] if first[0]!=2 else ((o,a,b) for o in [0,1] for a in range(m) for b in range(a+1,m))
                for second in candidates:
                    if ev(*second,w)&care==wanted:
                        c[j]=second
                        assert not check(c)
                        Path(out).write_text(json.dumps({'gates':c,'first':i,'second':j},indent=2))
                        print('WITNESS_FOUND',i,j,c,flush=True);return
        print(json.dumps({'first_gate_done':i,'seconds':time.monotonic()-start,'trials':trials,'feasible_pairs':feasible}),flush=True)
    print('No exact one-NOT repair by changing two gate records of this seed.',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--log',required=True);p.add_argument('--out',required=True);args=p.parse_args()
    rows=re.findall(r'score=(\d+).*?gates=(\[.*\])',Path(args.log).read_text())
    seed=json.loads(min(rows,key=lambda t:int(t[0]))[1]);print('Seed mismatch count:',len(check(seed)),flush=True)
    run(seed,args.out)
