#!/usr/bin/env python3
import json, random, time, math
from pathlib import Path
from search64 import N, INPUTS, TARGET, evaluate, independent_verify, valid, gate_value

JOB=Path('/tmp/oec/pequalnp-pilot-60')
rng=random.Random(2602060)
seed=json.loads((JOB/'tight-circuit.json').read_text())
seedg=seed['gates']

def used(gates,out):
    seen=set(); pending=[out]
    while pending:
        w=pending.pop()
        if w<N or w in seen:continue
        seen.add(w); _,a,b=gates[w-N];pending.extend((a,b))
    return seen

def compact(gates,out):
    live=used(gates,out); mp=list(range(N)); result=[]
    for j,(op,a,b) in enumerate(gates):
        if N+j in live:
            mp.append(N+len(result));result.append((op,mp[a],mp[b]))
        else:mp.append(-1)
    return result,mp[out]

def fresh():
    gates=[];mp=list(range(N))
    for j,(op,a,b) in enumerate(seedg):
        for t in range(3):
            k=N+len(gates)
            x,y=rng.sample(range(k),2)
            gates.append((rng.choice(('and','or')),x,y))
        mp.append(N+len(gates));gates.append((op,mp[a],mp[b]))
    return gates,mp[seed['output']]

start=time.monotonic();deadline=start+600;report=start;attempts=accepted=equiv=0;best=65;restarts=0
while time.monotonic()<deadline:
    gates,out=fresh(); sig,values=evaluate(gates,out);assert sig==(TARGET,0,0)
    live=used(gates,out); epoch=time.monotonic();stagnant=0
    while time.monotonic()<deadline and time.monotonic()-epoch<90:
        attempts+=1
        if rng.random()<0.70:j=rng.choice(tuple(live))-N
        else:j=rng.randrange(len(gates))
        old=gates[j];op,a,b=old
        part=rng.randrange(3)
        if part==0:op='and' if op=='or' else 'or'
        else:
            w=rng.randrange(N+j)
            if part==1:a=w
            else:b=w
        if a==b or (op,a,b)==old:continue
        gates[j]=(op,a,b)
        ns,nv=evaluate(gates,out,values,j)
        if ns!=(TARGET,0,0):gates[j]=old;continue
        nl=used(gates,out) if N+j in live else live
        delta=len(nl)-len(live)
        temp=0.6 if len(live)<=65 else 0.3
        if len(nl)>69 or (delta>0 and rng.random()>math.exp(-delta/temp)):
            gates[j]=old;continue
        values=nv;live=nl;accepted+=1
        if delta!=0:equiv+=1
        if attempts%250==0:
            options=[w for w in range(N,len(values)) if values[w]==(TARGET,0,0)]
            for w in options:
                wl=used(gates,w)
                if len(wl)<len(live):out=w;live=wl
        if len(live)<best:
            best=len(live); cg,co=compact(gates,out)
            candidate={'gates':cg,'output':co,'attempts':attempts,'seconds':time.monotonic()-start}
            (JOB/'cgp-best.json').write_text(json.dumps(candidate,indent=2)+'\n')
            print('BEST',best,'attempts',attempts,flush=True)
            if best<=64:
                assert valid(cg,co) and independent_verify(cg,co)
                (JOB/'cgp-witness64.json').write_text(json.dumps(candidate,indent=2)+'\n')
                print('FOUND EXACT WITNESS',best,flush=True)
                raise SystemExit(0)
        if time.monotonic()>=report:
            print(json.dumps({'seconds':round(time.monotonic()-start,1),'attempts':attempts,'accepted':accepted,'size_changes':equiv,'active':len(live),'best':best,'restarts':restarts}),flush=True)
            report=time.monotonic()+30
    restarts+=1
print(json.dumps({'finished':True,'seconds':time.monotonic()-start,'attempts':attempts,'accepted':accepted,'size_changes':equiv,'best':best,'restarts':restarts}),flush=True)
