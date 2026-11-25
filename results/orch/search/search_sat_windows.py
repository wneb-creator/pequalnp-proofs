from pathlib import Path
import random
import subprocess
import json

work=Path('/tmp/oec/pequalnp-pilot-93')
cadical=work/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def latest(name):
    ls=(work/name).read_text().splitlines()
    i=max(i for i,x in enumerate(ls) if x.startswith('BEST'))
    return [tuple(map(int,x.split()))[1:] for x in ls[i+1:i+20]]

def normalize(gs):
    mask=(1<<1024)-1
    vals=[sum(((r>>i)&1)<<r for r in range(1024)) for i in range(10)]
    ren={i:i for i in range(10)};unique=[]
    for j,(op,a,b) in enumerate(gs):
        a,b=ren[a],ren[b]
        v=vals[a]&vals[b] if op==0 else vals[a]|vals[b] if op==1 else vals[a]^mask
        if v in vals:ren[10+j]=vals.index(v)
        else:ren[10+j]=len(vals);vals.append(v);unique.append((3 if op==2 else op,a,a if op==2 else b))
    used={ren[28]}
    for j in range(len(unique)-1,-1,-1):
        if 10+j in used:
            op,a,b=unique[j];used|={a,b}
    remaining=[(j+10,g) for j,g in enumerate(unique) if j+10 in used]
    pad=19-len(remaining);mapped={i:i for i in range(10)}
    ordered=[(2,10+j,10+j) for j in range(pad)]
    while remaining:
        ready=[]
        for old,(op,a,b) in remaining:
            if a in mapped and b in mapped:
                a,b=sorted((mapped[a],mapped[b]));ready.append(((a,b,op),old))
        (a,b,op),old=min(ready);mapped[old]=10+len(ordered)
        ordered.append((op,a,b));remaining=[(k,g) for k,g in remaining if k!=old]
    return ordered

base=(work/'petersen19-full.cnf').read_text()
header,body=base.split('\n',1)
_,_,nv,nc=header.split();nv,nc=int(nv),int(nc)
ix=lambda k,j,a:(k*20+j)*1055+a+1
rng=random.Random(193651)
seeds=[normalize(latest('search_cgp.log')),normalize(latest('search_cgp_not.log'))]
for trial in range(20):
    gs=seeds[trial%2]
    mandatory={j for j,(op,a,b) in enumerate(gs) if op in (2,3)}
    pool=list(range(19)) if trial>=8 else list(range(11,19))
    free=mandatory|set(rng.sample([i for i in pool if i not in mandatory],6-len(mandatory)))
    units=[]
    for j,(op,a,b) in enumerate(gs):
        if j not in free:units += [[ix(0,j,op)],[ix(1,j,a)],[ix(2,j,b)]]
    units.append([ix(0,j,3) for j in range(19)])
    (work/'window-current.cnf').write_text(f'p cnf {nv} {nc+len(units)}\n'+body+''.join(' '.join(map(str,c))+' 0\n' for c in units))
    (work/f'window-{trial:02}.json').write_text(json.dumps({'free':sorted(free),'seed':gs,'units':units},indent=2)+'\n')
    print('TRIAL',trial,'free',sorted(free),flush=True)
    with (work/f'window-{trial:02}.stdout').open('w') as out,(work/f'window-{trial:02}.stderr').open('w') as err:
        p=subprocess.run([str(cadical),'-t','20',str(work/'window-current.cnf')],stdout=out,stderr=err)
    print('RESULT',trial,p.returncode,flush=True)
    if p.returncode==10:
        print('SAT candidate',trial,flush=True)
        break
