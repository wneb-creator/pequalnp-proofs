import importlib.util
import json
import subprocess
from pathlib import Path

P=Path('/tmp/oec/pequalnp-pilot-99/counterexample')
spec=importlib.util.spec_from_file_location('canonical',P/'canonical.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
SOLVER='/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical'
n=10;s=19
for blocker in [50,104,116,138,201]:
    edge=3;meet=edge&blocker;join=edge|blocker
    rows=sorted(set([r for r in range(1024) if not c.target(r)]+[(1<<a)|(1<<b) for a,b in c.EDGES]+[join]))
    cs,ix=c.make(n,s,rows)
    # Exactly one NOT selector; all other operation selections remain unrestricted.
    for i in range(s):
        for j in range(i+1,s):cs.append([-ix(0,i,3),-ix(0,j,3)])
    for j in range(s):
        for row,val in [(edge,False),(blocker,True),(meet,False),(join,True)]:
            cs.append([-ix(0,j,3),ix(4,j,row) if val else -ix(4,j,row)])
    copies=[(edge,False,False),(blocker,True,True),(meet,False,False),(meet,True,False),(join,False,True),(join,True,True)]
    for ci,(row,forced,goal) in enumerate(copies):
        tag=1024+ci
        for e in [1,2]:
            for j in range(s):
                for k in range(n+j+1):
                    sel=ix(e,j,k);val=ix(e+3,j,tag)
                    if k<n:cs.append([-sel,val if row>>k&1 else -val])
                    elif k<n+j:
                        wire=ix(3,k-n,tag)
                        cs.append([-sel,-val,wire]);cs.append([-sel,val,-wire])
                    else:cs.append([-sel,-val])
        for j in range(s):
            o=[ix(0,j,k) for k in range(4)];v=ix(3,j,tag);a=ix(4,j,tag);b=ix(5,j,tag)
            cs.extend([[-o[0],-v,a],[-o[0],-v,b],[-o[0],v,-a,-b],
                       [-o[1],v,-a],[-o[1],v,-b],[-o[1],-v,a,b],
                       [-o[2],v],[-o[3],v if forced else -v]])
        for k in range(n+s+1):
            out=ix(6,0,k)
            if k<n:
                if bool(row>>k&1)!=goal:cs.append([-out])
            elif k<n+s:cs.append([-out,ix(3,k-n,tag) if goal else -ix(3,k-n,tag)])
            elif goal:cs.append([-out])
    name=P/f'witness-{blocker}';mx=max(abs(v) for cl in cs for v in cl)
    with name.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {mx} {len(cs)}\n')
        for cl in cs:f.write(' '.join(map(str,cl))+' 0\n')
    name.with_suffix('.meta.json').write_text(json.dumps({'rows':rows,'edge':edge,'blocker':blocker,'meet':meet,'join':join,'copies':copies,'n':n,'s':s}))
    print('START',blocker,len(cs),flush=True)
    with name.with_suffix('.stdout').open('w') as out,name.with_suffix('.stderr').open('w') as err:
        run=subprocess.run([SOLVER,'--sat','-t','60',str(name.with_suffix('.cnf'))],stdout=out,stderr=err)
    print('END',blocker,run.returncode,flush=True)
    if run.returncode==10:
        model=set()
        for line in name.with_suffix('.stdout').read_text().splitlines():
            if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
        result=c.decode(n,s,ix,model);name.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2))
        print('MODEL mismatch',len(result['bad']),flush=True)
        if not result['bad']:print('COUNTEREXAMPLE',flush=True);break
