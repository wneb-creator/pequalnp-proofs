from pathlib import Path
from datetime import datetime, timezone
import subprocess, itertools, json
base=Path(__file__).resolve().parent
repo=Path('/workspace/pequalnp-proofs')
solver=Path('/tmp/oec/pequalnp-pilot-100/sat/cadical/build/cadical')
cases=[('c5',5,8,[(i,(i+1)%5) for i in range(5)]),('friendship2',5,10,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),('c6',6,10,[(i,(i+1)%6) for i in range(6)]),('c6chord',6,11,[(i,(i+1)%6) for i in range(6)]+[(0,2)])]
reports=[]
for name,n,s,edges in cases:
    start=datetime.now(timezone.utc).isoformat()
    E={frozenset(e) for e in edges}
    assert all(sum(frozenset((u,w)) in E and frozenset((v,w)) in E for w in range(n))<=1 for u,v in itertools.combinations(range(n),2))
    cap=len(E)-2;A=(1<<n)+n+s+1
    p=lambda k,j,a:(k*(s+1)+j)*A+a+1
    cnf=base/(name+'.cnf')
    with (base/(name+'-gen.out')).open('w') as out,(base/(name+'-gen.err')).open('w') as err:
        subprocess.run(['python3',str(repo/'notes/data/lrat-link/genmono.py'),str(n),str(s),','.join(str(u)+str(v) for u,v in edges),str(cnf),'lex'],stdout=out,stderr=err,check=True,cwd=repo)
    lines=cnf.read_text().splitlines();nv=int(lines[0].split()[2]);clauses=lines[1:]
    groups=[(0,j,3) for j in range(s)]+[(k,j,n+j+1) for k in (1,2) for j in range(s)]+[(6,0,n+s+1)]
    for k,j,m in groups:
        clauses.extend(f'{-p(k,j,a)} {-p(k,j,b)} 0' for a,b in itertools.combinations(range(m),2))
    clauses.extend(' '.join(str(-p(0,j,1)) for j in js)+' 0' for js in itertools.combinations(range(s),cap+1))
    cnf.write_text(f'p cnf {nv} {len(clauses)}\n'+'\n'.join(clauses)+'\n')
    with (base/(name+'-solve.out')).open('w') as out,(base/(name+'-solve.err')).open('w') as err:
        run=subprocess.run([str(solver),'-t','90',str(cnf)],stdout=out,stderr=err,cwd=repo)
    report={'name':name,'n':n,'slots':s,'edges':edges,'or_cap':cap,'start':start,'finish':datetime.now(timezone.utc).isoformat(),'returncode':run.returncode}
    if run.returncode==10:
        pos={int(v) for line in (base/(name+'-solve.out')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
        def pick(k,j,m):
            a=[i for i in range(m) if p(k,j,i) in pos]
            assert len(a)==1,(k,j,m,a)
            return a[0]
        raw=[(pick(0,j,3),pick(1,j,n+j+1),pick(2,j,n+j+1)) for j in range(s)]
        output=pick(6,0,n+s+1);live=set()
        def visit(w):
            if w<n or w in live:return
            assert w<n+s
            op,a,b=raw[w-n];assert op<2 and a<w and b<w
            live.add(w);visit(a);visit(b)
        visit(output);ren={i:i for i in range(n)};gates=[]
        for j,(op,a,b) in enumerate(raw):
            if n+j in live:
                ren[n+j]=n+len(gates);gates.append((op,ren[a],ren[b]))
        output=ren[output];errors=[]
        for r in range(1<<n):
            w=[bool(r>>i&1) for i in range(n)]
            for op,a,b in gates:w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]))
            if w[output]!=any(r>>u&1 and r>>v&1 for u,v in edges):errors.append(r)
        report.update(gates=gates,output=output,actual_size=len(gates),or_count=sum(op==1 for op,a,b in gates),errors=errors)
        assert not errors and report['or_count']<=cap
    reports.append(report);(base/'results.json').write_text(json.dumps(reports,indent=2));print(json.dumps(report),flush=True)
