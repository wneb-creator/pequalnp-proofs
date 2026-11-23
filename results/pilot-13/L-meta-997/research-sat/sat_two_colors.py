import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path
from sat_family_synthesis import CNF


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--width',type=int,required=True)
    ap.add_argument('--colors',type=int,default=2)
    ap.add_argument('--gates',type=int,required=True)
    ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--sources-json',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    w=args.width
    n=args.colors*w
    target=[((1<<w)-1)<<(w*c) for c in range(args.colors)]
    initial=sorted(set([sum(0 if p is None else 1<<p for p in ps)
                       for ps in itertools.product(*([None]+list(range(c*w,(c+1)*w))
                                                    for c in range(args.colors)))]
                      +[(1<<n)-1]))
    if args.sources_json:
        initial=json.loads(args.sources_json.read_text())['initial_sources']
    ni=len(initial)
    cnf=CNF()
    left=[];right=[];op=[];a=[];b=[];v=[]
    for g in range(args.gates):
        left.append(cnf.vars(ni+g));right.append(cnf.vars(ni+g));op.append(cnf.vars(1)[0])
        a.append(cnf.vars(n));b.append(cnf.vars(n));v.append(cnf.vars(n))
    outs=[cnf.vars(args.gates) for _ in target]
    for g in range(args.gates):
        cnf.one(left[g]);cnf.one(right[g])
        for p in range(ni+g):
            for q in range(p):cnf.clauses.append([-left[g][p],-right[g][q]])
        for row in range(n):
            for sels,picked in [(left[g],a[g][row]),(right[g],b[g][row])]:
                for wire,sel in enumerate(sels):
                    value=bool((initial[wire]>>row)&1) if wire<ni else v[wire-ni][row]
                    cnf.imply_equal(sel,picked,value)
            cnf.gate(a[g][row],b[g][row],v[g][row],op[g])
    for t,sels in zip(target,outs):
        cnf.one(sels)
        for g,sel in enumerate(sels):
            for row in range(n):cnf.imply_equal(sel,v[g][row],bool((t>>row)&1))
    for g in range(args.gates):
        uses=[sels[g] for sels in outs]
        uses += [left[k][ni+g] for k in range(g+1,args.gates)]
        uses += [right[k][ni+g] for k in range(g+1,args.gates)]
        cnf.clauses.append(uses)
    stem=args.output.with_suffix('')
    cp=Path(str(stem)+'.cnf');wp=Path(str(stem)+'.witness');lp=Path(str(stem)+'.solver.log')
    cnf.save(cp)
    result={'width':w,'colors':args.colors,'gates':args.gates,'rows':n,'initial_sources':initial,'targets':target,
            'variables':cnf.n,'clauses':len(cnf.clauses)}
    print(json.dumps(result),flush=True)
    start=time.monotonic()
    solver='/tmp/oec/pequalnp-pilot-13/lean_setup/lean-4.36.0-linux/bin/cadical'
    with lp.open('w') as log:
        p=subprocess.run([solver,'-t',str(args.seconds),'-w',str(wp),str(cp)],stdout=log,stderr=subprocess.STDOUT)
    result.update({'seconds':time.monotonic()-start,'solver_exit':p.returncode})
    if p.returncode==20:
        result['status']='UNSAT'
    elif p.returncode!=10:
        result['status']='UNKNOWN_timeout_or_error'
    else:
        model=set()
        for line in wp.read_text().splitlines():
            if line.startswith('v '):model.update(int(t) for t in line.split()[1:] if int(t)>0)
        assert all(any((x>0 and x in model) or (x<0 and -x not in model) for x in c) for c in cnf.clauses)
        values=list(initial);gates=[]
        for g in range(args.gates):
            p=next(i for i,x in enumerate(left[g]) if x in model)
            q=next(i for i,x in enumerate(right[g]) if x in model)
            typ='or' if op[g] in model else 'and'
            bits=values[p]|values[q] if typ=='or' else values[p]&values[q]
            values.append(bits);gates.append([typ,p,q,bits])
        outputs=[ni+next(i for i,x in enumerate(sels) if x in model) for sels in outs]
        assert [values[i] for i in outputs]==target
        result.update({'status':'SAT_verified_set_circuit','circuit':gates,'outputs':outputs})
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
