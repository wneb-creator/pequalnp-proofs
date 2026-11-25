import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import time

BASE=Path('/tmp/oec/pequalnp-pilot-96')
spec=importlib.util.spec_from_file_location('pilot_sat',BASE/'counterexample_sat.py')
sat=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sat)

def load_baseline(path):
    gates=[]
    for line in Path(path).read_text().splitlines():
        fields=line.split()
        if len(fields)==4 and fields[0].isdigit():
            index,op,a,b=map(int,fields)
            assert index==10+len(gates) and op in (0,1)
            assert 0<=a<index and 0<=b<index
            a,b=sorted((a+(a>=10),b+(b>=10)))
            gates.append((op,a,b))
    assert len(gates)==19
    return gates

def add_neighborhood(cnf,choices,baseline,max_changes):
    assert len(choices)==len(baseline) and 0<=max_changes<=len(choices)
    same=[]
    for (a,b,n,o),(op,left,right) in zip(choices,baseline):
        unchanged=cnf.new()
        same.append(unchanged)
        cnf.add(-unchanged,a[left])
        cnf.add(-unchanged,b[right])
        cnf.add(-unchanged,-n)
        cnf.add(-unchanged,o if op==1 else -o)
        # Ignore the OR bit at NOT by selecting its false representative.
        cnf.add(-n,-o)
    # Every max_changes+1 positions contain a marked unchanged position.
    # Marking implies equality; conversely all actually equal positions may
    # be marked. Thus existential marks encode the exact Hamming ball.
    for subset in itertools.combinations(same,max_changes+1):
        cnf.add(*subset)
    return same

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--seconds',type=int,default=900)
    ap.add_argument('--changes',type=int,default=4)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--baseline',type=Path,default=BASE/'counterexample-best.txt')
    args=ap.parse_args()
    baseline=load_baseline(args.baseline)
    baseline_wrong=sat.check(baseline)
    assert len(baseline_wrong)==6
    args.out.mkdir(exist_ok=True)
    rows=sorted(set(baseline_wrong)|{0}|{1<<i for i in range(10)}|{(1<<a)|(1<<b) for a,b in sat.EDGES}|{s for s in range(1024) if not sat.target(s) and all(sat.target(s|(1<<i)) for i in range(10) if not (s>>i&1))})
    print('BASELINE',len(baseline),'gates',len(baseline_wrong),'mismatches','MAX_CHANGES',args.changes,flush=True)
    start=time.monotonic()
    for iteration in range(20):
        cnf,choices=sat.encode(rows,19,'any',False)
        same=add_neighborhood(cnf,choices,baseline,args.changes)
        stem=args.out/f'iteration-{iteration:02d}'
        cnf.write(stem.with_suffix('.cnf'))
        seconds=max(1,args.seconds-int(time.monotonic()-start))
        print('ITERATION',iteration,'rows',len(rows),'vars',cnf.variables,'clauses',len(cnf.clauses),'remaining',seconds,flush=True)
        with stem.with_suffix('.stdout').open('w') as stdout,stem.with_suffix('.stderr').open('w') as stderr:
            proc=subprocess.run([str(BASE/'toolchain/lean-4.36.0-linux/bin/cadical'),'-q','-t',str(seconds),'--seed=92592096',str(stem.with_suffix('.cnf'))],stdout=stdout,stderr=stderr)
        print('SOLVER_EXIT',proc.returncode,'elapsed',round(time.monotonic()-start,2),flush=True)
        if proc.returncode==20:
            print('UNSAT only for this fixed gate-order Hamming neighborhood; no general or Lean-checked lower-bound claim.',flush=True)
            break
        if proc.returncode!=10:break
        text=stem.with_suffix('.stdout').read_text()
        truth={int(v) for line in text.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
        assert all(any((v in truth) if v>0 else (-v not in truth) for v in clause) for clause in cnf.clauses)
        gates=sat.decode(truth,choices)
        changed=[i for i,(g,h) in enumerate(zip(gates,baseline)) if tuple(g)!=tuple(h)]
        assert len(changed)<=args.changes
        assert any(g[0]==2 for g in gates)
        wrong=sat.check(gates)
        stem.with_suffix('.json').write_text(json.dumps({'gates':gates,'changed_positions':changed,'mismatches':wrong},indent=2)+'\n')
        print('MISMATCHES',len(wrong),'CHANGED',changed,flush=True)
        if not wrong:
            (args.out/'witness.json').write_text(json.dumps({'gates':gates,'false_wire':10,'actual_false_wire':29,'output':28},indent=2)+'\n')
            print('WITNESS',flush=True)
            break
        rows=sorted(set(rows)|set(wrong))
        if time.monotonic()-start>=args.seconds:break

if __name__=='__main__':main()
