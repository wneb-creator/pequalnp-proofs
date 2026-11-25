import argparse, hashlib, importlib.util, json, subprocess, time
from pathlib import Path

class CNF:
    def __init__(self, n):
        self.n = n
        self.cs = [[1]]
    def new(self):
        self.n += 1
        return self.n
    def add(self,*c):
        self.cs.append(list(c))
    def OR(self, xs):
        xs = list(dict.fromkeys(x for x in xs if x != -1))
        if 1 in xs or any(-x in xs for x in xs): return 1
        if not xs: return -1
        if len(xs)==1: return xs[0]
        z=self.new()
        for x in xs:self.add(-x,z)
        self.add(-z,*xs)
        return z
    def AND(self,xs):return -self.OR([-x for x in xs])
    def two(self,xs):
        one=-1;two=-1
        for x in xs:
            two=self.OR([two,self.AND([one,x])])
            one=self.OR([one,x])
        return two
    def write(self,path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.cs)}\n')
            for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',required=True)
    ap.add_argument('--solver',required=True)
    ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--per-solve',type=int,default=20)
    ap.add_argument('--steps',type=int,default=12)
    ap.add_argument('--resume',action='store_true')
    args=ap.parse_args()
    root=Path(args.root);out=root/'results/orch9248/frame-cegis';out.mkdir(exist_ok=True)
    spec=importlib.util.spec_from_file_location('rup',root/'results/orch9248/search/rup.py')
    rup=importlib.util.module_from_spec(spec);spec.loader.exec_module(rup)
    full=(1<<40)-1;n=args.steps
    def var(i,l):return 2+i*40+l
    cnf=CNF(1+n*40)
    for l in range(40):cnf.add(-var(n-1,l))
    frames=[];have=set()
    def add_frame(forced):
        if forced in have:return False
        false=rup.negate(forced)
        assert not forced&false
        unknown=full&~(forced|false)
        assert all(c&forced or (c&unknown).bit_count()>=2 for c in rup.php())
        stable=[]
        for i in range(n):
            sat=cnf.OR([var(i,l) for l in rup.literals(forced)])
            u2=cnf.two([var(i,l) for l in rup.literals(unknown)])
            st=cnf.OR([sat,u2])
            alive=cnf.OR([var(i,l) for l in rup.literals(full^false)])
            cnf.add(*[-s for s in stable],alive)
            stable.append(st)
        have.add(forced);frames.append(forced)
        return True
    add_frame(0)
    for l in range(40):
        ok,_,forced=rup.propagation(rup.php(),1<<l)
        assert not ok
        add_frame(forced)
    if args.resume and (out/'frames.json').exists():
        for f in json.loads((out/'frames.json').read_text()):add_frame(f)
    start=time.monotonic()
    iteration=json.loads((out/'status.json').read_text()).get('iteration',0) if args.resume and (out/'status.json').exists() else 0
    while time.monotonic()-start<args.seconds:
        iteration+=1
        prefix=out/f'iteration-{iteration:04d}'
        cnfpath=Path('/tmp/oec/pequalnp-pilot-103/frame-cegis/current.cnf');cnfpath.parent.mkdir(exist_ok=True);cnf.write(cnfpath)
        (out/'frames.json').write_text(json.dumps(frames)+'\n')
        so=prefix.with_suffix('.stdout');se=prefix.with_suffix('.stderr')
        with so.open('w') as f,se.open('w') as g:
            p=subprocess.run([args.solver,'-t',str(args.per_solve),'--seed='+str(iteration),str(cnfpath)],stdout=f,stderr=g)
        text=so.read_text()
        status={'iteration':iteration,'elapsed':time.monotonic()-start,'frames':len(frames),'variables':cnf.n,'clauses':len(cnf.cs),'solver_exit':p.returncode}
        if p.returncode==20:
            status['verdict']='UNSAT_SEMANTIC_OVERAPPROXIMATION'
            (out/'status.json').write_text(json.dumps(status,indent=2)+'\n')
            print(json.dumps(status),flush=True);return
        if p.returncode!=10:
            status['verdict']='UNKNOWN'
            (out/'status.json').write_text(json.dumps(status,indent=2)+'\n')
            print(json.dumps(status),flush=True)
            if p.returncode not in (0,):return
            continue
        model={int(t) for line in text.splitlines() if line.startswith('v ') for t in line[2:].split() if int(t)>0}
        run=[sum(1<<l for l in range(40) if var(i,l) in model) for i in range(n)]
        prefix.with_suffix('.model.json').write_text(json.dumps(run)+'\n')
        for forced in frames:
            false=rup.negate(forced);unknown=full&~(forced|false);oldstable=True
            for c in run:
                stable=bool(c&forced or (c&unknown).bit_count()>=2)
                dead=not(c&~false)
                assert not(oldstable and dead),('encoding',iteration,forced,c)
                oldstable &= stable
        database=rup.php();clean=[];added=0;invalid=0
        for c in run:
            if c&rup.negate(c):continue
            ok,hints,forced=rup.propagation(database,c)
            if not ok:
                invalid+=1
                added+=add_frame(forced)
            database.append(c);clean.append(c)
        (out/'frames.json').write_text(json.dumps(frames)+'\n')
        status.update(invalid_steps=invalid,new_frames=added,non_tautological_steps=len(clean))
        if not invalid:
            report=rup.check_run(clean)
            assert report['contains_empty']
            (out/'witness.json').write_text(json.dumps(report,indent=2)+'\n')
            status['verdict']='RUP_WITNESS'
            (out/'status.json').write_text(json.dumps(status,indent=2)+'\n')
            print(json.dumps(status),flush=True);return
        assert added>0
        status['verdict']='REFINING'
        (out/'status.json').write_text(json.dumps(status,indent=2)+'\n')
        print(json.dumps(status),flush=True)
    print(json.dumps({'verdict':'TIME_CAP','iterations':iteration,'frames':len(frames)}),flush=True)

if __name__=='__main__':main()
