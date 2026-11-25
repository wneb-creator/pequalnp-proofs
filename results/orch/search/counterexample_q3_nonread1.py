import argparse
import json
import sys
import subprocess
import time
from pathlib import Path
import counterexample_q3_minimal as base

forced_pair=(0,13)
original_neighborhood=base.neighborhood

def neighborhood(rng,trial):
    global forced_pair
    seed,free,details=original_neighborhood(rng,trial)
    actual=base.evaluate(seed,base.POSITIVE)
    lost=[edge for k,edge in enumerate(base.EDGES) if not (actual>>k)&1]
    assert lost
    forced_pair=lost[0]
    details['forced_nonread1_edge']=forced_pair
    return seed,free,details

class Encoding(base.Encoding):
    def __init__(self,seed,free,patterns):
        super().__init__(seed,free,patterns)
        self.pair=forced_pair
        self.proof=[[self.var() for _ in range(3)] for _ in seed]
        self.proof_left={};self.proof_right={};self.products={}
        for i,(op,a,b) in enumerate(seed):
            if i in self.free:
                left=[self.var() for _ in range(3)]
                right=[self.var() for _ in range(3)]
                self.proof_left[i]=left;self.proof_right[i]=right
                for selections,bits in ((self.lhs[i],left),(self.rhs[i],right)):
                    for wire,sel in enumerate(selections):
                        for k,bit in enumerate(bits):
                            w=self.proof_wire(wire,k)
                            self.add(-sel,-bit,w);self.add(-sel,bit,-w)
                o=self.ops[i]
                and_guard=[-o];or_guard=[o]
            else:
                left=[self.proof_wire(a,k) for k in range(3)]
                right=[self.proof_wire(b,k) for k in range(3)]
                and_guard=[];or_guard=[]
            vals=self.proof[i]
            if op or i in self.free:
                self.add(*and_guard,-vals[0]);self.add(*and_guard,-vals[1])
                u,v=self.var(),self.var();self.products[i]=(u,v)
                for z,x,y in ((u,left[0],right[1]),(v,left[1],right[0])):
                    self.add(-z,x);self.add(-z,y);self.add(z,-x,-y)
                self.or_equiv(vals[2],u,v,and_guard)
            if not op or i in self.free:
                for z,x,y in zip(vals,left,right):self.or_equiv(z,x,y,or_guard)
        self.add(-self.proof[-1][2])

    def or_equiv(self,z,x,y,guard):
        self.add(*guard,z,-x);self.add(*guard,z,-y);self.add(*guard,-z,x,y)

    def proof_wire(self,w,k):
        if w>=base.NINPUT:return self.proof[w-base.NINPUT][k]
        value=(w==self.pair[0]) if k==0 else (w==self.pair[1]) if k==1 else False
        return self.truth if value else -self.truth

    def known_assignment(self):
        assignment=super().known_assignment()
        p,q=self.pair
        vals=[(i==p,i==q,False) for i in range(base.NINPUT)]
        for i,(op,a,b) in enumerate(self.seed):
            if i in self.free:a,b=sorted((a,b))
            x,y=vals[a],vals[b]
            if i in self.free:
                for var,value in zip(self.proof_left[i],x):assignment[var]=value
                for var,value in zip(self.proof_right[i],y):assignment[var]=value
            if i in self.products:
                u,v=self.products[i]
                assignment[u]=x[0] and y[1];assignment[v]=x[1] and y[0]
            z=(False,False,(x[0] and y[1]) or(x[1] and y[0])) if op else tuple(x[k] or y[k] for k in range(3))
            vals.append(z)
            for var,value in zip(self.proof[i],z):assignment[var]=value
        return assignment

def reads_pair(circuit,pair):
    p,q=pair
    vals=[(i==p,i==q,False) for i in range(base.NINPUT)]
    for op,a,b in circuit:
        x,y=vals[a],vals[b]
        vals.append((False,False,(x[0] and y[1]) or(x[1] and y[0])) if op else tuple(x[k] or y[k] for k in range(3)))
    return vals[-1][2]

def control():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True)
    ap.add_argument('--proof-control',action='store_true');args=ap.parse_args()
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    seed=json.loads(Path(__file__).with_name('q3-67-charge-probe.json').read_text())['circuit']
    free=[0,1,2,3,4,66]
    patterns=base.POSITIVE+base.NEGATIVE+[1<<v for v in range(base.NINPUT)]
    assert not reads_pair(seed,forced_pair)
    e=Encoding(seed,free,patterns);e.least_or_strict();e.least_singleton()
    cnf=root/'control.cnf';e.write(cnf);phase=root/'control.phases';e.write_phases(phase)
    start=time.monotonic()
    with (root/'control.log').open('w') as out:
        r=subprocess.run([args.solver,str(cnf),str(phase),'60','1000000'],stdout=out,stderr=subprocess.STDOUT)
    report=dict(status=r.returncode,seconds=time.monotonic()-start,variables=e.count,clauses=len(e.clauses))
    if r.returncode==10:
        circuit=e.decode((root/'control.log').read_text())
        report['all_boundary_errors']=(base.evaluate(circuit,base.POSITIVE+base.NEGATIVE)^((1<<len(base.POSITIVE))-1)).bit_count()
        report['forced_pair_read1']=reads_pair(circuit,forced_pair)
        report['circuit']=circuit
    (root/'control.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

base.Encoding=Encoding
base.neighborhood=neighborhood
if __name__=='__main__':
    if '--proof-control' in sys.argv:control()
    else:base.main()
