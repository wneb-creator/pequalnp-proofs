from pathlib import Path
import argparse, itertools, json, subprocess, time
from repair_nearmiss_v3 import CNF, SOLVER, SCRATCH

EDGES = [(0,4),(0,5),(0,6),(0,7),(1,4),(2,4),(3,4)]

def run(k, seconds, defect, basis, and_count=None, first=None, control=False, connected=False):
    c=CNF(); sels=[]; ops=[]
    for g in range(k):
        ops.append(c.new())
        a=[c.new() for _ in range(8+g)]
        b=[c.new() for _ in range(8+g)]
        c.choose(a); prefix_b=c.choose(b)
        for i in range(8+g): c.add(-a[i],-prefix_b[i])
        sels.append((a,b))
    # Every input is essential for this function, so it must occur as an operand.
    for i in range(8): c.add(*(ss[i] for ab in sels for ss in ab))
    if connected:
        # An additional, explicitly recorded search restriction.
        for g in range(k-1): c.add(*(ss[8+g] for ab in sels[g+1:] for ss in ab))
    if and_count is not None:
        assert 0 <= and_count <= k
        for cc in itertools.combinations(ops,and_count+1): c.add(*[-x for x in cc])
        for cc in itertools.combinations(ops,k-and_count+1): c.add(*cc)
    if first is not None:
        op,a,b=first
        c.add(ops[0] if op else -ops[0]);c.add(sels[0][0][a]);c.add(sels[0][1][b])
    if control:
        assert k==10
        known=[[0,1,2],[0,3,8],[1,4,9],[0,5,6],[0,7,11],[0,4,12],[1,0,13],[0,10,14],[0,1,15],[1,15,16]]
        for g,(op,a,b) in enumerate(known):
            c.add(ops[g] if op else -ops[g]);c.add(sels[g][0][a]);c.add(sels[g][1][b])
    def eval_cnf(mask):
        vals=[1 if mask>>i&1 else -1 for i in range(8)]; args=[]
        for g in range(k):
            a,b=[c.mux(s,vals) for s in sels[g]]
            args.append((a,b)); vals.append(c.op(ops[g],a,b))
        return vals,args
    def deriv_cnf(base,seed):
        vals,args=eval_cnf(1<<base)
        ds=[1 if i==seed else -1 for i in range(8)]
        for g in range(k):
            a,b=[c.mux(s,ds) for s in sels[g]]
            av,bv=args[g]
            andval=c.lor(c.land(av,b),c.land(a,bv)); orval=c.lor(a,b)
            v=c.new()
            c.add(-ops[g],-v,andval);c.add(-ops[g],v,-andval)
            c.add(ops[g],-v,orval);c.add(ops[g],v,-orval)
            ds.append(v)
        c.add(-ds[-1])
    def target(mask): return any(mask>>a&1 and mask>>b&1 for a,b in EDGES)
    # The optional basis is checked independently against all 256 assignments.
    if basis:
        positives=[(1<<a)|(1<<b) for a,b in EDGES]
        negatives=[15,240,238]
        assert all(target(m)==any(p&m==p for p in positives) for m in range(256))
        assert all(target(m) or any(m&n==m for n in negatives) for m in range(256))
        rows=positives+negatives
    else:rows=list(range(256))
    for mask in rows:
        vals,_=eval_cnf(mask);c.add(vals[-1] if target(mask) else -vals[-1])
    if defect:deriv_cnf(0,4);deriv_cnf(4,0)
    stem=SCRATCH/('double-star-'+str(k)+('-defect' if defect else '-ordinary')+('-basis' if basis else '-full')+('' if and_count is None else '-and'+str(and_count))+('' if first is None else '-first'+'-'.join(map(str,first)))+('-control' if control else '')+('-connected' if connected else '')+'-relevant')
    c.write(stem.with_suffix('.cnf'))
    start=time.time()
    with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
        p=subprocess.run([str(SOLVER),'-t',str(seconds),str(stem.with_suffix('.cnf'))],stdout=out,stderr=err)
    rec={'gates':k,'require_zero_derivatives':defect,'assignments':len(rows),'and_count':and_count,'first_gate':first,'fixed_control':control,'all_gates_used':connected,'variables':c.n,'clauses':len(c.cs),'solver_code':p.returncode,'seconds':round(time.time()-start,2)}
    if p.returncode==10:
        truth={int(t) for line in stem.with_suffix('.stdout').read_text().splitlines() if line.startswith('v ') for t in line[2:].split() if int(t)>0}
        gates=[]
        for g in range(k):
            a,b=[[i for i,s in enumerate(ss) if s in truth] for ss in sels[g]]
            assert len(a)==len(b)==1
            gates.append([int(ops[g] in truth),a[0],b[0]])
        def scalar(mask):
            v=[bool(mask>>i&1) for i in range(8)]
            for op,a,b in gates:v.append(v[a] and v[b] if op else v[a] or v[b])
            return v
        def derivative(base,seed):
            v=scalar(1<<base);d=[i==seed for i in range(8)]
            for op,a,b in gates:d.append((v[a] and d[b]) or (d[a] and v[b]) if op else d[a] or d[b])
            return d[-1]
        assert all(scalar(mask)[-1]==target(mask) for mask in range(256))
        dl,dr=derivative(0,4),derivative(4,0)
        if defect:assert not dl and not dr
        rec.update(gates_list=gates,derivative_left=dl,derivative_right=dr)
        stem.with_suffix('.witness.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--gates',type=int,required=True);p.add_argument('--seconds',type=int,default=60);p.add_argument('--defect',action='store_true');p.add_argument('--basis',action='store_true');p.add_argument('--and-count',type=int);p.add_argument('--first');p.add_argument('--control',action='store_true');p.add_argument('--connected',action='store_true')
    a=p.parse_args();run(a.gates,a.seconds,a.defect,a.basis,a.and_count,None if a.first is None else tuple(map(int,a.first.split(','))),a.control,a.connected)
