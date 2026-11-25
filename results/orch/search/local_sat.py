import ctypes
import itertools
import json
from pathlib import Path
import random
import runpy
import sys
import time

ROOT=Path('/tmp/oec/pequalnp-pilot-87/counterexample')
core=runpy.run_path(str(ROOT/'synth.py'))
edges=core['EDGES'];target=core['target'];evaluate=core['evaluate']
lib=ctypes.CDLL(str(ROOT/'libcadical.so'))
lib.sat_init.argtypes=[];lib.sat_init.restype=ctypes.c_void_p
for f in ['add','assume','freeze']:
    getattr(lib,'sat_'+f).argtypes=[ctypes.c_void_p,ctypes.c_int]
    getattr(lib,'sat_'+f).restype=None
lib.sat_solve.argtypes=[ctypes.c_void_p];lib.sat_solve.restype=ctypes.c_int
lib.sat_val.argtypes=[ctypes.c_void_p,ctypes.c_int];lib.sat_val.restype=ctypes.c_int
lib.sat_set_option.argtypes=[ctypes.c_void_p,ctypes.c_char_p,ctypes.c_int];lib.sat_set_option.restype=None
lib.sat_limit.argtypes=[ctypes.c_void_p,ctypes.c_char_p,ctypes.c_int];lib.sat_limit.restype=None
lib.sat_release.argtypes=[ctypes.c_void_p];lib.sat_release.restype=None
CB=ctypes.CFUNCTYPE(ctypes.c_int,ctypes.c_void_p)
lib.sat_set_terminate.argtypes=[ctypes.c_void_p,ctypes.c_void_p,CB]
deadline=0
@CB
def terminate(_):
    return int(time.monotonic()>deadline)

def seed(rng):
    covers=[s for s in itertools.combinations(range(10),6) if all(a in s or b in s for a,b in edges)]
    cover=list(rng.choice(covers));rng.shuffle(cover)
    ns={a:[] for a in cover}
    for a,b in edges:
        if a in cover and (b not in cover or rng.randrange(2)):ns[a].append(b)
        else:ns[b].append(a)
    gs=[];stars=[]
    for a in cover:
        rng.shuffle(ns[a]);v=ns[a][0]+1
        for b in ns[a][1:]:gs.append((1,min(v,b+1),max(v,b+1)));v=10+len(gs)
        gs.append((0,min(a+1,v),max(a+1,v)));stars.append(10+len(gs))
    rng.shuffle(stars);v=stars[0]
    for b in stars[1:]:gs.append((1,min(v,b),max(v,b)));v=10+len(gs)
    assert len(gs)==20
    assert all(evaluate(gs,x)[-1]==target(x) for x in range(1024))
    return gs

def main():
    global deadline
    start=time.monotonic();rng=random.Random(237324)
    promise='--promise' in sys.argv
    rows=[x for x in range(1024) if x.bit_count()<=2 or not target(x)] if promise else list(range(1024))
    cnf,typ,left,right=core['encode'](rows,20,None,False,False,False)
    skips=[cnf.var() for _ in range(19)]
    for i,s in enumerate(skips):
        cnf.clause(-s,typ[i][1])
        for a in range(len(left[i])):cnf.clause(-s,-left[i][a],right[i][a])
    print('local SAT vars',cnf.nvars,'clauses',len(cnf.clauses),flush=True)
    solver=lib.sat_init();lib.sat_set_option(solver,b'quiet',1)
    lib.sat_set_terminate(solver,None,terminate)
    for v in skips+[v for ts in typ+left+right for v in ts]:lib.sat_freeze(solver,v)
    for c in cnf.clauses:
        for v in c:lib.sat_add(solver,v)
        lib.sat_add(solver,0)
    print('loaded seconds',time.monotonic()-start,flush=True)
    counts={0:0,10:0,20:0}
    gs=seed(rng)
    # Positive control: all gates fixed to a verified20-gate circuit.
    for i,(op,a,b) in enumerate(gs):
        for v in [typ[i][op],left[i][a],right[i][b]]:lib.sat_assume(solver,v)
    deadline=time.monotonic()+30
    result=lib.sat_solve(solver)
    print('positive control',result,flush=True)
    assert result==10
    for trial in range(10000):
        if time.monotonic()-start>600:break
        if trial%30==0:gs=seed(rng)
        d=rng.randrange(19);size=4+trial%7
        related={d}
        related.update(i for i,g in enumerate(gs) if d+11 in g[1:])
        related.update(a-11 for a in gs[d][1:] if a>=11)
        relax=set(rng.sample(range(20),min(size,20)))|related
        lib.sat_assume(solver,skips[d])
        for i,(op,a,b) in enumerate(gs):
            if i in relax:continue
            for v in [typ[i][op],left[i][a],right[i][b]]:lib.sat_assume(solver,v)
        lib.sat_limit(solver,b'conflicts',3000)
        deadline=time.monotonic()+2
        result=lib.sat_solve(solver);counts[result]+=1
        if result==10:
            def chosen(vs):return next(i for i,v in enumerate(vs) if lib.sat_val(solver,v)>0)
            out=[(chosen(typ[i]),chosen(left[i]),chosen(right[i])) for i in range(20)]
            assert out[d][0]==1 and out[d][1]==out[d][2]
            missed=[x for x in range(1024) if evaluate(out,x)[-1]!=target(x)]
            if missed:
                print('PROMISE_ONLY trial',trial,'bad rows',missed,flush=True)
                for i,(op,a,b) in enumerate(out):
                    for v in [typ[i][op],left[i][a],right[i][b]]:lib.sat_add(solver,-v)
                lib.sat_add(solver,0)
                continue
            copy=out[d][1]
            out.pop(d)
            def fix(a):return copy if a==d+11 else a-1 if a>d+11 else a
            out=[(op,fix(a),fix(b)) for op,a,b in out]
            assert all(evaluate(out,x)[-1]==target(x) for x in range(1024))
            a,b=out[-1][1:]
            exclusive=[[],[]]
            for row in range(1024):
                vals=evaluate(out,row)
                if vals[a] and not vals[b]:exclusive[0].append(row)
                if vals[b] and not vals[a]:exclusive[1].append(row)
            print('FULL_FUNCTION',out,'exclusive examples',[xs[:4] for xs in exclusive],flush=True)
            if all(exclusive):print('TARGET_REFUTATION_CANDIDATE',flush=True)
            (ROOT/'local-sat-witness.json').write_text(json.dumps(out))
            break
        if trial%50==0:print('trial',trial,'counts',counts,'elapsed',time.monotonic()-start,flush=True)
    print('DONE counts',counts,'elapsed',time.monotonic()-start,flush=True)
    lib.sat_release(solver)

if __name__=='__main__':main()
