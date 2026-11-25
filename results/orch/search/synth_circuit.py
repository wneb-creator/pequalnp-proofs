import argparse
import ctypes
import itertools
import json
import random
import re
import time

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
TARGET = sum(any((x>>a)&(x>>b)&1 for a,b in EDGES)<<x for x in range(1024))
INPUTS = [sum(((x>>i)&1)<<x for x in range(1024)) for i in range(10)]
FULL = (1<<1024)-1

class Z3:
    def __init__(self):
        self.z = ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
        for name,args,res in [('Z3_mk_config',[],ctypes.c_void_p),('Z3_mk_context',[ctypes.c_void_p],ctypes.c_void_p),('Z3_del_config',[ctypes.c_void_p],None),('Z3_del_context',[ctypes.c_void_p],None),('Z3_eval_smtlib2_string',[ctypes.c_void_p,ctypes.c_char_p],ctypes.c_char_p)]:
            f=getattr(self.z,name);f.argtypes=args;f.restype=res
        c=self.z.Z3_mk_config();self.ctx=self.z.Z3_mk_context(c);self.z.Z3_del_config(c)
    def run(self,s):
        return self.z.Z3_eval_smtlib2_string(self.ctx,s.encode()).decode()
    def __del__(self):
        self.z.Z3_del_context(self.ctx)

def solve(samples,size,timeout,seed,one_not=True,not_position=None,ordered=False,signed=False,near=None,max_changes=3,not_count=None):
    w=len(samples)
    bv=lambda v,n:f'(_ bv{v} {n})'
    smt=['(set-logic QF_BV)',f'(set-option :timeout {timeout})',f'(set-option :smt.random_seed {seed})',f'(set-option :sat.random_seed {seed})']
    wires=[bv(sum(((x>>i)&1)<<j for j,x in enumerate(samples)),w) for i in range(10)]
    names=[]
    nots=[]
    for g in range(size):
        a,b,o=f'a{g}',f'b{g}',f'o{g}'
        names.extend([a,b,o]);nots.append(f'(= {o} #b10)')
        smt.extend([f'(declare-const {a} (_ BitVec 5))',f'(declare-const {b} (_ BitVec 5))',f'(declare-const {o} (_ BitVec 2))'])
        smt.extend([f'(assert (bvult {a} {bv(10+g,5)}))',f'(assert (bvult {b} {bv(10+g,5)}))'])
        if signed:
            smt.append(f'(assert (bvult {a} {b}))')
        else:
            smt.extend([f'(assert (bvule {o} #b10))',f'(assert (=> (= {o} #b10) (= {b} #b00000)))',f'(assert (=> (not (= {o} #b10)) (bvult {a} {b})))'])
        if not_position is not None:
            smt.append(f'(assert {nots[-1] if g==not_position else "(not "+nots[-1]+")"})')
            if not_position==0 and g==0: smt.append('(assert (= a0 #b00000))')
        if ordered:
            maxdef=b if signed else f'(ite (= {o} #b10) {a} {b})'
            mindef=a if signed else f'(ite (= {o} #b10) #b00000 {a})'
            smt.extend([f'(define-fun max{g} () (_ BitVec 5) {maxdef})',f'(define-fun min{g} () (_ BitVec 5) {mindef})'])
            if g:
                smt.append(f'(assert (bvule max{g-1} max{g}))')
                smt.append(f'(assert (=> (= max{g-1} max{g}) (bvule min{g-1} min{g})))')
                smt.append(f'(assert (=> (and (= max{g-1} max{g}) (= min{g-1} min{g})) (bvult o{g-1} {o})))')
        def mux(sel):
            val=wires[-1]
            for i in range(len(wires)-2,-1,-1): val=f'(ite (= {sel} {bv(i,5)}) {wires[i]} {val})'
            return val
        negcase=f'(ite (= {o} #b10) (bvand u{g} (bvnot t{g})) (bvand (bvnot u{g}) t{g}))' if signed else f'(bvnot u{g})'
        smt.extend([f'(define-fun u{g} () (_ BitVec {w}) {mux(a)})',f'(define-fun t{g} () (_ BitVec {w}) {mux(b)})',f'(declare-const v{g} (_ BitVec {w}))',f'(assert (= v{g} (ite (= {o} #b00) (bvand u{g} t{g}) (ite (= {o} #b01) (bvor u{g} t{g}) {negcase}))))'])
        wires.append(f'v{g}')
    if not signed: smt.append('(assert (or '+' '.join(nots)+'))')
    if one_not and not signed:
        for a,b in itertools.combinations(nots,2): smt.append(f'(assert (not (and {a} {b})))')
    if not_count is not None:
        count=f'(ite {nots[0]} #b00001 #b00000)'
        for term in nots[1:]:count=f'(bvadd {count} (ite {term} #b00001 #b00000))'
        smt.append(f'(assert (= {count} {bv(not_count,5)}))')
    if near is not None:
        terms=[]
        for g,(o,a,b) in enumerate(near):
            if o in (0,1):a,b=sorted((a,b))
            else:b=0
            terms.append(f'(ite (and (= o{g} {bv(o,2)}) (= a{g} {bv(a,5)}) (= b{g} {bv(b,5)})) #b00000 #b00001)')
        count=terms[0]
        for term in terms[1:]:count=f'(bvadd {count} {term})'
        smt.append(f'(assert (bvule {count} {bv(max_changes,5)}))')
    # Every nonfinal gate is used. A minimum useful witness obeys this normal form.
    for g in range(size-1):
        smt.append('(assert (or '+' '.join(f'(= {v}{h} {bv(10+g,5)})' for h in range(g+1,size) for v in ['a','b'])+'))')
    target=sum(((TARGET>>x)&1)<<j for j,x in enumerate(samples))
    smt.append(f'(assert (= v{size-1} {bv(target,w)}))')
    z=Z3();z.run('\n'.join(smt))
    t=time.monotonic();r=z.run('(check-sat)');elapsed=time.monotonic()-t
    if r.strip()!='sat': return r.strip(),None,elapsed
    r=z.run('(get-value ('+' '.join(names)+'))')
    vals={name:int(bits,16 if pref=='x' else 2) for name,pref,bits in re.findall(r'\(([abo]\d+) #([bx])([0-9a-f]+)\)',r)}
    return 'sat',[(vals[f'o{g}'],vals[f'a{g}'],vals[f'b{g}']) for g in range(size)],elapsed

def check(gates,signed=False):
    wires=INPUTS[:]
    for o,a,b in gates:
        if signed:
            wires.append(wires[a]&wires[b] if o==0 else wires[a]|wires[b] if o==1 else wires[a]&(FULL^wires[b]) if o==2 else (FULL^wires[a])&wires[b])
        else:
            wires.append(wires[a]&wires[b] if o==0 else wires[a]|wires[b] if o==1 else FULL^wires[a])
    return [x for x in range(1024) if ((wires[-1]^TARGET)>>x)&1]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--size',type=int,default=19);ap.add_argument('--timeout',type=int,default=120000);ap.add_argument('--seed',type=int,default=0);ap.add_argument('--not-position',type=int);ap.add_argument('--out',required=True);ap.add_argument('--many-nots',action='store_true');ap.add_argument('--all-minimal',action='store_true');ap.add_argument('--ordered',action='store_true');ap.add_argument('--signed',action='store_true');ap.add_argument('--near-log');ap.add_argument('--max-changes',type=int,default=3);ap.add_argument('--not-count',type=int);args=ap.parse_args()
    rng=random.Random(args.seed)
    samples=sorted(set([0,1023]+[1<<i for i in range(10)]+[(1<<a)|(1<<b) for a,b in EDGES]+rng.sample(range(1024),24)))
    if args.all_minimal:
        samples=sorted(set(samples+[x for x in range(1024) if not((TARGET>>x)&1)]))
    near=None
    if args.near_log:
        with open(args.near_log) as f:rows=re.findall(r'score=(\d+).*?gates=(\[.*\])',f.read())
        near=json.loads(min(rows,key=lambda t:int(t[0]))[1]);samples=sorted(set(samples+check(near,args.signed)))
    for iteration in range(60):
        status,gates,elapsed=solve(samples,args.size,args.timeout,args.seed,not args.many_nots,args.not_position,args.ordered,args.signed,near,args.max_changes,args.not_count)
        print(json.dumps({'iteration':iteration,'samples':len(samples),'status':status,'seconds':elapsed}),flush=True)
        if gates is None: return
        bad=check(gates,args.signed)
        print(json.dumps({'gates':gates,'mismatches':len(bad)}),flush=True)
        if not bad:
            with open(args.out,'w') as f:json.dump({'gates':gates,'edges':EDGES},f,indent=2)
            print('WITNESS_FOUND',flush=True);return
        samples=sorted(set(samples+rng.sample(bad,min(16,len(bad)))))

if __name__=='__main__': main()
