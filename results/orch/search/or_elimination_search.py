import json,time,z3
from pathlib import Path
from counterexample_sparse_sat import extrema

# Search for a sound compact OR program where replacing ANY OR by EITHER
# operand loses at least two required graph edges. ANDs are free/unbounded.
def search(n,edges,k,timeout=90000):
    started=time.monotonic()
    tests,ne,mis=extrema(n,edges)
    width=len(tests); mw=n+k
    ones=z3.BitVecVal((1<<width)-1,width)
    inputs=[z3.BitVecVal(sum(1<<j for j,a in enumerate(tests) if a>>i&1),width) for i in range(n)]
    masks=[(z3.BitVec('a'+str(j),mw),z3.BitVec('b'+str(j),mw)) for j in range(k)]
    output=z3.BitVec('output',mw)
    so=z3.SolverFor('QF_BV');so.set(timeout=timeout)
    def meet(mask,values):
        v=ones
        for i,w in enumerate(values):
            v=v & z3.If(z3.Extract(i,i,mask)==1,w,ones)
        return v
    def run(replace=-1,side=0):
        values=inputs[:]
        for j,(a,b) in enumerate(masks):
            va,vb=meet(a,values),meet(b,values)
            values.append((va if side==0 else vb) if j==replace else va|vb)
        return meet(output,values)
    for j,(a,b) in enumerate(masks):
        so.add(z3.ULT(a,1<<(n+j)),z3.ULT(b,1<<(n+j)),z3.ULE(a,b))
    so.add(run()==(1<<ne)-1)
    for j in range(k):
        for side in range(2):
            val=run(j,side)
            # At least two positive test bits turn false.
            so.add(z3.PbGe([(z3.Extract(e,e,val)==0,1) for e in range(ne)],2))
    rr=so.check()
    result={'n':n,'edges':edges,'or_gates':k,'result':str(rr),'seconds':time.monotonic()-started,'all_replacements_lose_at_least':2}
    if rr==z3.unknown:result['reason']=so.reason_unknown()
    if rr==z3.sat:
        model=so.model()
        result['masks']=[(model.eval(a).as_long(),model.eval(b).as_long()) for a,b in masks]
        result['output']=model.eval(output).as_long()
        # Independent concrete full-truth replay and edge-loss validation.
        def concrete(bits,replace=-1,side=0):
            vals=[bool(bits>>i&1) for i in range(n)]
            def conjunction(mask):return all(v for i,v in enumerate(vals) if mask>>i&1)
            for j,(a,b) in enumerate(result['masks']):
                va,vb=conjunction(a),conjunction(b)
                vals.append((va if side==0 else vb) if j==replace else va or vb)
            return conjunction(result['output'])
        result['truth_errors']=[x for x in range(1<<n) if concrete(x)!=any(x>>u&1 and x>>v&1 for u,v in edges)]
        result['losses']=[[sum(not concrete((1<<u)|(1<<v),j,side) for u,v in edges) for side in range(2)] for j in range(k)]
    return result

if __name__=='__main__':
    z3.set_param('memory_max_size',256)
    cases=[('C5',5,[(i,(i+1)%5) for i in range(5)],4),('C5',5,[(i,(i+1)%5) for i in range(5)],5),('C6',6,[(i,(i+1)%6) for i in range(6)],5),('two_stars',6,[(0,1),(0,2),(3,4),(3,5)],3)]
    for name,n,edges,k in cases:
        print(json.dumps({'starting':name,'or_gates':k}),flush=True)
        result=search(n,edges,k);result['name']=name
        with Path('/tmp/oec/pequalnp-pilot-55/or-elimination-results.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
        print(json.dumps(result),flush=True)
