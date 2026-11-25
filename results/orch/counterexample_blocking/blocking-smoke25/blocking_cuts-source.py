"""CNF consequences of the six Lean-checked BlockingAll single-reader rules."""
import itertools
from search import N,E

DEGREE3={2,3,4,5,6,8,10,11,12,13}
EDGESET={tuple(sorted(e)) for e in E}


def add_blocking(cnf,schema,prefix):
    ops,lhs,rhs=schema
    base=N+len(prefix)
    initial=len(cnf.clauses)
    prefix_readers=[[] for _ in range(N)]
    for j,(op,a,b) in enumerate(prefix):
        for p in {a,b} if op<2 else {a}:
            if 0<=p<N:prefix_readers[p].append(j)

    def other_tail_readers(p,except_gate=-1):
        return [s for j in range(len(ops)) if j!=except_gate for s in [lhs[j][p],rhs[j][p]]]

    def known_bad(p,op,other):
        if op==2 or other<0:return False
        if other<N:return other!=p
        child,a,b=prefix[other-N]
        actual={a,b} if child<2 else {a}
        if child==2 and 0<=a<N and a!=p:return True
        if child==op and any(0<=q<N and q!=p for q in actual):return True
        if p in DEGREE3 and child<2 and 0<=a<N and 0<=b<N:
            if op==0 and child==1:return True
            if op==1 and child==0 and tuple(sorted((a,b))) not in EDGESET:return True
        return False

    # A primary already read once in the fixed prefix must be read again if
    # that fixed gate violates a necessary condition for a sole reader.
    for p,readers in enumerate(prefix_readers):
        if len(readers)!=1:continue
        op,a,b=prefix[readers[0]]
        if op<2:
            other=b if a==p else a
            if known_bad(p,op,other):cnf.add(*other_tail_readers(p))

    for r,(oo,aa,bb) in enumerate(zip(ops,lhs,rhs)):
        for p in range(N):
            if prefix_readers[p]:continue
            others=other_tail_readers(p,r)
            def forbid(*antecedent):
                cnf.add(*[-v for v in antecedent],*others)
            # Two distinct primary inputs at the current binary gate.
            for q in range(N):
                if q==p:continue
                for op in [0,1]:
                    if p<q:forbid(oo[op],aa[p],bb[q])
                    else:forbid(oo[op],aa[q],bb[p])
            # A fixed earlier partner can be classified directly.
            for j in range(len(prefix)):
                wire=N+j
                for op in [0,1]:
                    if known_bad(p,op,wire):forbid(oo[op],aa[p],bb[wire])
            # For a variable earlier partner, append its operation/fanin
            # selectors to the antecedent. A primary at current lhs is
            # forced by canonical binary fanin ordering.
            for j in range(r):
                wire=base+j
                child_ops,child_a,child_b=ops[j],lhs[j],rhs[j]
                for q in range(N):
                    if q==p:continue
                    for op in [0,1]:
                        forbid(oo[op],aa[p],bb[wire],child_ops[2],child_a[q])
                        forbid(oo[op],aa[p],bb[wire],child_ops[op],child_a[q])
                        forbid(oo[op],aa[p],bb[wire],child_ops[op],child_b[q])
                if p in DEGREE3:
                    for a in range(N):
                        for b in range(a,N):
                            forbid(oo[0],aa[p],bb[wire],child_ops[1],child_a[a],child_b[b])
                            if (a,b) not in EDGESET:
                                forbid(oo[1],aa[p],bb[wire],child_ops[0],child_a[a],child_b[b])
    return {'added_clauses':len(cnf.clauses)-initial,'frozen_readers':[len(x) for x in prefix_readers]}
