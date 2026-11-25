"""Redundant capacity cut for a full circuit with every input and gate in its cone.

If D primaries have at least two distinct reader gates and F selector slots pick
the false sentinel, then D+F <= S+1-N. There are 2S-F nonfalse slots. The N
primaries use at least N+D such slots, and the S-1 nonoutput gate results use at
least S-1. The NOT rhs selector must be the false sentinel, as in search.make.
This helper expects the FULL schema, not only the variable tail of a prefix.
"""


def negate(value):
    return not value if isinstance(value,bool) else -value


def threshold(cnf,values,k):
    """Return a literal/bool equivalent to at least k positive input literals."""
    assert k>=1
    previous=[True]+[False]*k
    for x in values:
        current=[True]
        for t in range(1,k+1):
            # z iff a OR (x AND b), where a is old threshold t and b is t-1.
            a,b=previous[t],previous[t-1]
            z=cnf.var();current.append(z)
            cnf.simple(negate(a),z)
            cnf.simple(-x,negate(b),z)
            cnf.simple(a,x,-z)
            cnf.simple(a,b,-z)
        previous=current
    return previous[k]


def add_reader_capacity(cnf,schema,input_count=14):
    """Requires full cone constraints and canonical false rhs for unary NOT."""
    ops,lhs,rhs=schema
    size=len(ops)
    assert size>=1 and input_count>=1
    before_variables=cnf.n;before_clauses=len(cnf.clauses)
    multiple=[]
    for p in range(input_count):
        readers=[]
        for aa,bb in zip(lhs,rhs):
            # Membership in a gate input list, rather than counting p twice.
            a,b=aa[p],bb[p]
            reader=cnf.var();readers.append(reader)
            cnf.add(-a,reader);cnf.add(-b,reader);cnf.add(a,b,-reader)
        multiple.append(threshold(cnf,readers,2))
    false_slots=[v for aa,bb in zip(lhs,rhs) for v in [aa[-1],bb[-1]]]
    bound=size+1-input_count
    if bound<0:
        cnf.add()
    else:
        excessive=threshold(cnf,multiple+false_slots,bound+1)
        cnf.simple(negate(excessive))
    return {'gate_count':size,'input_count':input_count,'multiple_reader_flags':multiple,
            'false_slot_literals':false_slots,'bound':bound,
            'added_variables':cnf.n-before_variables,'added_clauses':len(cnf.clauses)-before_clauses,
            'requires':'Full schema, all primaries and nonoutput gates read, NOT rhs=false sentinel'}
