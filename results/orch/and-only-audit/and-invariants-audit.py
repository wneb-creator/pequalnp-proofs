from itertools import combinations

def audit(n,f):
    z=[x for x in range(1<<n) if not f(x) and all((x>>i)&1 or f(x|(1<<i)) for i in range(n))]
    ones=[x for x in range(1<<n) if f(x) and all(not ((x>>i)&1) or not f(x^(1<<i)) for i in range(n))]
    return {'maxfalse':z,'mintrue':ones,'clauses':[[i for i in range(n) if not (x>>i)&1] for x in z]}

def shared(x):
    a,b,c,d,e,f=[bool((x>>i)&1) for i in range(6)]
    h=a and b
    return ((h or c) and d) or ((h or e) and f)
print('Shared AND, 3 paid AND gates:',audit(6,shared))

def p4(x):
    a,b,c,d=[bool((x>>i)&1) for i in range(4)]
    return ((a or c) and (b or d)) and (b or c)
assert all(p4(x)==any((x>>a)&1 and (x>>b)&1 for a,b in [(0,1),(1,2),(2,3)]) for x in range(16))
print('P4 shared first birth verified:',audit(4,p4))
