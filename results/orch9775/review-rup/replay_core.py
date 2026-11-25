"""Independent semantic-scheme and ordinary dictionary-UP replay of trimmed cores."""
import json
import sys
import hashlib
from pathlib import Path

EDGES = [(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),
         (3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
ADJ = {frozenset(e) for e in EDGES}

def adjacent(a, b):
    return frozenset((a, b)) in ADJ

def independent(mask):
    return not any(mask >> a & 1 and mask >> b & 1 for a, b in EDGES)

def expansion(scheme, k, mask, weak):
    tag, *a = scheme
    pos = lambda *f: (tuple(f), True)
    neg = lambda *f: (tuple(f), False)
    common = lambda x, c: ('common', min(x,c), max(x,c))
    cap = lambda x: 1 if mask >> x & 1 else 2+k
    if tag == 'self':
        x,j=a; return [pos('lab',x,j,x)]
    if tag == 'earlier':
        x,j=a; return [neg('live',x,j+1),pos('live',x,j)]
    if tag == 'labCommon':
        x,c,j=a; return [neg('live',x,j),neg('lab',x,j,c),pos(*common(x,c))]
    if tag == 'someRes':
        x,=a; return [neg('live',x,2)]+[pos('res',t,x) for t in range(k)]
    if tag == 'allRes':
        x,t=a; assert t<k; return [neg('live',x,1+k),pos('res',t,x)]
    if tag == 'exposure':
        x,m=a; assert independent(m) and any(m>>v&1 and adjacent(x,v) for v in range(14))
        return [pos('avoid',x,m,j) for j in range(cap(x))]
    if tag == 'exactAt':
        x,i,m=a; assert not weak and independent(m) and mask>>i&1 and m>>x&1 and adjacent(i,x)
        return [pos('see',x,i,m,j) for j in range(cap(x))]
    if tag == 'avoidLive':
        x,m,j=a; return [neg('avoid',x,m,j),pos('live',x,j)]
    if tag == 'seeLive':
        x,i,m,j=a; return [neg('see',x,i,m,j),pos('live',x,j)]
    if tag == 'avoidNot':
        x,c,m,j=a; assert m>>c&1; return [neg('avoid',x,m,j),neg('lab',x,j,c)]
    if tag == 'seeLab':
        x,i,c,m,j=a; assert m>>c&1
        return [neg('see',x,i,m,j),(('lab',x,j,c),adjacent(i,c))]
    if tag == 'diffX':
        t,x,c=a; return [neg('diff',t,x,c),pos('res',t,x)]
    if tag == 'diffC':
        t,x,c=a; return [neg('diff',t,x,c),neg('res',t,c)]
    if tag == 'adjacentCommon':
        x,c,i=a; assert mask>>i&1 and adjacent(i,x) and adjacent(i,c)
        return [pos(*common(x,c))]
    if tag == 'resCommon':
        x,c,t=a; return [neg('res',t,x),neg('res',t,c),pos(*common(x,c))]
    if tag == 'residual':
        x,c,j,l=a; assert x!=c and not(mask>>x&1) and j<l
        return [neg(*common(x,c)),neg('live',x,l),pos('lab',x,j,c),pos('lab',x,l,c)]+[pos('diff',t,x,c) for t in range(k)]
    if tag == 'readerAny':
        s,e=a; return [pos('reader',s,e,j) for j in range(cap(EDGES[e][int(s)]))]
    if tag == 'readerLive':
        s,e,j=a; return [neg('reader',s,e,j),pos('live',EDGES[e][int(s)],j)]
    if tag == 'readerLab':
        s,e,j,c,d=a; return [neg('reader',s,e,j),(('lab',EDGES[e][int(s)],j,c),not d),(('es',s,e,c),d)]
    if tag == 'eqLab':
        s,e,f,c,d=a; return [neg('gate',e,f),(('es',s,e,c),not d),(('es',s,f,c),d)]
    if tag == 'gateEq':
        s,e,f,j=a; assert EDGES[e][int(s)]==EDGES[f][int(s)]
        return [neg('reader',s,e,j),neg('reader',s,f,j),pos('gate',e,f)]
    if tag == 'pairedExact':
        x,i,y,j,m=a
        assert weak and independent(m) and mask>>i&1 and mask>>j&1 and m>>x&1 and m>>y&1
        assert adjacent(i,x) and adjacent(j,y) and any(m>>v&1 and adjacent(j,v) and not adjacent(i,v) for v in range(14))
        return [pos('see',x,i,m,r) for r in range(cap(x))]+[pos('see',y,j,m,r) for r in range(cap(y))]
    raise AssertionError(('unknown scheme',scheme))

def check_rup(book, boundary, clause, hints):
    assignment = {}
    for variable, sign in clause:
        assert type(sign) is bool
        if variable in assignment:
            assert assignment[variable] == (not sign), 'tautology not supported by this replay'
        assignment[variable] = not sign
    for ref in hints:
        assert isinstance(ref,int) and 0<=ref<boundary
        remaining = {(v,s) for v,s in book[ref] if v not in assignment or assignment[v] == s}
        if not remaining:
            return True
        assert len(remaining)==1, ('not a unit reason',boundary,ref)
        variable, sign = remaining.pop()
        if variable in assignment:
            assert assignment[variable] == sign
        assignment[variable] = sign
    raise AssertionError(('no falsified reason clause',boundary))

def replay(data):
    facts, book, base = data['facts'], data['book'], data['base_count']
    assert len(data['schemes'])==base and len(data['rows'])==len(book)-base
    for c in book:
        assert all(isinstance(v,int) and 0<=v<len(facts) and type(s) is bool for v,s in c)
    for index, scheme in enumerate(data['schemes']):
        wanted = set(expansion(scheme,data['k'],data['I'],data.get('no_exact',False)))
        actual = {(tuple(facts[v]),s) for v,s in book[index]}
        assert wanted <= actual, ('initial scheme mismatch',index,scheme,wanted-actual)
    for offset, hints in enumerate(data['rows']):
        check_rup(book,base+offset,book[base+offset],hints)
    check_rup(book,len(book),[],data['last_hints'])
    return dict(I=data['I'],k=data['k'],weak=data.get('no_exact',False),
                facts=len(facts),base=base,learned=len(data['rows']),
                all_initial_schemes_checked=True,all_rup_rows_checked=True,
                final_assumption_free_conflict_checked=True)

if __name__=='__main__':
    for filename in sys.argv[1:]:
        path=Path(filename); raw=path.read_bytes(); data=json.loads(raw)
        result=replay(data)
        result.update(source=str(path),sha256=hashlib.sha256(raw).hexdigest())
        print(json.dumps(result),flush=True)
