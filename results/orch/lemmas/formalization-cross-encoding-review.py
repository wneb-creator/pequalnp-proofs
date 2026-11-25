import hashlib
import itertools
import json
import sys
from pathlib import Path

BASE = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('/tmp/oec/pequalnp-pilot-81')

def cnf(path):
    lines = path.read_text().splitlines()
    _, _, nv, nc = lines[0].split()
    clauses = [list(map(int, line.split()))[:-1] for line in lines[1:]]
    assert len(clauses) == int(nc)
    return int(nv), clauses

inputs = [sum(1 << m for m in range(16384) if (m >> i) & 1) for i in range(14)]
def truth(control):
    values = []
    for atom in control['atoms']:
        slots = []
        for slot in atom['slots']:
            word = 0
            for i in slot['primary']:
                word |= inputs[i]
            for j in slot['prior']:
                assert j < len(values)
                word |= values[j]
            slots.append(word)
        values.append(slots[0] & slots[1])
    output = 0
    for j in control['final']:
        output |= values[j]
    expected = 0
    for p in range(7):
        for line in range(7):
            if ((p - line) % 7 in (0, 1, 3)) if control['graph'] == 'fano' else p == line:
                expected |= inputs[p] & inputs[7 + line]
    assert output == expected

def trace(control, base, seed):
    values, traces = [], []
    for atom in control['atoms']:
        sv, sd = [], []
        for slot in atom['slots']:
            sv.append(base in slot['primary'] or any(values[j] for j in slot['prior']))
            sd.append(seed in slot['primary'] or any(traces[j] for j in slot['prior']))
        values.append(sv[0] and sv[1])
        traces.append((sv[0] and sd[1]) or (sd[0] and sv[1]))
    return any(traces[j] for j in control['final'])

def adj(a,b):
    return (a<7<=b and (a-(b-7))%7 in (0,1,3)) or (b<7<=a and (b-(a-7))%7 in (0,1,3))
reports=[]
for suffix in ['18-target','28-control','-host-control']:
    tag='sat-p14-compact-cross'+suffix
    m=json.loads((BASE/(tag+'.metadata.json')).read_text())
    old=json.loads((BASE/('sat-p14-compact-shared'+suffix+'.metadata.json')).read_text())
    nv,clauses=cnf(BASE/(tag+'.cnf'))
    oldnv,oldclauses=cnf(BASE/('sat-p14-compact-shared'+suffix+'.cnf'))
    ext=m['cross_support']
    assert ext['variable_begin']==oldnv and ext['clause_begin']==len(oldclauses)
    assert clauses[:len(oldclauses)]==oldclauses
    assert m['atoms']==old['atoms'] and m['enhancements']==old['enhancements']
    expected=[];variables=[];transfer=0
    if ext['enabled']:
        assert m['equality']
        for pair,record in zip(m['enhancements']['cooccurrence'],ext['pair_prefixes'],strict=True):
            assert record['pair']==pair['pair'] and record['terms']==pair['terms']
            terms=pair['terms'];ps=record['prefixes'];assert len(ps)==len(terms)-1
            for index,t in enumerate(terms):
                if index:expected.append([-ps[index-1],-t])
                if index+1<len(terms):
                    p=ps[index];variables.append(p)
                    if index:expected.extend([[-p,ps[index-1],t],[-ps[index-1],p],[-t,p]])
                    else:expected.extend([[-p,t],[-t,p]])
        pairs={tuple(z['pair']):z for z in m['enhancements']['cooccurrence']}
        slots=[slot for atom in m['atoms'] for slot in atom['slots']]
        for x in range(14):
            for a,b in itertools.combinations([y for y in range(14)if y!=x],2):
                if adj(a,b):continue
                pa=pairs[tuple(sorted((x,a)))];pb=pairs[tuple(sorted((x,b)))]
                for index,slot in enumerate(slots):
                    expected.append([-pa['terms'][index],-pb['out'],slot['primary'][b]])
                    transfer+=1
    assert variables==list(range(oldnv+1,nv+1))
    assert clauses[len(oldclauses):]==expected
    assert ext['clause_end']==len(clauses) and ext['transfer_count']==transfer
    record={'tag':tag,'source_variables':nv,'clauses':len(clauses),'cross_enabled':ext['enabled'],'added_variables':nv-oldnv,'added_clauses':len(expected),'transfer_clauses':transfer,'exact_shared_prefix':True}
    if not suffix.endswith('target'):
        A={int(k):bool(v)for k,v in json.loads((BASE/(tag+'.complete-assignment.json')).read_text()).items()}
        assert set(A)==set(range(1,nv+1))
        assert all(any(A[abs(v)]==(v>0)for v in clause)for clause in clauses)
        slots=[slot for atom in m['atoms']for slot in atom['slots']]
        for pair in m['enhancements']['cooccurrence']:
            a,b=pair['pair'];assert len(pair['terms'])==len(slots)
            assert all(A[t]==(A[slot['primary'][a]]and A[slot['primary'][b]])for t,slot in zip(pair['terms'],slots))
            assert A[pair['out']]==any(A[t]for t in pair['terms'])
        for pair in ext['pair_prefixes']:
            assert all(A[p]==any(A[t]for t in pair['terms'][:i+1])for i,p in enumerate(pair['prefixes']))
        control=json.loads((BASE/(tag+'.compact-control.json')).read_text());truth(control)
        assert not trace(control,0,7)and not trace(control,7,0)
        record.update(complete_assignment_pass=True,all_truth_rows=16384,raw_derivatives=[False,False],graph=control['graph'])
    reports.append(record)
checks=0
for graph in range(8):
    edges={pair for k,pair in enumerate(itertools.combinations(range(3),2))if graph>>k&1}
    for a in range(8):
        for b in range(8):
            sets=[{i for i in range(3)if mask>>i&1}for mask in[a,b]]
            intended=not(sets[0]&sets[1])and all(tuple(sorted((u,v)))in edges for u in sets[0]for v in sets[1])
            encoded=not(sets[0]&sets[1])and all(not(u in S and any(v in T for T in sets))or v in S for u,v in itertools.combinations(range(3),2)if(u,v)not in edges for S in sets)
            assert intended==encoded;checks+=1
source=BASE/'sat-p14-compact-cross.py'
print(json.dumps({'verdict':'PASS independent exact-extension/full-control audit','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'reports':reports,'unordered_orientation_cases':checks,'scope':'Only the new pair-at-most-once and cross-transfer CNF extension and exact preserved prefix. One unordered orientation is sufficient with pair-at-most-once. Controls are full clause/truth/trace checks, not solver results or a target witness.'},indent=2))
