import sys,json,hashlib,collections,datetime
from pathlib import Path

base=Path(sys.argv[1])
# Reuse the frozen baseline audit through construction of its complete
# assignment. This prefix performs no writes and starts no solver.
review=(base/'status-full-fano-sat-review.py').read_text()
marker='for size in (27,28):'
assert review.count(marker)==1
exec(compile(review[:review.index(marker)],'status-full-fano-sat-review.py','exec'))

essential=json.loads((base/'sat-fano-essential28-control.metadata.json').read_text())
minimal=json.loads((base/'sat-fano-minimal28-control.metadata.json').read_text())
assert isinstance(essential,dict) and isinstance(minimal,dict)
assert essential['gates']==meta['gates'] and essential['tests']==meta['tests']
assert {k:v for k,v in minimal.items() if k!='clauses'}=={k:v for k,v in essential.items() if k!='clauses'}
assert minimal['clauses']==essential['clauses']+28
added=essential['boundary_essential']
assert isinstance(added,list) and len(added)==28*58
for d in added:
    assert isinstance(d,dict)
    j,r=d['gate'],d['row']
    assert 0<=j<28 and 0<=r<58
    av=assignment[essential['gates'][j]['selected_a'][r]]
    bv=assignment[essential['gates'][j]['selected_b'][r]]
    for key,val in [('a_not_b',av and not bv),('b_not_a',bv and not av)]:
        v=d[key]
        assert v not in assignment and 6945<=v<=essential['variables']
        assignment[v]=val
assert len(assignment)==essential['variables']==minimal['variables']==10192
for j,(op,a,b) in enumerate(gates):
    rows=range(21,58) if op=='and' else range(21)
    assert any(vals[a][r] and not vals[b][r] for r in rows)
    assert any(vals[b][r] and not vals[a][r] for r in rows)

def read_cnf(name,m):
    with (base/name).open() as f:
        assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
        counts=collections.Counter(f)
    assert sum(counts.values())==m['clauses']
    for line in counts:
        row=list(map(int,line.split()))
        assert row[-1]==0 and all(1<=abs(l)<=m['variables'] for l in row[:-1])
        assert cnf_sat([row[:-1]],assignment)
    return counts

oldrows=read_cnf('sat-fano-essential28-control.cnf',essential)
newrows=read_cnf('sat-fano-minimal28-control.cnf',minimal)
assert not oldrows-newrows
expected=collections.Counter(' '.join(str(-g['outputs'][r]) for r in range(21,58))+' 0\n' for g in minimal['gates'])
assert newrows-oldrows==expected and sum(expected.values())==28
text='\n'.join([
    'Independent final Fano SAT control review PASS',
    datetime.datetime.now(datetime.UTC).isoformat(),
    'Complete10192-variable assignment satisfies all218698 essential and218726 minimal control clauses.',
    'Exact difference:28 expected maximal-negative false-output clauses, no other changes.',
    'Both operand polarities hold on the appropriate positive/negative boundary for every control gate.',
    'No solver run; no target27 satisfiability claim.',
    'Minimal source SHA256 '+hashlib.sha256((base/'sat-fano-minimal.py').read_bytes()).hexdigest(),
])+'\n'
print(text,end='')
