import sys,json,collections,hashlib,datetime,itertools
from pathlib import Path
base=Path(sys.argv[1])
exec(compile((base/'status-final-fano-sat-review.py').read_text(),'status-final-fano-sat-review.py','exec'))
extended=json.loads((base/'sat-fano-orcount28-control.metadata.json').read_text())
assert isinstance(extended,dict)
assert {k:v for k,v in extended.items() if k not in ['variables','clauses','false_or_count']} == {k:v for k,v in minimal.items() if k not in ['variables','clauses']}
records=extended['false_or_count']
assert len(records)==37
assert [d['mask'] for d in records]==extended['negative']
expected=collections.Counter()
def add(*ls):
    if any(x is True for x in ls):return
    vals=set(x for x in ls if x is not False)
    if any(-x in vals for x in vals):return
    expected[tuple(sorted(vals))]+=1
def neg(x):return not x if isinstance(x,bool) else -x
for a,b,x,z in itertools.product([False,True],repeat=4):
    clauses=[(not a,z),(not b,not x,z),(not z,a,b),(not z,a,x)]
    assert all(any(c) for c in clauses)==(z==(a or (b and x)))
for d in records:
    r,mask,k=d['row'],d['mask'],d['required']
    assert extended['tests'][r]==mask and not any(mask>>a&1 and mask>>b&1 for a,b in edges)
    absent=[i for i in range(14) if not(mask>>i&1)]
    assert k==len(absent)-1
    for i in absent:
        m=mask|(1<<i)
        assert any(m>>a&1 and m>>b&1 for a,b in edges)
    lits=d['gate_literals'];dp=d['dp']
    assert len(lits)==28 and dp['literals']==lits and dp['threshold']==k
    for j,q in enumerate(lits):
        g=extended['gates'][j];op=g['op'];value=g['outputs'][r]
        assert q not in assignment
        assignment[q]=not assignment[op] and not assignment[value]
        add(op,value,q);add(-op,-q);add(-value,-q)
    assert sum(assignment[q] for q in lits)>=k
    cells={(c['prefix'],c['threshold']):c['var'] for c in dp['cells']}
    assert len(cells)==len(dp['cells'])
    assert set(cells)=={(i,j) for i in range(1,29) for j in range(1,min(i,k)+1)}
    def cell(i,j):
        if j==0:return True
        return cells.get((i,j),False)
    for (i,j),z in cells.items():
        assert z not in assignment
        assignment[z]=sum(assignment[q] for q in lits[:i])>=j
        a,b,x=cell(i-1,j),cell(i-1,j-1),lits[i-1]
        add(neg(a),z);add(neg(b),neg(x),z);add(-z,a,b);add(-z,a,x)
    assert dp['root']==cell(28,k)
    add(dp['root'])
assert set(assignment)==set(range(1,extended['variables']+1))
def parsed(name,m):
    with (base/name).open() as f:
        assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
        rows=[]
        for line in f:
            lits=list(map(int,line.split()));assert lits[-1]==0
            rows.append(tuple(sorted(lits[:-1])))
    assert len(rows)==m['clauses']
    for row in rows:assert cnf_sat([row],assignment)
    return collections.Counter(rows)
before=parsed('sat-fano-minimal28-control.cnf',minimal)
after=parsed('sat-fano-orcount28-control.cnf',extended)
assert not before-after and after-before==expected
print(json.dumps({'verdict':'PASS','utc':datetime.datetime.now(datetime.UTC).isoformat(),'variables':extended['variables'],'clauses':extended['clauses'],'new_clauses':sum(expected.values()),'negative_rows':len(records),'critical_input_threshold_histogram':dict(collections.Counter(d['required'] for d in records)),'source_sha256':hashlib.sha256((base/'sat-fano-orcount.py').read_bytes()).hexdigest(),'scope':'Exact extension and complete canonical28 assignment verified. Each absent input is critical on its maximal-negative row; OR bound follows reviewed false_or_count. No solver or target27 verdict.'}))
