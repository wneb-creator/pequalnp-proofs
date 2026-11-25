import itertools, json, pathlib, sys
for name in sys.argv[1:]:
    base=pathlib.Path(name)
    d=json.loads(base.with_suffix('.map.json').read_text())
    lines=base.with_suffix('.stdout').read_text().splitlines()
    model={abs(int(x)):int(x)>0 for line in lines if line.startswith('v ')
           for x in line[2:].split() if int(x)}
    assert model, name
    clauses=0
    for line in base.with_suffix('.cnf').read_text().splitlines():
        if line.startswith(('c','p')): continue
        xs=list(map(int,line.split()))[:-1]
        assert any(model[abs(x)]==(x>0) for x in xs),(name,xs)
        clauses+=1
    n=d['n']; k=d['k']; inp=2*n
    edges=[(i,j) for i in range(n) for j in range(n) if model[d['edge'][i][j]]]
    assert all((i,i) in edges for i in range(n))
    assert all(not all((u,v) in edges for u in [i,ii] for v in [j,jj])
               for i,ii in itertools.combinations(range(n),2)
               for j,jj in itertools.combinations(range(n),2))
    sels=[[[h for h,x in enumerate(d['sel'][g][b]) if model[x]] for b in range(2)] for g in range(k)]
    outs=[g for g,x in enumerate(d['outs']) if model[x]]
    for mask in range(1<<inp):
        vals=[bool(mask>>h&1) for h in range(inp)]
        for left,right in sels:
            vals.append(any(vals[h] for h in left) and any(vals[h] for h in right))
        got=any(vals[inp+g] for g in outs)
        if d.get('dual',False):
            expected=all((mask>>i&1) or (mask>>(n+j)&1) for i,j in edges)
        else:
            expected=any((mask>>i&1) and (mask>>(n+j)&1) for i,j in edges)
        assert got==bool(expected),(name,mask,got,expected)
    report=dict(name=name,variables=len(model),clauses_checked=clauses,assignments_checked=1<<inp,
                edges=edges,selectors=sels,output=outs,dual=d.get('dual',False))
    base.with_suffix('.verified.json').write_text(json.dumps(report,indent=2))
    print(name,'PASS',len(edges),'edges',k,'counted ANDs',clauses,'clauses')
