import sys,json,itertools,collections,hashlib,datetime
from pathlib import Path
base=Path(sys.argv[1])
reports=[]
def ev(gs,m):
    v=[bool(m>>i&1) for i in range(14)]
    for op,a,b in gs:v.append((v[a] and v[b]) if op=='and' else (v[a] or v[b]))
    return v
for a,b,op,q in itertools.product([False,True],repeat=4):
    cs=[(not q,op),(not q,a,b),(not op,not a,q),(not op,not b,q)]
    assert all(any(c) for c in cs)==(q==(op and (a or b)))
def canon_clause(ls):
    if any(v is True for v in ls):return None
    vs=set(v for v in ls if v is not False)
    if any(-v in vs for v in vs):return None
    return tuple(sorted(vs))
def neg(v):return not v if type(v)==bool else -v
for tag,control,full in [('sat-fano-p14-35control','sat-p14-canonical35-control.json',True),('sat-fano-p14-27','sat-p14-matching27-structural-control.json',False)]:
    meta=json.loads((base/(tag+'.metadata.json')).read_text());ctrl=json.loads((base/control).read_text())
    assert isinstance(meta,dict) and isinstance(ctrl,dict)
    gs=ctrl['gates'];N=len(gs);tests=meta['tests'];assert meta['inputs']==14 and meta['original']==list(range(14))
    assert len(tests)==72 and set(tests)==set(meta['positive']+meta['negative']+[1<<i for i in range(14)])
    assert len(meta['positive'])==21 and len(meta['negative'])==37 and len(meta['gates'])==N
    for j,(op,a,b) in enumerate(gs):assert op in ['and','or'] and 0<=a<b<14+j
    tables={m:ev(gs,m) for m in tests}
    for m in range(1<<14):
        expected=any(m>>p&1 and m>>(7+l)&1 for p in range(7) for l in range(7) if ((p-l)%7 in (0,1,3)) if full) if full else any(m>>p&1 and m>>(7+p)&1 for p in range(7))
        assert ev(gs,m)[-1]==expected
    A={}
    def put(v,b):
        assert type(v)==int and v not in A and 1<=v<=meta['variables'];A[v]=bool(b)
    for j,(op,a,b) in enumerate(gs):
        g=meta['gates'][j];put(g['op'],op=='and')
        assert len(g['select_a'])==len(g['select_b'])==14+j
        for w,z in enumerate(g['select_a']):put(z,w==a)
        for w,z in enumerate(g['select_b']):put(z,w==b)
        for r,m in enumerate(tests):
            put(g['selected_a'][r],tables[m][a]);put(g['selected_b'][r],tables[m][b]);put(g['outputs'][r],tables[m][14+j])
    for direction,mask in enumerate(meta['bases']):
        seed=meta['edge'][1-direction];d=[i==seed for i in range(14)];v=tables[mask]
        for j,(op,a,b) in enumerate(gs):
            t=meta['gates'][j]['traces'][direction];left=v[a] and d[b];right=d[a] and v[b];z=(left or right) if op=='and' else (d[a] or d[b])
            for k,bv in [('selected_a',d[a]),('selected_b',d[b]),('term_a',left),('term_b',right),('both',left or right),('out',z)]:put(t[k],bv)
            d.append(z)
    for d in meta['boundary_essential']:
        g=meta['gates'][d['gate']];r=d['row'];a=A[g['selected_a'][r]];b=A[g['selected_b'][r]]
        put(d['a_not_b'],a and not b);put(d['b_not_a'],b and not a)
    extra=collections.Counter();eligibility=collections.Counter()
    def add(dst,*ls):
        c=canon_clause(ls)
        if c is not None:dst[c]+=1
    def literal(v):return v if type(v)==bool else A[abs(v)] if v>0 else not A[-v]
    def dp(dp,dst=None):
        lits=dp['literals'];k=dp['threshold'];cells=dp['cells'];keys={(c['prefix'],c['threshold']):c['var'] for c in cells}
        if k<=0:assert dp['root'] is True and not cells;return
        if k>len(lits):assert dp['root'] is False and not cells;return
        assert len(keys)==len(cells) and set(keys)=={(i,j) for i in range(1,len(lits)+1) for j in range(1,min(i,k)+1)}
        def cell(i,j):return True if j==0 else keys.get((i,j),False)
        for (i,j),z in keys.items():
            put(z,sum(literal(v) for v in lits[:i])>=j)
            if dst is not None:
                a,b,x=cell(i-1,j),cell(i-1,j-1),lits[i-1]
                add(dst,neg(a),z);add(dst,neg(b),neg(x),z);add(dst,-z,a,b);add(dst,-z,a,x)
        assert dp['root']==cell(len(lits),k)
    for r in meta['false_or_count']:
        for j,z in enumerate(r['gate_literals']):put(z,gs[j][0]=='or' and not tables[tests[r['row']]][14+j])
        dp(r['dp'])
    assert len(meta['p14_branches'])==14+N-1
    for w,r in enumerate(meta['p14_branches']):
        assert r['wire']==w
        uses=[g[k][w] for g in meta['gates'] for k in ['select_a','select_b'] if w<len(g[k])]
        assert r['uses']==uses==r['dp']['literals'] and r['dp']['threshold']==2
        dp(r['dp'],eligibility)
        count=sum(w in [a,b] for _,a,b in gs)
        assert literal(r['dp']['root'])==(count>=2)
    assert len(meta['p14_eligible'])==14
    for x,r in enumerate(meta['p14_eligible']):
        assert r['label']==x and tests[r['row']]==1<<x and len(r['options'])==14+N-1
        for w,z in enumerate(r['options']):
            branch=meta['p14_branches'][w]['dp']['root'];value=(bool(x==w) if w<14 else meta['gates'][w-14]['outputs'][r['row']])
            put(z,literal(branch) and tables[1<<x][w]);add(eligibility,neg(branch),neg(value),z);add(eligibility,branch,-z);add(eligibility,value,-z)
        add(eligibility,*r['options']);assert any(A[z] for z in r['options'])
    assert len(meta['p14_equality'])==(0 if full else 14)
    for x,r in enumerate(meta['p14_equality']):
        assert r['label']==x and tests[r['row']]==1<<x and len(r['exits'])==N
        for j,z in enumerate(r['exits']):
            g=meta['gates'][j];a,b,op=g['selected_a'][r['row']],g['selected_b'][r['row']],g['op']
            put(z,A[op] and (A[a] or A[b]));assert not(A[a] and A[b])
            add(extra,-a,-b);add(extra,-z,op);add(extra,-z,a,b);add(extra,-op,-a,z);add(extra,-op,-b,z)
        assert r['dp']['literals']==r['exits'] and r['dp']['threshold']==3
        dp(r['dp'],extra)
        root2=next(c['var'] for c in r['dp']['cells'] if c['prefix']==N and c['threshold']==2)
        assert root2==r['at_least_two'];add(extra,root2);add(extra,-r['dp']['root']);assert sum(A[z] for z in r['exits'])==2
    assert set(A)==set(range(1,meta['variables']+1))
    lo,hi=meta['p14_clause_range'];allcs=collections.Counter();eqcs=collections.Counter();checked=0
    with (base/(tag+'.cnf')).open() as f:
        assert f.readline().split()==['p','cnf',str(meta['variables']),str(meta['clauses'])]
        for i,line in enumerate(f):
            ls=list(map(int,line.split()));assert ls[-1]==0 and all(1<=abs(z)<=meta['variables'] for z in ls[:-1]);c=tuple(sorted(ls[:-1]));allcs[c]+=1
            if lo<=i<hi:eqcs[c]+=1
            if full or lo<=i<hi:assert any(literal(z) for z in ls[:-1]);checked+=1
    assert sum(allcs.values())==meta['clauses'] and eqcs==extra and not(eligibility-allcs)
    reports.append(dict(tag=tag,variables=meta['variables'],clauses_checked=checked,eligibility_clauses_verified=sum(eligibility.values()),equality_clauses_verified=sum(extra.values()),full_boolean_assignments=16384,scope='exact Fano35 and complete CNF' if full else 'exact matching27, only structural and eligibility clauses; not Fano'))
print(json.dumps({'verdict':'PASS','utc':datetime.datetime.now(datetime.UTC).isoformat(),'source_sha256':hashlib.sha256((base/'sat-fano-p14.py').read_bytes()).hexdigest(),'controls':reports,'target_verdict':'none; no solver launched'}))
