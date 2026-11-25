import sys,json,itertools,hashlib,datetime,importlib.util
from pathlib import Path
base=Path(sys.argv[1])
source=base/'sat-fano-full.py'
spec=importlib.util.spec_from_file_location('review_sat_full',source)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
report=[]
def note(s): report.append(s)
def cnf_sat(cs,env):
    return all(any(env[abs(l)] if l>0 else not env[abs(l)] for l in c) for c in cs)
for op in ('eq','conj','disj'):
    for conditional in (False,True):
        c=mod.CNF(); y=c.var(); a=c.var(); b=c.var(); q=c.var()
        if op=='eq': getattr(c,op)(y,a,q if conditional else True)
        else: getattr(c,op)(y,a,b,q if conditional else True)
        for bits in itertools.product((False,True),repeat=4):
            yy,aa,bb,qq=bits
            v={'eq':aa,'conj':aa and bb,'disj':aa or bb}[op]
            expected=(not qq or yy==v) if conditional else yy==v
            assert cnf_sat(c.cs,dict(enumerate(bits,1)))==expected
note('Primitive CNF equality/AND/OR, guarded and unguarded: exhaustive truth-table PASS.')
meta=json.loads((base/'sat-fano-full28-control.metadata.json').read_text())
small=json.loads((base/'sat-fano-full27-broad.metadata.json').read_text())
control=json.loads((base/'sat-fano-canonical28-control.json').read_text())
assert all(isinstance(x,dict) for x in (meta,small,control))
n=meta['inputs']; gates=control['gates']
assert n==14 and control['output']==n+len(gates)-1 and len(gates)==28
assert meta['edge']==[0,7] and meta['bases']==[1,128]
edges=[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)]
positives=[(1<<p)|(1<<l) for p,l in edges]
def hit(m): return any(m>>p&1 and m>>l&1 for p,l in edges)
negatives=[m for m in range(1<<n) if not hit(m) and all(hit(m|(1<<i)) for i in range(n) if not m>>i&1)]
assert meta['positive']==positives and meta['negative']==negatives
assert meta['tests']==positives+negatives+[1,128]
assert small['gates']==meta['gates'][:27]
assert all(small[k]==meta[k] for k in ('inputs','original','tests','positive','negative','edge','bases'))
note('Boundary PASS: 21 minimal positives,37 maximal negatives,2 singleton bases; target/control encodings share the same first27 gates.')
assignment={}
def put(v,truth):
    assert isinstance(v,int) and not isinstance(v,bool) and 1<=v<=meta['variables']
    truth=bool(truth)
    assert v not in assignment or assignment[v]==truth
    assignment[v]=truth
vals=[[bool(m>>i&1) for m in meta['tests']] for i in range(n)]
ders=[[i==7,i==0] for i in range(n)]
for j,(op,a,b) in enumerate(gates):
    assert op in ('and','or') and 0<=a<b<n+j
    z=meta['gates'][j]; put(z['op'],op=='and')
    for i,v in enumerate(z['select_a']): put(v,i==a)
    for i,v in enumerate(z['select_b']): put(v,i==b)
    vy=[]
    for r,m in enumerate(meta['tests']):
        av,bv=vals[a][r],vals[b][r]
        yv=av and bv if op=='and' else av or bv
        put(z['selected_a'][r],av); put(z['selected_b'][r],bv); put(z['outputs'][r],yv)
        vy.append(yv)
    dy=[]
    for r,t in enumerate(z['traces']):
        k=meta['tests'].index(meta['bases'][r]); av,bv=vals[a][k],vals[b][k]
        da,db=ders[a][r],ders[b][r]
        ta,tb=av and db,da and bv; both=ta or tb
        out=both if op=='and' else da or db
        for key,val in [('selected_a',da),('selected_b',db),('term_a',ta),('term_b',tb),('both',both),('out',out)]: put(t[key],val)
        dy.append(out)
    vals.append(vy); ders.append(dy)
assert len(assignment)==meta['variables']==6944 and not any(ders[-1])
keys=[(b,a,0 if op=='and' else 1) for op,a,b in gates]
assert keys==sorted(keys) and all(any(v[:21]) for v in vals[n:])
read={a for _,a,b in gates}|{b for _,a,b in gates}
assert set(range(n))<=read and set(range(n,n+len(gates)-1))<=read
for size in (27,28):
    name='sat-fano-full28-control' if size==28 else 'sat-fano-full27-broad'
    m=meta if size==28 else small; count=0
    with (base/(name+'.cnf')).open() as f:
        assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
        for line in f:
            row=list(map(int,line.split())); assert row[-1]==0
            cs=row[:-1]; assert all(1<=abs(l)<=m['variables'] for l in cs)
            count+=1
            if size==28: assert cnf_sat([cs],assignment)
    assert count==m['clauses']
    if size==28: note(f'Known28 control assigns all6944 variables and satisfies all{count} emitted clauses.')
    else: note(f'Target27 DIMACS count/range PASS: {m["variables"]} variables,{count} clauses; no satisfiability claim.')
full=[sum(1<<m for m in range(1<<n) if m>>i&1) for i in range(n)]
target=0
for a,b in edges: target|=full[a]&full[b]
for op,a,b in gates: full.append(full[a]&full[b] if op=='and' else full[a]|full[b])
assert full[-1]==target
note('Known28 control passes all16384 Boolean inputs and both direct derivatives; topology,distinct inputs,all-used,support and canonical ordering pass.')
for p,l in edges:
    l-=7; d=(p-l)%7; a={0:1,1:4,3:2}[d]
    pp=lambda u:(a*(u-p))%7
    ll=lambda t:(a*(t-l))%7
    assert pp(p)==0 and ll(l)==0
    assert all(((u-t)%7 in (0,1,3))==((pp(u)-ll(t))%7 in (0,1,3)) for u in range(7) for t in range(7))
note('Fixed flag WLOG: explicit affine incidence automorphisms map every one of21 flags to(0,0).')
report[:0]=['Independent full-Fano SAT encoding review PASS',datetime.datetime.now(datetime.UTC).isoformat()]
note('Source SHA256 '+hashlib.sha256(source.read_bytes()).hexdigest())
text='\n'.join(report)+'\n'
(base/'status-full-fano-sat-review.txt').write_text(text)
print(text,end='')
