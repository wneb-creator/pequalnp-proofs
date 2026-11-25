import argparse,itertools,json
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--graph',choices=['c5','petersen-minus2'],default='petersen-minus2')
p.add_argument('--gates',type=int,required=True)
p.add_argument('--out',required=True)
p.add_argument('--decode')
a=p.parse_args();k=a.gates
if a.graph=='c5':n=5;edges=[(i,(i+1)%5) for i in range(5)]
else:
    pairs=list(itertools.combinations(range(5),2));keep=[i for i in range(10) if i not in (0,7)]
    rename={old:new for new,old in enumerate(keep)};n=8
    edges=[(rename[i],rename[j]) for i in keep for j in keep if i<j and not set(pairs[i])&set(pairs[j])]
ind=[x for x in range(1<<n) if not any((x>>u)&1 and (x>>v)&1 for u,v in edges)]
maxind=[x for x in ind if all((x|(1<<v)) not in ind for v in range(n) if not ((x>>v)&1))]
samples=[((1<<u)|(1<<v),True) for u,v in edges]+[(x,False) for x in maxind]
V={};clauses=[]
def var(key):
    if key not in V:V[key]=len(V)+1
    return V[key]
def clause(*xs):clauses.append(tuple(xs))
for t in range(k):
    op=var(('and',t));count=n+t+1
    for side in (0,1):
        sels=[var(('sel',t,side,j)) for j in range(count)]
        clause(*sels)
        for u,v in itertools.combinations(sels,2):clause(-u,-v)
        for z,(x,_) in enumerate(samples):
            value=var(('input',t,side,z))
            for j,s in enumerate(sels):
                if j==n+t:clause(-s,-value)
                elif j<n:clause(-s,value if ((x>>j)&1) else -value)
                else:
                    src=var(('value',j-n,z));clause(-s,-value,src);clause(-s,value,-src)
    for u in range(count):
        for v in range(u):clause(-var(('sel',t,0,u)),-var(('sel',t,1,v)))
    for z,_ in enumerate(samples):
        left=var(('input',t,0,z));right=var(('input',t,1,z));out=var(('value',t,z))
        clause(-op,-out,left);clause(-op,-out,right);clause(-op,out,-left,-right)
        clause(op,-left,out);clause(op,-right,out);clause(op,left,right,-out)
for t in range(k-1):
    clause(*(var(('sel',j,side,n+t)) for j in range(t+1,k) for side in (0,1)))
for z,(_,target) in enumerate(samples):clause(var(('value',k-1,z)) if target else -var(('value',k-1,z)))
meta={'graph':a.graph,'n':n,'edges':edges,'gates':k,'samples':samples,'variables':len(V),'clauses':len(clauses),'constants':'false only','all_gates_reach_output':True}
if a.decode:
    model={}
    for line in Path(a.decode).read_text().splitlines():
        if line.startswith('v '):
            for token in line.split()[1:]:
                v=int(token)
                if v:model[abs(v)]=v>0
    assert all(any(model.get(abs(v),False)==(v>0) for v in c) for c in clauses)
    circuit=[]
    for t in range(k):
        operands=[]
        for side in (0,1):
            selected=[j for j in range(n+t+1) if model[var(('sel',t,side,j))]]
            assert len(selected)==1
            j=selected[0];operands.append(-1 if j==n+t else j)
        circuit.append(('and' if model[var(('and',t))] else 'or',*operands))
    for x in range(1<<n):
        values=[bool((x>>i)&1) for i in range(n)]
        for op,u,v in circuit:
            left=False if u<0 else values[u];right=False if v<0 else values[v]
            values.append(left and right if op=='and' else left or right)
        assert values[-1]==any((x>>u)&1 and (x>>v)&1 for u,v in edges)
    meta['circuit']=circuit;meta['validation']='every clause and every Boolean input checked'
    Path(a.out+'.witness.json').write_text(json.dumps(meta,indent=2)+'\n')
else:
    Path(a.out+'.cnf').write_text('p cnf '+str(len(V))+' '+str(len(clauses))+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    Path(a.out+'.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta))
