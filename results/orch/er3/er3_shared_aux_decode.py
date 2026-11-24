import itertools,json,sys
from pathlib import Path
meta=json.loads(Path(sys.argv[1]).read_text());positive=set()
for line in Path(sys.argv[2]).read_text().splitlines():
    if line.startswith('v '):positive.update(int(x) for x in line[2:].split() if int(x)>0)
if not positive:print('no model');sys.exit(0)
n=meta['n'];gates=[]
def add(op,a,b):gates.append([op,a,b]);return n+len(gates)-1
def pick(vs):
    xs=[i for i,v in enumerate(vs) if v in positive];assert len(xs)==1;return xs[0]
def decode(block,rename):
    for ls,rs,op in block:rename.append(add('or' if op in positive else 'and',rename[pick(ls)],rename[pick(rs)]))
    return rename
shared=decode(meta['shared'],meta['A'].copy())[4:]
pieces=[];aux_wire=None
for block in meta['locals']:
    wires=decode(block['gates'],block['vertices']+shared)
    base=7+len(shared)
    pieces.append(wires[-1] if block['main_sel'] is None else wires[base+pick(block['main_sel'])])
    if block['aux_sel'] is not None:aux_wire=wires[base+pick(block['aux_sel'])]
B=meta['B'];u=add('and',B[0],B[1]);v=add('or',B[0],B[1]);w=add('and',B[2],v)
pieces.append(add('or',u,w));output=pieces[0]
for p in pieces[1:]:output=add('or',output,p)
assert len(gates)==meta['budget']
def verify(n,edges,gates,output,aux=None):
    hood=[0]*n
    for i,j in edges:assert i!=j;hood[i]|=1<<j;hood[j]|=1<<i
    assert all((hood[i]&hood[j]).bit_count()<2 for i,j in itertools.combinations(range(n),2))
    mi=0
    for row in range(1<<n):
        ws=[bool(row>>i&1) for i in range(n)];want=any(ws[i] and ws[j] for i,j in edges)
        if not want:mi=max(mi,row.bit_count())
        for op,a,b in gates:ws.append((ws[a] or ws[b]) if op=='or' else (ws[a] and ws[b]))
        assert ws[output]==want,('bad graph row',n,row)
        if aux is not None:
            z,(a,c)=aux;assert ws[z]==(ws[a] or ws[c]),('bad auxiliary row',row)
    tau=n-mi;bound=len(edges)+tau-1
    return {'n':n,'edges':edges,'gates':gates,'output':output,'tau':tau,'bound':bound,
            'full_truth_rows':1<<n,'is_counterexample':len(gates)<bound}
original=verify(n,meta['edges'],gates,output,(aux_wire,meta['aux_pair']))
original['aux_wire']=aux_wire;original['aux_pair']=meta['aux_pair']
shift=lambda w:w if w<n else w+2
extended=[[op,shift(a),shift(b)] for op,a,b in gates]
z,leaf=n,n+1
extended.append(['or',shift(aux_wire),leaf]);s=n+2+len(extended)-1
extended.append(['and',z,s]);t=n+2+len(extended)-1
extended.append(['or',shift(output),t]);out=n+2+len(extended)-1
a,c=meta['aux_pair'];edges=meta['edges']+[[z,a],[z,c],[z,leaf]]
result=verify(n+2,edges,extended,out)
path=Path(sys.argv[3]);path.write_text(json.dumps(result,indent=2))
path.with_name(path.stem+'-original.json').write_text(json.dumps(original,indent=2))
print(json.dumps({'original_gates':len(gates),'aux_pair':meta['aux_pair'],
    'extended_n':n+2,'extended_edges':len(edges),'extended_gates':len(extended),
    'tau':result['tau'],'bound':result['bound'],'full_truth_rows':result['full_truth_rows'],
    'is_counterexample':result['is_counterexample']}),flush=True)
