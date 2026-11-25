import argparse
import json
from pathlib import Path
import numpy as np

EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def normalize(gs):
    n=10;m=len(gs)
    masks=np.arange(1<<m,dtype=np.uint32)
    costs=np.zeros(len(masks),dtype=np.uint16)
    for source in range(n+m):
        phase=0 if source<n else (masks>>(source-n))&1
        bad=np.zeros(len(masks),dtype=np.bool_)
        for i,(op,a,b) in enumerate(gs):
            current=(masks>>i)&1
            if a==source:bad|=(((op&1)^((op>>2)&1)^current^phase)!=0)
            if b==source:bad|=((((op>>1)&1)^((op>>2)&1)^current^phase)!=0)
        if source==n+m-1:bad|=(phase!=0)
        costs+=bad
    chosen=int(costs.argmin());best=int(costs[chosen])
    phases=[0]*n+[(chosen>>i)&1 for i in range(m)]
    result=[];stored=list(range(n));inverse={}
    def literal(source,negative):
        if not negative:return stored[source]
        if source not in inverse:
            result.append(('not',stored[source],stored[source]))
            inverse[source]=n+len(result)-1
        return inverse[source]
    for i,(op,a,b) in enumerate(gs):
        sign=phases[n+i]^((op>>2)&1)
        aa=literal(a,(op&1)^phases[a]^sign)
        bb=literal(b,((op>>1)&1)^phases[b]^sign)
        result.append(('or' if sign else 'and',aa,bb))
        stored.append(n+len(result)-1)
    output=literal(n+m-1,phases[-1])
    assert len(result)==m+best
    return result,output,best

def evaluate(gs,x):
    vals=[bool(x>>a&1) for a in range(10)]
    for op,a,b in gs:
        av=vals[a] if a<len(vals) else False
        bv=vals[b] if b<len(vals) else False
        if isinstance(op,str):
            out=(av and bv) if op=='and' else (av or bv) if op=='or' else not av
        else:
            out=((not av) if op&1 else av) and ((not bv) if op&2 else bv)
            if op&4:out=not out
        vals.append(out)
    return vals

def simplify(gs,output):
    full=(1<<1024)-1
    tables=[sum((1<<x) for x in range(1024) if x>>a&1) for a in range(10)]
    equivalent={table:a for a,table in enumerate(tables)};equivalent[0]=1000
    mapping=list(range(10));new=[]
    for op,a,b in gs:
        av=tables[a] if a<len(tables) else 0;bv=tables[b] if b<len(tables) else 0
        table=av&bv if op=='and' else av|bv if op=='or' else full^av
        tables.append(table)
        if table not in equivalent:
            aa=mapping[a] if a<len(mapping) else 1000;bb=mapping[b] if b<len(mapping) else 1000
            new.append((op,aa,bb));equivalent[table]=9+len(new)
        mapping.append(equivalent[table])
    out=mapping[output] if output<len(mapping) else 1000
    live=set()
    def visit(w):
        if w<10 or w>=10+len(new) or w in live:return
        live.add(w);op,a,b=new[w-10];visit(a)
        if op!='not':visit(b)
    visit(out)
    reduced=[];rename={a:a for a in range(10)};rename[1000]=1000
    for i,(op,a,b) in enumerate(new):
        if 10+i not in live:continue
        reduced.append((op,rename[a],rename[b] if op!='not' else rename[a]))
        rename[10+i]=9+len(reduced)
    return reduced,rename[out]

def main():
    p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('--output');args=p.parse_args()
    path=Path(args.source)
    if path.suffix=='.json':
        data=json.loads(path.read_text());gs=data['gates'] if isinstance(data,dict) else data
        gs=[(0 if op=='and' else 7 if op=='or' else op,a,b) for op,a,b in gs]
    else:
        lines=path.read_text().splitlines();start=max(i for i,l in enumerate(lines) if l.startswith('score='))
        gs=[]
        for line in lines[start+1:]:
            if not line or line.startswith(('score=','Finished')):break
            index,op,a,b=line.split();gs.append((int(op.removeprefix('type')),int(a),int(b)))
    circuit,output,negations=normalize(gs)
    circuit,output=simplify(circuit,output)
    bad=[]
    for x in range(1024):
        vals=evaluate(circuit,x)
        value=vals[output] if output<len(vals) else False
        assert value==evaluate(gs,x)[-1]
        if value!=any((x>>a&1) and (x>>b&1) for a,b in EDGES):bad.append(x)
    print('signed_gates',len(gs),'minimum_added_NOTs',negations,'ordinary_gates',len(circuit),'target_mismatches',len(bad))
    print('output',output,'gates',circuit)
    if args.output:Path(args.output).write_text(json.dumps({'gates':circuit,'output':output,'target_mismatches':bad,'minimum_added_NOTs':negations},indent=2)+'\n')

if __name__=='__main__':main()
