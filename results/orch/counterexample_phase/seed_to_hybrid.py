import argparse, importlib.util, json
from pathlib import Path
SOURCE=Path('/tmp/oec/pequalnp-pilot-85/counterexample/compact_hybrid.py')
spec=importlib.util.spec_from_file_location('hybrid',SOURCE)
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)

def flatten(data):
    gates=data['gates'];N=14
    nots=[i for i,g in enumerate(gates) if g[0]==2]
    assert len(nots)==1
    ni=nots[0];source=gates[ni][1];neg_wire=N+ni
    assert 0<=source<N+ni
    primitive={i:i for i in range(N)}
    kinds=[];nodes=[];inserted=False
    def expand(w):
        if w<0:return set()
        if w in primitive:return {primitive[w]}
        op,a,b=gates[w-N]
        assert op==1,(w,op)
        return expand(a)|expand(b)
    def insert():
        nonlocal inserted
        ss=sorted(expand(source));assert ss
        positive=N+len(nodes)
        kinds.append('or');nodes.append([ss])
        kinds.append('flip');nodes.append([])
        primitive[source]=positive
        primitive[neg_wire]=positive+1
        inserted=True
    if source<N:insert()
    for i,(op,a,b) in enumerate(gates):
        wire=N+i
        if op==0:
            aa,bb=sorted(expand(a)),sorted(expand(b));assert aa and bb
            primitive[wire]=N+len(nodes)
            kinds.append('and');nodes.append([aa,bb])
        elif op==2:
            assert i==ni and inserted
        else:assert op==1
        if wire==source:insert()
    assert inserted
    output=sorted(v-N for v in expand(data.get('output',N+len(gates)-1)))
    assert all(i>=0 for i in output)
    swaps=0
    while True:
        j=next((j for j in range(len(nodes)-1)
                if kinds[j]==kinds[j+1]=='and'
                and max(sum(nodes[j],[]))>max(sum(nodes[j+1],[]))),None)
        if j is None:break
        assert N+j not in sum(nodes[j+1],[])
        nodes[j],nodes[j+1]=nodes[j+1],nodes[j]
        for node in nodes[j+2:]:
            for ss in node:
                for t,w in enumerate(ss):
                    if w==N+j:ss[t]=N+j+1
                    elif w==N+j+1:ss[t]=N+j
                ss.sort()
        output=[j+1 if t==j else j if t==j+1 else t for t in output]
        swaps+=1;assert swaps<100000
    for j,(kind,node) in enumerate(zip(kinds,nodes)):
        if kind=='and':
            aa,bb=node
            if tuple(i in aa for i in range(N+j))>tuple(i in bb for i in range(N+j)):
                node.reverse()
    k=kinds.count('and');p=kinds.index('or')
    root=h.root_circuit(kinds,nodes,output)
    selected=sum(len(ss) for node in nodes for ss in node)+len(output)
    assert root['size']==selected-k-1
    assert not h.validate(root)
    return {'ands':k,'position':p,'kinds':kinds,'nodes':nodes,'output':output,
            'selected':selected,'root_circuit':root,'ordering_swaps':swaps}

def main():
    p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('destination');a=p.parse_args()
    result=flatten(json.loads(Path(a.source).read_text()))
    Path(a.destination).write_text(json.dumps(result,indent=2))
    print('ANDs',result['ands'],'position',result['position'],'selectors',result['selected'],
          'actual gates',result['root_circuit']['size'],'ordering swaps',result['ordering_swaps'])
if __name__=='__main__':main()
