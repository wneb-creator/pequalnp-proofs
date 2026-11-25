import json
from pathlib import Path

P=Path(__file__).resolve().parent
n=6
p=l=3
edges={(0,3),(0,5),(1,3),(1,4),(2,4),(2,5)}
gates=[(1,3,5),(0,0,6),(1,3,4),(0,1,8),(1,4,5),(0,2,10),(1,7,9),(1,12,11)]
output=13
for q in (6,8,10):
    gates.append((1,output,q));h=n+len(gates)-1
    gates.append((0,output,h));output=n+len(gates)-1
def ev(gs,out,row):
    w=[bool(row>>i&1) for i in range(n)]
    for op,a,b in gs:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
    return False if out is None else w[out]
def tau(es):return min(r.bit_count() for r in range(1<<n) if all((r>>a&1) or (r>>b&1) for a,b in es))
def star_data(gs,es):
    adj=[0]*n
    for a,b in es:adj[a]|=1<<b;adj[b]|=1<<a
    sup=[1<<i for i in range(n)];reach=sup[:];data=[];mixed=0
    for j,(op,a,b) in enumerate(gs):
        q=(sup[a]|sup[b]) if op else (sup[a]&sup[b]);sup.append(q);reach.append((reach[a]|reach[b]) if op else 0)
        mixed+=bool(op and reach[-1]&7 and reach[-1]&56)
        centers=[v for v in range(n) if q.bit_count()>=2 and q&~adj[v]==0] if op else []
        if centers and not ev(gs,n+j,63^q):
            assert len(centers)==1;v=centers[0];served={e for e in es if (e[0]==v and q>>e[1]&1) or (e[1]==v and q>>e[0]&1)};data.append((j,served))
    return data,mixed
def folded(v):
    mapping={i:(None if i==v else i) for i in range(n)};gs=[]
    for j,(op,a,b) in enumerate(gates):
        a,b=mapping[a],mapping[b]
        if not op and (a is None or b is None):w=None
        elif op and a is None:w=b
        elif op and b is None:w=a
        elif a==b:w=a
        else:gs.append((op,a,b));w=n+len(gs)-1
        mapping[n+j]=w
    return gs,mapping[output]
def cone(gs,out):
    todo=[] if out is None else [out];keep=set()
    while todo:
        w=todo.pop()
        if w<n or w-n in keep:continue
        j=w-n;keep.add(j);todo.extend(gs[j][1:])
    return keep
original_stars,mixed=star_data(gates,edges)
assert mixed==0 and set().union(*(e for j,e in original_stars))==edges
assert all(ev(gates,output,r)==any((r>>a&1) and (r>>b&1) for a,b in edges) for r in range(64))
results=[]
for v in range(n):
    es={e for e in edges if v not in e};gs,out=folded(v);keep=cone(gs,out);stars,mt=star_data(gs,es)
    allroots=set(keep)
    for j,e in stars:allroots|=cone(gs,n+j)
    served=set().union(*(e for j,e in stars if j in allroots)) if stars else set()
    saving=len(gates)-len(keep);saving_all=len(gates)-len(allroots);deg=sum(v in e for e in edges);drop=tau(edges)-tau(es);required=deg+drop
    assert all(ev(gs,out,r)==any((r>>a&1) and (r>>b&1) for a,b in es) for r in range(64))
    results.append({'vertex':v,'degree':deg,'tau_drop':drop,'saving_output_only':saving,'saving_preserve_stars':saving_all,'required_degree_step':required,'surviving_served_edges':len(served),'required_W_step':len(edges)-len(served)+drop,'folded_gates':gs,'folded_output':out,'kept_output_gate_indices':sorted(keep)})
assert all(r['saving_output_only']<r['required_degree_step'] for r in results)
assert all(r['saving_preserve_stars']<r['required_W_step'] for r in results)
result={'n':n,'p':p,'edges':sorted(edges),'gates':gates,'output':output,'size':len(gates),'tCount':mixed,'truth_rows_checked':64,'star_hypothesis':True,'restrictions':results,'scope':'Counterexample to literal constant folding/idempotence/dead-pruning existential elimination, not to4970. Absorption identities remove the masks and may restore a viable strategy.'}
(P/'restriction_obstruction.json').write_text(json.dumps(result,indent=2)+'\n')
print('Valid4970 C6 circuit with14 gates,T0; all six vertices fail the proposed literal elimination inequalities.')
for r in results:print(r['vertex'],'save',r['saving_output_only'],'required',r['required_degree_step'],'W-save',r['saving_preserve_stars'],'W-required',r['required_W_step'])
