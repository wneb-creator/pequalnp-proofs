import json
from pathlib import Path

P=Path(__file__).resolve().parent
p=l=3;n=p+l
edges={(0,0),(0,2),(1,0),(1,1),(2,1),(2,2)}
gates=[(1,3,5),(0,0,6),(1,3,4),(0,1,8),(1,4,5),(0,2,10),(1,7,9),(1,12,11)]
old_out=13
# Add a live mixed OR of all inputs, then a redundant AND with F.
all_inputs=0
for i in range(1,n):gates.append((1,all_inputs,i));all_inputs=n+len(gates)-1
gates.append((0,old_out,all_inputs));old_out=n+len(gates)-1

new=[];rename={i:i for i in range(n)}
for j,(op,a,b) in enumerate(gates):
    assert a<n+j and b<n+j
    a,b=rename[a],rename[b]
    if op:
        new.append((0,a,a));u=n+len(new)-1
        new.append((0,b,b));v=n+len(new)-1
        new.append((1,u,v))
    else:new.append((0,a,b))
    rename[n+j]=n+len(new)-1
base_size=len(new);witnesses=[]
for a in range(p):
    neighbors=sorted(b for u,b in edges if u==a);assert len(neighbors)%2==0
    for i in range(0,len(neighbors),2):
        q=neighbors[i:i+2];new.append((1,p+q[0],p+q[1]));witnesses.append((a,q,len(new)-1))
new_out=rename.get(old_out,n+len(new))
def evaluate(gs,row):
    w=[bool(row>>i&1) for i in range(n)]
    for j,(op,a,b) in enumerate(gs):
        assert a<n+j and b<n+j
        w.append((w[a] or w[b]) if op else (w[a] and w[b]))
    return w
def tcount(gs):
    reach=[{i} for i in range(n)];count=0
    for op,a,b in gs:
        reach.append(reach[a]|reach[b] if op else set())
        count+=bool(op and any(i<p for i in reach[-1]) and any(i>=p for i in reach[-1]))
    return count
target=lambda row:any(row>>a&1 and row>>(p+b)&1 for a,b in edges)
for row in range(1<<n):
    old=evaluate(gates,row);fresh=evaluate(new,row)
    assert old[old_out]==fresh[new_out]==target(row)
    assert all(old[i]==fresh[j] for i,j in rename.items())
    for a,q,j in witnesses:assert fresh[n+j]==any(row>>(p+b)&1 for b in q)
assert tcount(gates)>0 and tcount(new)==0
assert len(new)==len(gates)+2*sum(op for op,a,b in gates)+len(edges)//2
assert all(any(a==u and b in q for u,q,j in witnesses) for a,b in edges)
result={'old_gates':gates,'old_output':old_out,'new_gates':new,'new_output':new_out,'renaming':rename,'star_witnesses':witnesses,'old_size':len(gates),'old_OR_count':sum(op for op,a,b in gates),'base_transformed_size':base_size,'dead_pairs_added':len(witnesses),'new_size':len(new),'old_tCount':tcount(gates),'new_tCount':tcount(new),'truth_rows_checked':1<<n,'note':'Finite validation of the general hiding/dead-witness transfer. Not a refutation of4970.'}
(P/'hide_or_transfer.json').write_text(json.dumps(result,indent=2)+'\n')
print('Validated64 rows and every renamed wire; size',len(gates),'->',len(new),'Tcount',tcount(gates),'->',tcount(new),'dead pair ORs',len(witnesses))
