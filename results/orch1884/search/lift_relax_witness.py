import argparse,json
from pathlib import Path

P=argparse.ArgumentParser()
P.add_argument('input')
P.add_argument('output')
args=P.parse_args()
data=json.loads(Path(args.input).read_text())
g=data['gates'] if isinstance(data,dict) else data
E=[(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(4,6),(6,8),(8,5),(5,7),(7,4)]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in E)
def evaluate(gates,x):
    values=[bool(x>>j&1)for j in range(9)]
    for op,a,b in gates:
        values.append((values[a]&values[b])if op==0 else(values[a]|values[b])if op==1 else not values[a])
    return values
assert all(op in[0,1]and 0<=a<9+i and 0<=b<9+i for i,(op,a,b)in enumerate(g))
table=[evaluate(g,x)for x in range(512)]
assert all(not target(x)or table[x][-1]for x in range(512))
assert all(not(table[x][-1]and not target(x))or x in[261,276,277]for x in range(512))

def cone(i):
    todo=[i];found=set();ok=True
    while todo:
        j=todo.pop()
        if j in found:continue
        found.add(j)
        for src in g[j][1:]:
            if src in[0,4]:ok=False
            if src>=9:todo.append(src-9)
    return found if ok else None

choices=[]
for i in range(len(g)):
    ancestors=cone(i)
    if ancestors is None or not table[260][9+i]:continue
    if all(not table[x][9+i]or (x&260==260)or target(x&~17)for x in range(512)):
        choices.append((len(ancestors),i,ancestors))
out=[];mapping={};used_existing=bool(choices)
if choices:
    _,hi,ancestors=min(choices,key=lambda q:(q[0],q[1]))
    for i in sorted(ancestors):
        op,a,b=g[i];a=mapping[a-9]if a>=9 else a;b=mapping[b-9]if b>=9 else b
        out.append([op,a,b]);mapping[i]=8+len(out)
    h=mapping[hi]
else:
    hi=None;ancestors=set();out.append([0,2,8]);h=9
out.append([2,h,h]);q=8+len(out)
out.append([0,0,q]);v=8+len(out)
out.append([0,4,q]);w=8+len(out)
def remap(src):
    if src==0:return v
    if src==4:return w
    return mapping[src-9]if src>=9 else src
for i,(op,a,b)in enumerate(g):
    if i in ancestors:continue
    out.append([op,remap(a),remap(b)]);mapping[i]=8+len(out)
assert mapping[len(g)-1]==8+len(out)
bad=[x for x in range(512)if evaluate(out,x)[-1]!=target(x)]
assert not bad
result={'source_gates':len(g),'lifted_gates':len(out),'used_existing_H':used_existing,
        'existing_H_gate_index':hi,'inserted_gates':3 if used_existing else 4,
        'gates':out,'inputs':9,'output':8+len(out),'full_rows_checked':512,'bad_rows':bad,
        'scope':'Exact nine-input cofactor circuit; this alone is not a counterexample to the posted1884 statement.'}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='gates'}))
