from pathlib import Path
import json, time
started=time.time()
n=10
universe=(1<<(1<<n))-1
xs=[sum(1<<u for u in range(1<<n) if u>>i&1) for i in range(n)]
edges=[xs[2*i]&xs[2*i+1] for i in range(5)]
F=0
for e in edges:F|=e
v=xs[:];gates=[]
def add(op,a,b):
    gates.append((op,a,b));v.append(v[a]&v[b] if op=="and" else v[a]|v[b]);return len(v)-1
e=[None]+[add("and",2*i,2*i+1) for i in range(1,5)]
a0=add("or",0,e[1]);a=add("or",a0,e[3])
b0=add("or",0,e[2]);b=add("or",b0,e[4])
t10=add("or",1,e[1]);t1=add("or",t10,e[2])
t20=add("or",1,e[3]);t2=add("or",t20,e[4])
prefix=v[:]
u=add("or",a,b)
c1=add("and",u,t1);c2=add("and",u,t2);out=add("or",c1,c2)
assert v[out]==F
edge_inputs=[(1<<(2*i))|(1<<(2*i+1)) for i in range(5)]
def profile(f):return sum(1<<i for i,p in enumerate(edge_inputs) if f>>p&1)
def calc(fs):
    closure={universe}
    for f in fs:closure|={f&g for g in closure}
    cleanprofiles=sorted({profile(f) for f in closure if not(f&~F)})
    dp=[100]*32;dp[0]=0
    for mask in range(32):
        for cp in cleanprofiles:dp[mask|cp]=min(dp[mask|cp],dp[mask]+1)
    return {'closure_size':len(closure),'clean_edge_profiles':cleanprofiles,'tau':dp[31]}
old=calc(prefix);new=calc(prefix+[v[u]])
assert old['tau']==4 and new['tau']==2
active=[profile(v[n+j]) for j in range(len(gates))]
assert all(active)
essential=[]
for clamp in range(len(gates)):
    w=xs[:]
    for j,(op,a,b) in enumerate(gates):w.append(0 if j==clamp else w[a]&w[b] if op=="and" else w[a]|w[b])
    essential.append(profile(F & ~w[out]))
assert all(essential)
traces=[]
for i in range(5):
    row=[]
    for base,target in [(2*i,2*i+1),(2*i+1,2*i)]:
        vals=[bool((1<<base)>>j&1) for j in range(n)];d=[j==target for j in range(n)]
        for op,a,b in gates:
            d.append((vals[a] and d[b]) or(d[a] and vals[b]) if op=="and" else d[a] or d[b])
            vals.append(vals[a] and vals[b] if op=="and" else vals[a] or vals[b])
        row.append(d[out])
    traces.append(row)
record={'target':'5-edge matching on10 inputs','gates':gates,'output':out,'prefix_gate_count':len(prefix)-n,'before':old,'after_one_OR':new,'all1024_function_rows_verified':True,'gate_edge_profiles':active,'clamping_loses_edge_profiles':essential,'marked_derivative_pairs':traces,'elapsed_seconds':time.time()-started}
p=Path('/workspace/pequalnp-proofs/results/orch/tau-drop-counterexample.json');p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
