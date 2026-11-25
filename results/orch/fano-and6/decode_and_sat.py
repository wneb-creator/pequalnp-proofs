import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("metadata");p.add_argument("log");p.add_argument("--cnf");a=p.parse_args()
d=json.loads(Path(a.metadata).read_text());lines=Path(a.log).read_text().splitlines()
if "s SATISFIABLE" not in lines:raise SystemExit("No SAT model in log")
model={abs(int(v)):int(v)>0 for line in lines if line.startswith("v ") for v in line[2:].split() if int(v)}
if a.cnf:
 count=0
 for line in Path(a.cnf).read_text().splitlines():
  if not line or line[0] in "cp":continue
  clause=[int(x) for x in line.split() if int(x)]
  assert any(model.get(abs(v),False)==(v>0) for v in clause),(count,clause)
  count+=1
 print("CNF clauses independently satisfied:",count)
n=d["n"];k=d["k"];left=d["left"];edges=d["edges"]
ops=[[[i for i,v in enumerate(row) if model.get(v,False)] for row in gate] for gate in d["selectors"]]
outputs=[i for i,v in enumerate(d["outputs"]) if model.get(v,False)]
for j,rows in enumerate(ops):
 assert all(rows)
 assert all(i<n+j for row in rows for i in row)
 if d["t0"]:assert all(len({i>=left for i in row if i<n})<=1 for row in rows)
for mask in range(1<<n):
 values=[bool(mask>>i&1) for i in range(n)]
 for rows in ops:values.append(all(any(values[i] for i in row) for row in rows))
 out=any(values[n+i] for i in outputs)
 target=any((mask>>u&1) and (mask>>v&1) for u,v in edges)
 assert out==target,mask
print("All full truth assignments checked:",1<<n)
print("AND gates:",k,"final OR outputs:",outputs)
for j,rows in enumerate(ops):print("AND",j,rows)
# Expand free-OR normal form to a binary circuit, sharing identical prefixes.
gates=[];memo={};andwires=[]
def mkor(wires):
 wires=tuple(sorted(set(wires)))
 assert wires
 if len(wires)==1:return wires[0]
 if wires not in memo:
  u=mkor(wires[:-1]);v=wires[-1]
  memo[wires]=n+len(gates);gates.append(["or",u,v])
 return memo[wires]
for rows in ops:
 args=[mkor([i if i<n else andwires[i-n] for i in row]) for row in rows]
 andwires.append(n+len(gates));gates.append(["and",*args])
out=mkor([andwires[j] for j in outputs])
reach=[{i} for i in range(n)];pure=[{i} for i in range(n)]
for op,u,v in gates:
 reach.append(reach[u]|reach[v] if op=="or" else set())
 pure.append((pure[u]|pure[v]) if op=="or" and pure[u] is not None and pure[v] is not None else None)
tcount=sum(op=="or" and any(i<left for i in reach[n+j]) and any(i>=left for i in reach[n+j]) for j,(op,u,v) in enumerate(gates))
E={tuple(e) for e in edges};covered=[]
for u,v in edges:
 witnesses=[]
 for j,(op,_,_) in enumerate(gates):
  leaves=pure[n+j]
  if op!="or" or leaves is None or len(leaves)<2:continue
  if v in leaves and all((u,b) in E for b in leaves):witnesses.append(j)
  if u in leaves and all((b,v) in E for b in leaves):witnesses.append(j)
 covered.append(bool(witnesses))
tau=min(mask.bit_count() for mask in range(1<<n) if all((mask>>u&1) or (mask>>v&1) for u,v in edges))
result=dict(source=a.log,n=n,edges=edges,gates=gates,output=out,and_count=k,or_count=len(gates)-k,tcount=tcount,star_covered=sum(covered),edge_count=len(edges),minimum_cover=tau,size=len(gates),target_lower_bound=len(edges)+tau-1)
print(json.dumps({key:value for key,value in result.items() if key not in {"gates","edges"}},sort_keys=True))
Path(a.log+".decoded.json").write_text(json.dumps(result,indent=2)+"\n")
