from pathlib import Path
import sys,json
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-71/core-counterexample')
from evaluator import Model
stem=Path(sys.argv[1]);meta=json.loads(stem.with_suffix('.meta.json').read_text());sol=stem.with_suffix('.sol').read_text();assert 's SATISFIABLE' in sol
true=set()
for line in sol.splitlines():
 if line.startswith('v '):true.update(int(x) for x in line.split()[1:] if int(x)>0)
for line in stem.with_suffix('.cnf').read_text().splitlines():
 if not line or line[0] in 'cp':continue
 clause=[int(x) for x in line.split() if x!='0']
 assert any((x in true) if x>0 else (-x not in true) for x in clause), ('unsatisfied CNF clause',clause)
n=meta['n'];gates=[];cache={};wires=list(range(n))
def gate(op,a,b):
 a,b=sorted((a,b));key=(op,a,b)
 if key not in cache:cache[key]=n+len(gates);gates.append(key)
 return cache[key]
def many(values):
 assert values
 out=values[0]
 for x in values[1:]:out=gate(1,out,x)
 return out
for ss in meta['selectors']:
 ports=[many([wires[a] for a,v in enumerate(side) if v in true]) for side in ss]
 wires.append(gate(0,*ports))
out=many([wires[n+g] for g,v in enumerate(meta['outs']) if v in true]);edges=meta['edges'] if 'edgevars' not in meta else [e for e,v in zip(meta['edges'],meta['edgevars']) if v in true];left=meta.get('left',n//2);M=Model(n,left,edges,'decoded')
for a in range(left):
 for b in range(a):assert len(M.adj[a]&M.adj[b])<=1
vals=list(M.inputs)
for op,a,b in gates:vals.append(vals[a]&vals[b] if op==0 else vals[a]|vals[b])
assert not(vals[out]&~M.f)
for a,b in meta['positive']:assert vals[out]>>((1<<a)|(1<<b))&1
D=sum(1<<k for k,(a,b) in enumerate(M.edges) if vals[out]>>((1<<a)|(1<<b))&1)
result=dict(gates=gates,output=out,n=n,edges=edges,D=D,accepted=D.bit_count(),matching=M.tau(D),exact=vals[out]==M.f,AND=sum(op==0 for op,a,b in gates),OR=sum(op==1 for op,a,b in gates));stem.with_suffix('.decoded.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['gates','edges']}))
