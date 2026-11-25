import json,sys,subprocess
from pathlib import Path
base=Path(__file__).resolve().parent;cnf=base/'c5-nested-control14.cnf';subprocess.run([sys.executable,str(base/'topform_sat_v1.py'),'5','14',str(cnf),'ustar'],check=True);meta=json.loads(Path(str(cnf)+'.meta.json').read_text());n=5;edges=meta['edges'];negative=[m for m in range(32) if not any(m>>a&1 and m>>b&1 for a,b in edges)];maxind=[m for m in negative if all(m>>i&1 or m|(1<<i) not in negative for i in range(5))];raw=[];roots=[]
def add(op,a,b):raw.append((op,a,b));return 4+len(raw)
for mask in maxind:
 clause=[i for i in range(5) if not(mask>>i&1)];v=clause[0]
 for w in clause[1:]:v=add(0,v,w)
 roots.append(v)
v=roots[0]
for w in roots[1:]:v=add(1,v,w)
assert len(raw)==14
pending=list(enumerate(raw,5));mapped={i:i for i in range(5)};gates=[]
while pending:
 _,j,(op,a,b)=min((tuple(sorted((mapped[a],mapped[b]),reverse=True)),j,(op,a,b)) for j,(op,a,b) in pending if a in mapped and b in mapped)
 a,b=sorted((mapped[a],mapped[b]));mapped[j]=5+len(gates);gates.append((op,a,b));pending=[(i,g) for i,g in pending if i!=j]
units=[]
for j,(op,a,b) in enumerate(gates):units.extend([meta['ops'][j] if op else -meta['ops'][j],meta['choice'][j][0][a],meta['choice'][j][1][b]])
lines=cnf.read_text().splitlines();h=lines[0].split();h[3]=str(int(h[3])+len(units));cnf.write_text(' '.join(h)+'\n'+'\n'.join(lines[1:])+'\n'+'\n'.join(str(x)+' 0' for x in units)+'\n');print(json.dumps({'pinned_gates':gates,'minimal_vertex_cover_clauses':[[i for i in range(5) if not(m>>i&1)] for m in maxind]}))
