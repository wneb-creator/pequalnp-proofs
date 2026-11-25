import json,subprocess,sys
from pathlib import Path
base=Path(__file__).resolve().parent
d=json.loads((base/'theta3-or7-full.profile.json').read_text())
d['window_budget']=12;d['and_count']=4
profile=base/'theta3-control12.profile.json';profile.write_text(json.dumps(d,indent=2)+'\n')
cnf=base/'theta3-control12.cnf'
subprocess.run([sys.executable,str(base/'local_sat.py'),str(profile),str(cnf),'ordered'],check=True)
m=json.loads(Path(str(cnf)+'.meta.json').read_text())
raw=[(0,5,6),(0,8,7),(1,0,9),(0,4,5),(1,1,11),(0,4,6),(1,2,13),(0,4,7),(1,3,15),(0,10,12),(0,14,16),(0,17,18)]
pending=list(enumerate(raw,8));mapped={i:i for i in range(8)};gates=[]
while pending:
 ready=[(tuple(sorted([mapped[a],mapped[b]],reverse=True)),i,(op,a,b)) for i,(op,a,b) in pending if a in mapped and b in mapped]
 _,i,(op,a,b)=min(ready);a,b=sorted([mapped[a],mapped[b]])
 mapped[i]=8+len(gates);gates.append((op,a,b));pending=[(j,g) for j,g in pending if j!=i]
for mask in range(256):
 w=[bool(mask>>i&1) for i in range(8)]
 for op,a,b in gates:w.append(w[a] and w[b] if op else w[a] or w[b])
 assert w[-1]==any(mask>>a&1 and mask>>b&1 for a,b in d['graph_edges'])
units=[]
for j,(op,a,b) in enumerate(gates):units.extend([m['ops'][j] if op else -m['ops'][j],m['choose'][j][0][a],m['choose'][j][1][b]])
lines=cnf.read_text().splitlines();h=lines[0].split();h[3]=str(int(h[3])+len(units))
cnf.write_text(' '.join(h)+'\n'+'\n'.join(lines[1:])+'\n'+'\n'.join(str(x)+' 0' for x in units)+'\n')
print(json.dumps({'control_gates':gates,'and_count':sum(x[0] for x in gates),'or_count':sum(not x[0] for x in gates),'truth_rows_verified':256}))
