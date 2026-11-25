from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-111/counterexample')
ls=(p/'search.stdout').read_text().splitlines();start=max(i for i,l in enumerate(ls) if l.startswith('score '));gates=[]
for line in ls[start+1:start+20]:
 no,op,a,b=line.split();gates.append((int(no),op,int(a),int(b)))
ordered=[];known={i:i for i in range(10)};pending=list(gates)
while pending:
 ready=[g for g in pending if g[2] in known and g[3] in known]
 def key(g):return tuple(sorted([known[g[2]],known[g[3]]]))+(0 if g[1]=='AND' else 1,)
 g=min(ready,key=key);pending.remove(g);a,b=sorted([known[g[2]],known[g[3]]]);known[g[0]]=10+len(ordered);ordered.append((g[0],g[1],a,b))
base=(p/'p19-strengthened-n1.cnf').read_text().splitlines();h=base[0].split();A,s=1055,19;ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
for k,free in enumerate([{18,19,20,21},{10,16,17,18,19,20,21},{10,11,12,16,17,18,19,20,21}]):
 extra=[]
 for j,(old,op,a,b) in enumerate(ordered):
  if old not in free:extra.extend([[ix(0,j,0 if op=='AND' else 1)],[ix(1,j,a)],[ix(2,j,b)]])
 (p/f'local{k}.cnf').write_text(f'p cnf {h[2]} {int(h[3])+len(extra)}\n'+'\n'.join(base[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in extra))
