from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-111/counterexample');base=(p/'p19-strengthened-n1.cnf').read_text().splitlines();h=base[0].split();s,A=19,1055;ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
pairs=[(50,3),(50,6),(50,12),(116,3),(116,6)]
for i,(ind,edge) in enumerate(pairs):
 extra=[]
 for j in range(s):extra.extend([[-ix(0,j,3),ix(4,j,ind)],[-ix(0,j,3),-ix(4,j,edge)]])
 q=p/f'p19-n1-orbit{i}.cnf';q.write_text(f'p cnf {h[2]} {int(h[3])+len(extra)}\n'+'\n'.join(base[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in extra));print(q.name,'independent',ind,'edge',edge)
