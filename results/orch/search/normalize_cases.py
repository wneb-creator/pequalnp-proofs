import sys,json
from pathlib import Path
base=Path(sys.argv[1]);out=Path(sys.argv[2]);kind=sys.argv[3] if len(sys.argv)>3 else 'all';m=json.loads(base.with_suffix('.meta.json').read_text());s,A=m['s'],m['A'];ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
extra=[[-ix(0,j,op)] for j in range(s) for op in [0,5,6,7]]
if kind in ['edge','nonedge']:
 extra.extend([[ix(0,0,4)],[ix(1,0,0)],[ix(2,0,1 if kind=='edge' else 2)]])
else:assert kind=='all'
ls=base.read_text().splitlines();h=ls[0].split();out.write_text(f'p cnf {h[2]} {int(h[3])+len(extra)}\n'+'\n'.join(ls[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in extra));out.with_suffix('.meta.json').write_text(json.dumps(m)+'\n')
