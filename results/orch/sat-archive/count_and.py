import sys,json,itertools
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
n=14;count=int(sys.argv[1])
ls=(base/'circuit-14.cnf').read_text().splitlines()
vs=json.loads((base/'vars-14.json').read_text());ops=[vs[f'o{k}'] for k in range(13,27)]
new=[]
for subset in itertools.combinations(ops,count+1):new.append(' '.join(map(str,subset))+' 0')
for subset in itertools.combinations(ops,n-count+1):new.append(' '.join(str(-x) for x in subset)+' 0')
head=ls[0].split();head[-1]=str(int(head[-1])+len(new))
(base/f'circuit-14-and{count}.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+new)+'\n')
print(count,len(new))
