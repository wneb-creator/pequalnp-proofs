from pathlib import Path
import json,itertools
base=Path('/tmp/oec/pequalnp-pilot-42/sat');ls=(base/'free-and-10-prune.cnf').read_text().splitlines();head=ls[0].split();counter=int(head[2]);extra=[];ns=json.loads((base/'free-and-vars-10.json').read_text());reps=json.loads((base/'free-and-first-reps.json').read_text());choices=[]
for val,a,b in reps:
 counter+=1;choice=counter;choices.append(choice)
 for arg,factors in enumerate([a,b]):
  for j in range(14):
   v=ns[f's0_{arg}_{j}'];extra.append(f'-{choice} {v if j in factors else -v} 0')
extra.append(' '.join(map(str,choices))+' 0')
for a,b in itertools.combinations(choices,2):extra.append(f'-{a} -{b} 0')
head[2]=str(counter);head[3]=str(int(head[3])+len(extra));(base/'free-and-10-sym.cnf').write_text(' '.join(head)+'\n'+'\n'.join(ls[1:]+extra)+'\n');print('variables',counter,'extra clauses',len(extra))
