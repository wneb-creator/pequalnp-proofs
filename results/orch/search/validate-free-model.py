import argparse,json,re
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--cnf',required=True);ap.add_argument('--log',required=True);ap.add_argument('--p',type=int,required=True);ap.add_argument('--l',type=int,required=True);ap.add_argument('--edges',required=True);ap.add_argument('--gates',type=int,required=True);ap.add_argument('--kind',choices=['and','or'],required=True);ap.add_argument('--mixed',action='store_true');ap.add_argument('--out',required=True);a=ap.parse_args();n=a.p+a.l;k=a.gates;E=[tuple(map(int,e.split(','))) for e in a.edges.split(';')]
log=Path(a.log).read_text();assert 's SATISFIABLE' in log
model={abs(int(v)):int(v)>0 for line in log.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)!=0}
names={int(m.group(1)):m.group(2) for line in Path(a.cnf).read_text().splitlines() if (m:=re.fullmatch(r'c (\d+) (\S+)',line))}
sel={name:model.get(i,False) for i,name in names.items()};gs=[{'a':[i for i in range(n+j) if sel.get(f'a{j}s{i}',False)],'b':[i for i in range(n+j) if sel.get(f'b{j}s{i}',False)]} for j in range(k)];out=[i for i in range(n+k) if sel.get(f'outs{i}',False)]
assert all(g['a'] and g['b'] for g in gs) and out
if a.kind=='and' and not a.mixed:assert all(len({i<a.p for i in g[side] if i<n})<=1 for g in gs for side in ['a','b'])
valid=True;dirty=set();first_bad=None
for x in range(1<<n):
 w=[bool(x>>i&1) for i in range(n)]
 for g in gs:
  if a.kind=='and':w.append(any(w[i] for i in g['a']) and any(w[i] for i in g['b']))
  else:w.append(all(w[i] for i in g['a']) or all(w[i] for i in g['b']))
 actual=any(w[i] for i in out) if a.kind=='and' else all(w[i] for i in out);expected=any((x>>u&1) and (x>>(a.p+v)&1) for u,v in E)
 if not expected:dirty.update(j for j in range(k) if w[n+j])
 if actual!=expected:valid=False;first_bad=x;break
report={'valid_all_assignments':valid,'assignments':1<<n,'first_bad':first_bad,'p':a.p,'l':a.l,'edges':E,'kind':a.kind,'gates':gs,'output':out,'dirty_counted_gates':sorted(dirty),'cnf':a.cnf,'solver_log':a.log}
Path(a.out).write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k not in ['gates','edges','output']}));assert valid
