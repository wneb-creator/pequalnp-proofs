import itertools,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-86/counterexample')
d=json.loads((base/'c6-9-sym.json').read_text())
old=json.loads((base/'c6-8-sym.json').read_text())
units={int(line.split()[0]) for line in (base/'c6-8-sym-fixed.cnf').read_text().splitlines() if len(line.split())==2}
gates=[]
for aa,bb,o in zip(old['A'],old['B'],old['O']):
 a=[i for i,x in enumerate(aa) if x in units];b=[i for i,x in enumerate(bb) if x in units]
 assert len(a)==len(b)==1 and ((o in units)!=(-o in units))
 gates.append((a[0],b[0],int(o in units)))
n=old['n'];j=next(i for i,g in enumerate(gates) if g[2]==0 and min(g[:2])<n)
point=min(gates[j][:2]);wire=n+j
control=gates[:j+1]+[(point,wire,0)]+[(a+int(a>=wire),b+int(b>=wire),o) for a,b,o in gates[j+1:]]
# Canonical topological order, reindexing all selected predecessor wires.
index={i:i for i in range(n)};remaining=set(range(len(control)));ordered=[]
while remaining:
 ready=[]
 for i in remaining:
  a,b,o=control[i]
  if a in index and b in index:ready.append((*sorted((index[a],index[b])),o,i))
 assert ready
 a,b,o,i=min(ready);index[n+i]=n+len(ordered);ordered.append((a,b,o));remaining.remove(i)
assert index[n+len(control)-1]==n+len(control)-1
vals=[sum(bool(x&(1<<i))<<x for x in range(1<<n)) for i in range(n)]
for a,b,o in ordered:vals.append(vals[a]|vals[b] if o else vals[a]&vals[b])
target=sum(any((x>>p&1) and (x>>l&1) for p,l in d['edges'])<<x for x in range(1<<n))
assert vals[-1]==target and sum(o for a,b,o in ordered)==5
for cap in [4,5]:
 lines=(base/'c6-9-sym.cnf').read_text().splitlines()
 extra=[[-v for v in subset] for subset in itertools.combinations(d['O'],cap+1)]
 if cap==5:
  for i,(a,b,o) in enumerate(ordered):extra.extend([[d['A'][i][a]],[d['B'][i][b]],[d['O'][i] if o else -d['O'][i]]])
 head=lines[0].split();head[3]=str(int(head[3])+len(extra));lines[0]=' '.join(head)
 lines.extend(' '.join(map(str,c))+' 0' for c in extra)
 (base/('c6-9-or'+str(cap)+'.cnf')).write_text('\n'.join(lines)+'\n')
(base/'c6-9-or5-control.json').write_text(json.dumps(dict(gates=ordered,fulltruth=True,or_count=5),indent=2)+'\n')
print('Prepared C6 nine-gate ORcap4 target and fulltruth-verified fixed ORcap5 control.')
