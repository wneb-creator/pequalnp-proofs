import itertools,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-86/counterexample')
d=json.loads((base/'c6-8-sym.json').read_text())
for cap in [4,5]:
 source=base/('c6-8-sym.cnf' if cap==4 else 'c6-8-sym-fixed.cnf')
 lines=source.read_text().splitlines()
 extra=[[-v for v in subset] for subset in itertools.combinations(d['O'],cap+1)]
 head=lines[0].split();head[3]=str(int(head[3])+len(extra));lines[0]=' '.join(head)
 lines.extend(' '.join(map(str,c))+' 0' for c in extra)
 (base/('c6-8-or'+str(cap)+'.cnf')).write_text('\n'.join(lines)+'\n')
print('Prepared C6 eight-gate ORcap4 target and fixed ORcap5 positive control.')
