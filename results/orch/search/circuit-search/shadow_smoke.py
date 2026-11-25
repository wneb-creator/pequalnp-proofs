import json,subprocess,sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
star=json.loads((base/'star27.json').read_text())
for count,expected in [(27,20),(28,10)]:
 gates=star if count==27 else star+[['and',40,40]]
 cnf=base/f'shadow-smoke-{count}.cnf'
 with (base/f'shadow-smoke-{count}-encode.log').open('w') as log:
  subprocess.run([sys.executable,str(base/'synthesize.py'),'--gates',str(count),'--shadow-missing','3','--output',str(cnf)],stdout=log,stderr=subprocess.STDOUT,check=True)
 meta=json.loads(cnf.with_suffix('.map.json').read_text());units=[]
 for (op,a,b),s in zip(gates,meta['structure']):
  a,b=sorted([a,b]);units.extend([s['left'][a],s['right'][b],s['op'] if op=='or' else -s['op']])
 lines=cnf.read_text().splitlines();fields=lines[0].split();fields[-1]=str(int(fields[-1])+len(units));lines[0]=' '.join(fields)
 lines.extend(str(v)+' 0' for v in units);cnf.write_text('\n'.join(lines)+'\n')
 solve=base/f'shadow-smoke-{count}-solve.log'
 with solve.open('w') as log:
  rc=subprocess.run([str(base/'cadical/build/cadical'),'-t','10',str(cnf)],stdout=log,stderr=subprocess.STDOUT).returncode
 assert rc==expected,(count,rc,expected)
 if rc==10:
  with (base/f'shadow-smoke-{count}-verified.log').open('w') as log:
   subprocess.run([sys.executable,str(base/'decode.py'),str(cnf.with_suffix('.map.json')),str(solve)],stdout=log,stderr=subprocess.STDOUT,check=True)
  model={int(x) for line in solve.read_text().splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
  assert all(v not in model for v in meta['structure'][-1]['quadratic'])
 print('fixed circuit',count,'gates:',{10:'SAT with all quadratic target bits absent; truth table verified',20:'UNSAT as expected for read-1 star'}[rc],flush=True)
