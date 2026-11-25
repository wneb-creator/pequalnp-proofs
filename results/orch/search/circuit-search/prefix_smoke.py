import json,subprocess,sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
gates=json.loads((base/'star27.json').read_text())+[['and',40,40]]
for prefix,expected in [(20,10),(28,20)]:
 cnf=base/f'prefix-smoke-{prefix}.cnf'
 with (base/f'prefix-smoke-{prefix}-encode.log').open('w') as log:
  subprocess.run([sys.executable,str(base/'synthesize.py'),'--gates','28','--shadow-missing','3','--minimal-prefix',str(prefix),'--output',str(cnf)],stdout=log,stderr=subprocess.STDOUT,check=True)
 meta=json.loads(cnf.with_suffix('.map.json').read_text());units=[]
 for (op,a,b),s in zip(gates,meta['structure']):
  a,b=sorted([a,b]);units.extend([s['left'][a],s['right'][b],s['op'] if op=='or' else -s['op']])
 lines=cnf.read_text().splitlines();fields=lines[0].split();fields[-1]=str(int(fields[-1])+len(units));lines[0]=' '.join(fields)
 lines.extend(str(v)+' 0' for v in units);cnf.write_text('\n'.join(lines)+'\n')
 meta['clauses']+=len(units);meta['fixed_test_network']=True;cnf.with_suffix('.map.json').write_text(json.dumps(meta))
 solve=base/f'prefix-smoke-{prefix}-solve.log'
 with solve.open('w') as log:
  rc=subprocess.run([str(base/'cadical/build/cadical'),'-t','10',str(cnf)],stdout=log,stderr=subprocess.STDOUT).returncode
 assert rc==expected,(prefix,rc,expected)
 if rc==10:
  with (base/f'prefix-smoke-{prefix}-verified.log').open('w') as log:
   subprocess.run([sys.executable,str(base/'decode.py'),str(cnf.with_suffix('.map.json')),str(solve)],stdout=log,stderr=subprocess.STDOUT,check=True)
 print('first',prefix,'gates undominated:',{10:'SAT; tail copy allowed; all16384 inputs verified',20:'UNSAT; domination of final copy detected'}[rc],flush=True)
