import argparse,importlib.util,itertools,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('local_core',BASE/'sat-collinear4.py');local=importlib.util.module_from_spec(spec);spec.loader.exec_module(local)
broad=local.broad;EDGES=local.EDGES;ORIGINAL=local.ORIGINAL
validate_local=local.validate_local;splice=local.splice
REPRESENTATIVES=[(0,4),(0,8),(0,9),(2,9)]
def build(size,double=True,minimal=True,orbits=True):
 c,m=local.build(size,double);extra=dict(minimal=minimal,orbits=orbits,variable_begin=c.n,clause_begin=len(c.cs),gates=[],representatives=REPRESENTATIVES)
 if minimal:
  rowsets=[list(range(len(m['positive']),len(m['tests']))),list(range(len(m['positive'])))]
  for gate in m['gates']:
   entry=[]
   for operation,rows in zip(['and','or'],rowsets):
    directions=[]
    for first,second in [(gate['selected_a'],gate['selected_b']),(gate['selected_b'],gate['selected_a'])]:
     terms=[]
     for row in rows:
      d=c.var();c.conj(d,first[row],-second[row]);terms.append(d)
     c.add(-gate['op'] if operation=='and' else gate['op'],*terms);directions.append(terms)
    entry.append(dict(operation=operation,rows=rows,directions=directions))
   c.add(*[-gate['outputs'][r] for r in rowsets[0]]);extra['gates'].append(entry)
 if orbits:
  for edge,flag in zip(EDGES,m['flags']):
   if edge not in REPRESENTATIVES:c.add(-flag)
 extra['clause_end']=len(c.cs);m['minimality']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def symmetry_check():
 points=[0,1,3];middle=[9,7,6];leaves=[4,10,5];maps=[]
 for perm in itertools.permutations(range(3)):
  mapping=list(range(11))
  for group in [points,middle,leaves]:
   for i in range(3):mapping[group[i]]=group[perm[i]]
  assert sorted(mapping)==list(range(11));assert {(mapping[a],mapping[b]) for a,b in EDGES}==set(EDGES);maps.append(mapping)
 orbits=[sorted({(p[a],p[b]) for p in maps}) for a,b in REPRESENTATIVES]
 assert len({tuple(x) for x in orbits})==4 and set().union(*map(set,orbits))==set(EDGES)
 return dict(permutations=maps,representatives=REPRESENTATIVES,orbits=orbits)

def main():
 p=argparse.ArgumentParser();p.add_argument('--size',type=int,default=15);p.add_argument('--ordinary',action='store_true');p.add_argument('--tag',required=True);p.add_argument('--no-minimality',action='store_true');p.add_argument('--no-orbits',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.size,not a.ordinary,not a.no_minimality,not a.no_orbits);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['inputs','size','variables','clauses','double']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([broad.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(z) for line in text.splitlines() if line.startswith('v ') for z in line.split()[1:] if z!='0'};edge=next(e for e,z in zip(EDGES,m['flags']) if z in model)
  gates=[['and' if g['op'] in model else 'or',next(i for i,z in enumerate(g['select_a']) if z in model),next(i for i,z in enumerate(g['select_b']) if z in model)] for g in m['gates']]
  ds=validate_local(gates,edge,not a.ordinary);witness=dict(original=ORIGINAL,gates=gates,edge=edge,derivatives=ds,size=a.size);(BASE/(a.tag+'.witness.json')).write_text(json.dumps(witness,indent=2)+'\n');full=splice(gates,edge);(BASE/(a.tag+'.full-fano.json')).write_text(json.dumps(full,indent=2)+'\n');print(json.dumps(dict(local_witness=str(BASE/(a.tag+'.witness.json')),full_witness=str(BASE/(a.tag+'.full-fano.json')),full_size=full['size'],derivatives=ds)),flush=True)
if __name__=='__main__':main()
