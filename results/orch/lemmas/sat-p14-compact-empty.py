import argparse,importlib.util,itertools,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('partition_core',BASE/'sat-p14-compact-partition.py');partition_core=importlib.util.module_from_spec(spec);spec.loader.exec_module(partition_core)
quiet=partition_core.quiet

def build(cap,equality=True,negative_proxy=False,graph='fano',nine_free=True,incomparable=True,partition=True,empty_opposite=True):
 c,m=partition_core.build(cap,equality,negative_proxy,graph,nine_free,incomparable,partition)
 extra=dict(enabled=empty_opposite,variable_begin=c.n,clause_begin=len(c.cs),slots=[])
 if empty_opposite:
  assert equality
  for j,atom in enumerate(m['atoms']):
   for side in range(2):
    own=atom['slots'][side]['primary'];other=atom['slots'][1-side]['primary'];nonempty=c.var();c.disjunction(nonempty,own)
    for group in [range(7),range(7,14)]:
     for a,b in itertools.combinations(group,2):c.add(nonempty,-other[a],-other[b])
    extra['slots'].append(dict(atom=j,empty_side=side,nonempty=nonempty))
 extra['clause_end']=len(c.cs);m['empty_opposite']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--no-equality',action='store_true');p.add_argument('--no-nine-free',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--no-incomparable',action='store_true');p.add_argument('--no-partition',action='store_true');p.add_argument('--no-empty-opposite',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.cap,not a.no_equality,a.negative_proxy,a.graph,not a.no_nine_free,not a.no_incomparable,not a.no_partition,not a.no_empty_opposite);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([quiet.core.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'};candidate=quiet.core.decode(m,model);quiet.core.validate(candidate);assert not quiet.compact_derivative(candidate,0,7) and not quiet.compact_derivative(candidate,7,0);path=BASE/(a.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=16384,both_marked_derivatives=False)),flush=True)
if __name__=='__main__':main()
