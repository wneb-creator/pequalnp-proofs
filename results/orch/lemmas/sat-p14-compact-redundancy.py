import argparse,importlib.util,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('cross_core',BASE/'sat-p14-compact-cross.py');cross_core=importlib.util.module_from_spec(spec);spec.loader.exec_module(cross_core)
quiet=cross_core.quiet

def build(cap,equality=True,negative_proxy=False,graph='fano',nine_free=True,incomparable=True,partition=True,empty_opposite=True,shared_slot=True,cross=True,positive_redundancy=True):
 c,m=cross_core.build(cap,equality,negative_proxy,graph,nine_free,incomparable,partition,empty_opposite,shared_slot,cross)
 extra=dict(enabled=positive_redundancy,variable_begin=c.n,clause_begin=len(c.cs),atoms=[])
 if positive_redundancy:
  assert equality
  for atom in m['atoms']:
   rows=[]
   for x in range(14):
    indices=[i for i,mask in enumerate(m['positive']) if not(mask>>x&1)];terms=[atom['values'][i]for i in indices];v=c.var();c.disjunction(v,terms)
    c.add(-atom['modes'][1+x],v)
    for consumer in atom['consumers']:
     sx=m['atoms'][consumer['atom']]['slots'][consumer['side']]['primary'][x]
     c.add(-atom['modes'][0],-consumer['var'],-sx,v)
    rows.append(dict(label=x,positive_indices=indices,terms=terms,out=v))
   extra['atoms'].append(rows)
 extra['clause_end']=len(c.cs);m['positive_redundancy']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--no-equality',action='store_true');p.add_argument('--no-nine-free',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--no-incomparable',action='store_true');p.add_argument('--no-partition',action='store_true');p.add_argument('--no-empty-opposite',action='store_true');p.add_argument('--no-shared-slot',action='store_true');p.add_argument('--no-cross',action='store_true');p.add_argument('--no-positive-redundancy',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.cap,not a.no_equality,a.negative_proxy,a.graph,not a.no_nine_free,not a.no_incomparable,not a.no_partition,not a.no_empty_opposite,not a.no_shared_slot,not a.no_cross,not a.no_positive_redundancy);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([quiet.core.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'};candidate=quiet.core.decode(m,model);quiet.core.validate(candidate);assert not quiet.compact_derivative(candidate,0,7) and not quiet.compact_derivative(candidate,7,0);path=BASE/(a.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=16384,both_marked_derivatives=False)),flush=True)
if __name__=='__main__':main()
