import argparse,importlib.util,itertools,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('essential_core',BASE/'sat-p14-compact-essential.py');essential=importlib.util.module_from_spec(spec);spec.loader.exec_module(essential)
quiet=essential.quiet

def build(cap,equality=True,negative_proxy=False,graph='fano',nine_free=True,incomparable=True,partition=True):
 c,m=essential.build(cap,equality,negative_proxy,graph,nine_free,incomparable)
 extra=dict(enabled=partition,variable_begin=c.n,clause_begin=len(c.cs),triples=[])
 if partition:
  assert equality and nine_free
  pairs={tuple(item['pair']):item['out'] for item in m['enhancements']['cooccurrence']}
  for side in [range(7),range(7,14)]:
   for a,b,d in itertools.combinations(side,3):
    ab,ad,bd=pairs[a,b],pairs[a,d],pairs[b,d]
    c.add(-ab,-bd,ad);c.add(-ab,-ad,bd);c.add(-ad,-bd,ab)
    extra['triples'].append(dict(labels=[a,b,d],variables=[ab,ad,bd]))
 extra['clause_end']=len(c.cs);m['partition']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--no-equality',action='store_true');p.add_argument('--no-nine-free',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--no-incomparable',action='store_true');p.add_argument('--no-partition',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.cap,not a.no_equality,a.negative_proxy,a.graph,not a.no_nine_free,not a.no_incomparable,not a.no_partition);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([quiet.core.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'};candidate=quiet.core.decode(m,model);quiet.core.validate(candidate);assert not quiet.compact_derivative(candidate,0,7) and not quiet.compact_derivative(candidate,7,0);path=BASE/(a.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=16384,both_marked_derivatives=False)),flush=True)
if __name__=='__main__':main()
