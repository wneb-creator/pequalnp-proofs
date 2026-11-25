import argparse,importlib.util,itertools,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('shared_core',BASE/'sat-p14-compact-shared.py');shared=importlib.util.module_from_spec(spec);spec.loader.exec_module(shared)
quiet=shared.quiet

def build(cap,equality=True,negative_proxy=False,graph='fano',nine_free=True,incomparable=True,partition=True,empty_opposite=True,shared_slot=True,cross=True):
 c,m=shared.build(cap,equality,negative_proxy,graph,nine_free,incomparable,partition,empty_opposite,shared_slot)
 extra=dict(enabled=cross,variable_begin=c.n,clause_begin=len(c.cs),pair_prefixes=[],transfer_count=0)
 if cross:
  assert equality and nine_free
  pairs={tuple(z['pair']):z for z in m['enhancements']['cooccurrence']}
  for pair in m['enhancements']['cooccurrence']:
   previous=False;prefixes=[]
   for index,t in enumerate(pair['terms']):
    c.add(quiet.core.neg(previous),-t)
    if index+1<len(pair['terms']):
     p=c.var();c.disjunction(p,[previous,t]);prefixes.append(p);previous=p
   extra['pair_prefixes'].append(dict(pair=pair['pair'],terms=pair['terms'],prefixes=prefixes))
  slots=[slot for atom in m['atoms'] for slot in atom['slots']]
  for x in range(14):
   for a,b in itertools.combinations([y for y in range(14) if y!=x],2):
    if b in shared.neighbors(a):continue
    pa=pairs[tuple(sorted([x,a]))];pb=pairs[tuple(sorted([x,b]))]
    for index,slot in enumerate(slots):
     c.add(-pa['terms'][index],-pb['out'],slot['primary'][b]);extra['transfer_count']+=1
 extra['clause_end']=len(c.cs);m['cross_support']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--no-equality',action='store_true');p.add_argument('--no-nine-free',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--no-incomparable',action='store_true');p.add_argument('--no-partition',action='store_true');p.add_argument('--no-empty-opposite',action='store_true');p.add_argument('--no-shared-slot',action='store_true');p.add_argument('--no-cross',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.cap,not a.no_equality,a.negative_proxy,a.graph,not a.no_nine_free,not a.no_incomparable,not a.no_partition,not a.no_empty_opposite,not a.no_shared_slot,not a.no_cross);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([quiet.core.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'};candidate=quiet.core.decode(m,model);quiet.core.validate(candidate);assert not quiet.compact_derivative(candidate,0,7) and not quiet.compact_derivative(candidate,7,0);path=BASE/(a.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=16384,both_marked_derivatives=False)),flush=True)
if __name__=='__main__':main()
