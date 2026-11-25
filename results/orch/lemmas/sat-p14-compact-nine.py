import argparse,importlib.util,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('quiet_core',BASE/'sat-p14-compact-quiet.py');quiet=importlib.util.module_from_spec(spec);spec.loader.exec_module(quiet)

def free_originals(c):
 def adjacent(x,y):
  if x>=7:x,y=y,x
  return x<7<=y and (x-(y-7))%7 in (0,1,3)
 return [x for x in range(14) if (x<7)!=(c<7) and not adjacent(c,x)]

def build(cap,equality=True,negative_proxy=False,graph='fano',nine_free=True):
 c,m=quiet.build(cap,equality,negative_proxy,graph);extra=dict(nine_free=nine_free,variable_begin=c.n,clause_begin=len(c.cs),ordering=[],cooccurrence=[],centers=[])
 for j,atom in enumerate(m['atoms']):
  flags=[None]*j
  for k in range(j-1,-1,-1):
   d=c.var();c.disjunction(d,[atom['slots'][0]['prior'][k],atom['slots'][1]['prior'][k]]+([] if k==j-1 else [flags[k+1]]));flags[k]=d
  extra['ordering'].append(flags)
  if j:
   for k,old in enumerate(extra['ordering'][j-1]):c.add(-atom['active'],-old,flags[k])
 if nine_free:
  assert equality
  pairs={}
  for x in range(14):
   for y in range(x+1,14):
    terms=[]
    for atom in m['atoms']:
     for slot in atom['slots']:
      d=c.var();c.conj(d,slot['primary'][x],slot['primary'][y]);terms.append(d)
    d=c.var();c.disjunction(d,terms);pairs[x,y]=d;extra['cooccurrence'].append(dict(pair=[x,y],terms=terms,out=d))
  for x in range(14):
   labels=[y for y in range(14) if y!=x];neighbors=[pairs[min(x,y),max(x,y)] for y in labels];free=free_originals(x);assert len(free)==4
   all6=c.threshold(neighbors,6);free2=c.threshold([pairs[min(x,y),max(x,y)] for y in free],2);c.add(-all6['root'],free2['root']);extra['centers'].append(dict(center=x,labels=labels,free_originals=free,all_at_least_six=all6,free_at_least_two=free2))
 extra['clause_end']=len(c.cs);m['enhancements']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def canonicalize(control):
 pending=set(range(len(control['atoms'])));mapping={};atoms=[]
 while pending:
  ready=[j for j in pending if all(k in mapping for slot in control['atoms'][j]['slots'] for k in slot['prior'])];assert ready
  j=min(ready,key=lambda j:(max([mapping[k] for s in control['atoms'][j]['slots'] for k in s['prior']],default=-1),j));old=control['atoms'][j]
  slots=[dict(primary=list(s['primary']),prior=sorted(mapping[k] for k in s['prior'])) for s in old['slots']];slots.sort(key=lambda s:min(s['primary']+[14+k for k in s['prior']]))
  mapping[j]=len(atoms);atoms.append(dict(slots=slots,mode=old.get('mode')));pending.remove(j)
 out=dict(control);out['atoms']=atoms;out['final']=sorted(mapping[j] for j in control['final']);return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--no-equality',action='store_true');p.add_argument('--no-nine-free',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.cap,not a.no_equality,a.negative_proxy,a.graph,not a.no_nine_free);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([quiet.core.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'};candidate=quiet.core.decode(m,model);quiet.core.validate(candidate);assert not quiet.compact_derivative(candidate,0,7) and not quiet.compact_derivative(candidate,7,0);path=BASE/(a.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=16384,both_marked_derivatives=False)),flush=True)
if __name__=='__main__':main()
