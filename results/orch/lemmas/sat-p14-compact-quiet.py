import argparse,importlib.util,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('compact_core',BASE/'sat-p14-compact.py');core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
def build(cap,equality=True,negative_proxy=False,graph='fano',quiet=True,oriented=True,edge_cover=True,positive_atoms=True):
 c,m=core.build(cap,equality,negative_proxy,graph);begin=len(c.cs);extra=dict(quiet=quiet,oriented=oriented,edge_cover=edge_cover,positive_atoms=positive_atoms,clause_begin=begin,covers=[],traces=[])
 if oriented:
  for a in m['atoms']:
   left=a['slots'][0]['primary']+a['slots'][0]['prior'];right=a['slots'][1]['primary']+a['slots'][1]['prior']
   for i,z in enumerate(right):c.add(-z,*left[:i])
 if positive_atoms:
  for a in m['atoms']:c.add(-a['active'],*[a['values'][r] for r,mask in enumerate(m['tests']) if mask in m['positive']])
 if edge_cover:
  for p,l in m['edges']:
   terms=[];gates=[]
   for a in m['atoms']:
    s,t=a['slots'];q=c.var();r=c.var();c.conj(q,s['primary'][p],t['primary'][l]);c.conj(r,s['primary'][l],t['primary'][p]);terms.extend([q,r]);gates.append([q,r])
   c.add(*terms);extra['covers'].append(dict(edge=[p,l],terms=gates))
 if quiet:
  for base,seed in [(0,7),(7,0)]:
   derivatives=[];rows=[]
   for a in m['atoms']:
    sd=[];sm=[]
    for s in a['slots']:
     terms=[]
     for k,z in enumerate(s['prior']):
      q=c.var();c.conj(q,z,derivatives[k]);terms.append(q)
     d=c.var();c.disjunction(d,[s['primary'][seed]]+terms);sd.append(d);sm.append(dict(terms=terms,out=d))
    ta=c.var();tb=c.var();d=c.var();c.conj(ta,a['slots'][0]['primary'][base],sd[1]);c.conj(tb,sd[0],a['slots'][1]['primary'][base]);c.disjunction(d,[ta,tb]);derivatives.append(d);rows.append(dict(slots=sm,left_term=ta,right_term=tb,out=d))
   terms=[]
   for j,z in enumerate(m['final']):
    q=c.var();c.conj(q,z,derivatives[j]);terms.append(q)
   out=c.var();c.disjunction(out,terms);c.add(-out);extra['traces'].append(dict(base=base,seed=seed,atoms=rows,terms=terms,out=out))
 extra['clause_end']=len(c.cs);m['extension']=extra;m['variables']=c.n;m['clauses']=len(c.cs);return c,m

def compact_derivative(compact,base,seed):
 ds=[]
 for a in compact['atoms']:
  values=[base in s['primary'] for s in a['slots']];derivs=[seed in s['primary'] or any(ds[k] for k in s['prior']) for s in a['slots']]
  ds.append(values[0] and derivs[1] or derivs[0] and values[1])
 return any(ds[j] for j in compact['final'])

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--no-equality',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.cap,not a.no_equality,a.negative_proxy,a.graph);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([core.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'};candidate=core.decode(m,model);core.validate(candidate);assert not compact_derivative(candidate,0,7) and not compact_derivative(candidate,7,0);path=BASE/(a.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=16384,both_marked_derivatives=False)),flush=True)
if __name__=='__main__':main()
