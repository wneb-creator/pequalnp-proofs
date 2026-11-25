import argparse,hashlib,json,os,random,subprocess,time
from pathlib import Path
from blif_validate import EDGES,translate
BASE=Path('/tmp/oec/pequalnp-pilot-85/abc-search')
LIB=Path('/tmp/oec/pequalnp-pilot-85/abc-tool/unit.genlib')
TARGET=Path('/tmp/oec/pequalnp-pilot-85/abc-tool/target.blif')
CNFSEED=BASE/'max-independent-cnf.blif'

def star_seed(path,rng,side,expand=False):
 gates=[];terms=[]
 def gate(op,a,b):
  n=14+len(gates);gates.append([op,a,b]);return n
 def ors(ws):
  ws=list(ws)
  while len(ws)>1:
   a=ws.pop(rng.randrange(len(ws)));b=ws.pop(rng.randrange(len(ws)))
   ws.append(gate(1,a,b))
  return ws[0]
 vertices=list(range(7)) if side==0 else list(range(7,14));rng.shuffle(vertices)
 for i in vertices:
  ns=[b if a==i else a for a,b in EDGES if a==i or b==i]
  terms.append(gate(0,i,ors(ns)))
 out=ors(terms)
 if expand:
  old=gates;gates=[];renaming={i:i for i in range(14)};chosen=rng.randrange(len(old))
  for j,(op,a,b) in enumerate(old):
   a=renaming[a];b=renaming[b]
   if j==chosen:
    inv=gate(2,b,-1)
    middle=gate(1-op,a,inv)
    outwire=gate(op,middle,b)
   else:outwire=gate(op,a,b)
   renaming[14+j]=outwire
  out=renaming[out]
 inputs=list(range(14));rng.shuffle(inputs)
 lines=['.model star25','.inputs '+' '.join('x'+str(i) for i in inputs),'.outputs f']
 name=lambda a:'x'+str(a) if a<14 else 'n'+str(a)
 for j,(op,a,b) in enumerate(gates):
  if op==2:lines.append('.gate INV A='+name(a)+' Y='+name(14+j))
  else:lines.append('.gate '+('AND2' if op==0 else 'OR2')+' A='+name(a)+' B='+name(b)+' Y='+name(14+j))
 lines+=['.gate BUF A='+name(out)+' Y=f','.end']
 path.write_text('\n'.join(lines)+'\n')
 check=translate(path)
 assert check['errors']==0 and check['gate_count']==(27 if expand else 25)
 return path

def shannon_seed(path,rng,count):
 variables=rng.sample(list(range(14)),count)
 ports=list(range(14));rng.shuffle(ports)
 lines=['.model shannon_seed','.inputs '+' '.join('x'+str(i) for i in ports),'.outputs f']
 serial=0
 def fresh():
  nonlocal serial
  serial+=1;return 's'+str(serial)
 def cofactor(assignment):
  out=fresh();remaining=[i for i in range(14) if i not in assignment]
  terms=[];constant=False
  for edge in EDGES:
   if any(assignment.get(i,True)==False for i in edge):continue
   term=tuple(i for i in edge if i not in assignment)
   if not term:constant=True;break
   terms.append(term)
  if constant:
   lines.extend(['.names '+out,'1']);return out
  singles={term[0] for term in terms if len(term)==1}
  terms=sorted(set(term for term in terms if len(term)==1 or not any(i in singles for i in term)))
  lines.append('.names '+' '.join('x'+str(i) for i in remaining)+' '+out)
  for term in terms:lines.append(''.join('1' if i in term else '-' for i in remaining)+' 1')
  return out
 def rec(level,assignment):
  if level==count:return cofactor(assignment)
  var=variables[level]
  lo=rec(level+1,{**assignment,var:False})
  hi=rec(level+1,{**assignment,var:True})
  out=fresh()
  lines.extend(['.names x'+str(var)+' '+lo+' '+hi+' '+out,'01- 1','1-1 1'])
  return out
 out=rec(0,{})
 lines.extend(['.names '+out+' f','1 1','.end'])
 path.write_text('\n'.join(lines)+'\n')
 check=translate(path)
 assert check['errors']==0
 return path

def dnf_seed(path,rng):
 ports=list(range(14));rng.shuffle(ports);edges=list(EDGES);rng.shuffle(edges)
 lines=['.model shuffled_dnf','.inputs '+' '.join('x'+str(i) for i in ports),'.outputs f','.names '+' '.join('x'+str(i) for i in ports)+' f']
 lines+=[''.join('1' if i in edge else '-' for i in ports)+' 1' for edge in edges]
 lines+=['.end'];path.write_text('\n'.join(lines)+'\n')
 assert translate(path)['errors']==0
 return path

def cnf_seed(path,rng):
 masks=json.loads(Path('/tmp/oec/pequalnp-pilot-85/linear_network/maximal-negative.json').read_text());rng.shuffle(masks)
 ports=list(range(14));rng.shuffle(ports)
 lines=['.model shuffled_cnf','.inputs '+' '.join('x'+str(i) for i in ports),'.outputs f'];clauses=[]
 for j,mask in enumerate(masks):
  variables=[i for i in range(14) if not(mask>>i&1)];rng.shuffle(variables)
  name='c'+str(j);clauses.append(name)
  lines.append('.names '+' '.join('x'+str(i) for i in variables)+' '+name)
  cubes=['-'*k+'1'+'-'*(len(variables)-k-1)+' 1' for k in range(len(variables))];rng.shuffle(cubes);lines+=cubes
 rng.shuffle(clauses)
 lines+=['.names '+' '.join(clauses)+' f','1'*len(clauses)+' 1','.end'];path.write_text('\n'.join(lines)+'\n')
 assert translate(path)['errors']==0
 return path

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--abc',required=True);ap.add_argument('--runs',type=int,default=200);ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--per-run-seconds',type=float,default=30);ap.add_argument('--seed',type=int,default=9811);ap.add_argument('--extra-ops');ap.add_argument('--mappers');ap.add_argument('--name',default='search');ap.add_argument('--library',default=str(LIB));ap.add_argument('--seed-netlist',action='append',default=[])
 a=ap.parse_args();out=BASE/a.name;out.mkdir(exist_ok=True)
 (out/'controller.pid').write_text(str(os.getpid())+'\n')
 rng=random.Random(a.seed);started=time.monotonic();best=10000;best_nonmono=10000;valid=0;errors=[];beam=[];seen=set();hist={}
 base_ops=['balance','rewrite','rewrite -z','refactor','refactor -z','refactor -N 14 -z','resub -K 8 -N 3 -z','resub -K 12 -N 3 -z','resub -K 12 -N 3 -z -l']
 if a.extra_ops:base_ops+=json.loads(Path(a.extra_ops).read_text())
 mappers=['map -a','map','map -a -r']
 if a.mappers:mappers=json.loads(Path(a.mappers).read_text())
 for seed_path in a.seed_netlist:
  seed_path=Path(seed_path);check=translate(seed_path)
  assert check['errors']==0
  signature=hashlib.sha256(json.dumps(check['gates']).encode()).hexdigest()
  beam.append({'blif':seed_path,'size':check['gate_count'],'nots':check['not_count'],'sig':signature});seen.add(signature)
 recipes=[[],['balance'],['balance','rewrite','rewrite -z','balance','refactor -z','rewrite -z','balance'],['resub -K 12 -N 3 -z','balance','refactor -N 14 -z','rewrite -z'],['refactor -N 14 -z','balance','resub -K 12 -N 3 -z -l','rewrite -z']]
 for i in range(a.runs):
  if time.monotonic()-started>=a.seconds or (out/'STOP').exists():break
  run=out/f'run-{i:04d}';run.mkdir(exist_ok=True)
  mode=rng.random()
  if i==0 or mode<0.06:source=dnf_seed(run/'seed.blif',rng)
  elif i==1 or mode<0.12:source=cnf_seed(run/'seed.blif',rng)
  elif i in {2,3} or mode<0.32:source=shannon_seed(run/'seed.blif',rng,1+i%2)
  elif beam and mode<0.65:source=rng.choice(beam)['blif']
  else:source=star_seed(run/'seed.blif',rng,rng.randrange(2),expand=(rng.random()<0.5))
  steps=recipes[i] if i<len(recipes) else [rng.choice(base_ops) for _ in range(rng.randrange(3,24))]
  mapper=rng.choice(mappers)
  dest=run/'mapped.blif'
  commands=['read_library '+str(a.library),'read_blif '+str(source),'strash']+steps+[mapper,'print_stats','write_blif '+str(dest)]
  script='; '.join(commands)
  (run/'script.abc').write_text(script+'\n')
  record={'run':i,'source':str(source),'steps':steps,'mapper':mapper}
  with (run/'stdout-stderr.log').open('w') as f:
   try:p=subprocess.run([a.abc,'-s','-c',script],stdout=f,stderr=subprocess.STDOUT,timeout=a.per_run_seconds,cwd=run);record['exit']=p.returncode
   except subprocess.TimeoutExpired:record['timeout']=True
  if dest.exists():
   try:
    result=translate(dest)
    (run/'candidate.json').write_text(json.dumps(result,indent=2)+'\n')
    record.update({'gates':result['gate_count'],'nots':result['not_count'],'errors':result['errors']})
    if result['errors']:
     errors.append(record);print('INVALID',record,flush=True)
    else:
     valid+=1;size=result['gate_count'];hist[size]=hist.get(size,0)+1
     signature=hashlib.sha256(json.dumps(result['gates']).encode()).hexdigest()
     if signature not in seen:
      seen.add(signature);beam.append({'blif':dest,'size':size,'nots':result['not_count'],'sig':signature})
      floor=min(x['size'] for x in beam)
      pool=sorted((x for x in beam if x['size']<=floor+8),key=lambda x:x['size'])
      keep=pool[:30]+[x for x in pool if x['nots']][:20]
      kept={x['sig'] for x in keep};keep=list({x['sig']:x for x in keep}.values())
      rest=[x for x in pool if x['sig'] not in kept]
      beam=keep+rng.sample(rest,min(80-len(keep),len(rest)))
     if result['not_count'] and size<best_nonmono:
      best_nonmono=size;(out/'BEST_NONMONOTONE.json').write_text(json.dumps(result,indent=2)+'\n')
      print('BEST_NONMONOTONE',size,'NOT',result['not_count'],'run',i,flush=True)
     if size<best:
      best=size;(out/'BEST.json').write_text(json.dumps(result,indent=2)+'\n')
      print('BEST',size,'NOT',result['not_count'],'run',i,'elapsed',round(time.monotonic()-started,2),flush=True)
     if size<=24:
      (out/'FOUND.json').write_text(json.dumps(result,indent=2)+'\n')
      print('FOUND',str(out/'FOUND.json'),flush=True)
      (run/'result.json').write_text(json.dumps(record,indent=2)+'\n');break
   except Exception as e:
    record['parse_error']=str(e);errors.append(record);print('PARSE_ERROR',record,flush=True)
  else:
   record['no_output']=True;errors.append(record)
  (run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
  if not record.get('timeout') and (record.get('exit',0)!=0 or record.get('no_output') or record.get('parse_error') or record.get('errors',0)):
   print('STOP_ON_RUN_FAILURE',record,flush=True);break
  if i%20==0:print('PROGRESS',i,'best',best,'valid',valid,'unique',len(seen),'elapsed',round(time.monotonic()-started,2),flush=True)
 summary={'best':best,'best_nonmonotone':best_nonmono,'valid':valid,'unique':len(seen),'histogram':hist,'errors':errors,'elapsed_seconds':time.monotonic()-started,'seed':a.seed}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
