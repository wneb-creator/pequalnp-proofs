from pathlib import Path
import argparse,hashlib,json,resource,struct,subprocess,time
import sympy as S
ROOT=Path('/tmp/oec/pequalnp-pilot-78');OUT=ROOT/'construct_search/net_normal_form';SOURCE=ROOT/'geometry_search/tracezero/charts-manifest.json';MOD=1000000007

def monomials(n,degree):
 out=[]
 def exact(k,left,prefix):
  if k==1:out.append(tuple(prefix+[left]));return
  for e in range(left+1):exact(k-1,left-e,prefix+[e])
 for total in range(degree+1):exact(n,total,[])
 return out

def build(chart,degree):
 payload=json.loads(SOURCE.read_text());assert payload['status']=='PASS';data=next(c for c in payload['charts'] if c['name']==chart);assert len(data['variables'])==10
 variables=S.symbols(' '.join(data['variables']));env=dict(zip(data['variables'],variables));generators=[S.Poly(S.sympify(g,locals=env),*variables) for g in data['generators']]
 columns=monomials(10,degree);index={m:i for i,m in enumerate(columns)};mults={d:monomials(10,degree-d) for d in set(g.total_degree() for g in generators)}
 rows=sum(len(mults[g.total_degree()]) for g in generators);nnz=sum(len(mults[g.total_degree()])*len(g.terms()) for g in generators);stem=f'{chart}-D{degree}';matrix=OUT/(stem+'.bin')
 with matrix.open('wb') as out:
  out.write(struct.pack('<IIQ',rows,len(columns),nnz));row=0
  for gi,g in enumerate(generators):
   for mult in mults[g.total_degree()]:
    entries=[]
    for mon,coef in g.terms():entries.append((index[tuple(a+b for a,b in zip(mon,mult))],int(coef)))
    for col,value in sorted(entries):out.write(struct.pack('<IIq',row,col,value))
    row+=1
 assert row==rows
 (OUT/(stem+'-degrees.bin')).write_bytes(b''.join(struct.pack('<I',sum(m)) for m in columns))
 opposite=-1-variables[3]-variables[5]-variables[7]-variables[9] if chart=='rank1-incident' else variables[7]
 targets=[]
 triangle1=variables[3]*variables[7] if chart=='rank1-incident' else variables[3]*variables[5]
 triangle2=variables[5]*variables[9] if chart=='rank1-incident' else variables[9]*(-1-variables[3]-variables[5]-variables[7]-variables[9])
 for name,expression,powers in [('opposite_edge',opposite,range(1,5)),('triangle1',triangle1,range(1,3)),('triangle2',triangle2,range(1,3))]:
  for power in powers:
   poly=S.Poly(expression**power,*variables);targets.append({'name':name,'power':power,'terms':[[index[mon],int(coef)] for mon,coef in poly.terms()]})
 meta={'chart':chart,'degree':degree,'modulus':MOD,'rows':rows,'columns':columns,'column_count':len(columns),'nnz':nnz,'matrix_bytes':matrix.stat().st_size,'matrix_sha256':hashlib.sha256(matrix.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'targets':targets,'generators':[str(g.as_expr()) for g in generators]}
 (OUT/(stem+'-metadata.json')).write_text(json.dumps(meta,separators=(',',':'))+'\n');print(json.dumps({k:meta[k] for k in ['chart','degree','rows','column_count','nnz','matrix_bytes','matrix_sha256']}),flush=True)

def run(chart,degree):
 stem=f'{chart}-D{degree}';meta=json.loads((OUT/(stem+'-metadata.json')).read_text());assert hashlib.sha256((OUT/(stem+'.bin')).read_bytes()).hexdigest()==meta['matrix_sha256']
 def limits():
  resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,123));resource.setrlimit(resource.RLIMIT_FSIZE,(4*2**20,4*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (OUT/(stem+'.stdout')).open('w') as out,(OUT/(stem+'.stderr')).open('w') as err:
  try:
   proc=subprocess.run([str(ROOT/'numeric/s4-structure/graded-sparse'),str(OUT/(stem+'.bin')),str(OUT/(stem+'-degrees.bin')),str(OUT/(stem+'-echelon.jsonl'))],stdin=subprocess.DEVNULL,stdout=out,stderr=err,preexec_fn=limits,timeout=140);code=proc.returncode
  except subprocess.TimeoutExpired:code='timeout'
 after=resource.getrusage(resource.RUSAGE_CHILDREN);result={'chart':chart,'degree':degree,'exit':code,'wall_seconds':time.monotonic()-start,'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'max_rss_kib':after.ru_maxrss}
 (OUT/(stem+'-run.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
 if code==0:reduce_targets(chart,degree)

def reduce_targets(chart,degree):
 stem=f'{chart}-D{degree}';meta=json.loads((OUT/(stem+'-metadata.json')).read_text());columns=meta['columns'];order=sorted(range(len(columns)),key=lambda i:(-sum(columns[i]),i));position={i:j for j,i in enumerate(order)}
 pivots={}
 for line in (OUT/(stem+'-echelon.jsonl')).read_text().splitlines():
  item=json.loads(line);terms={int(c):int(v) for c,v in item['terms']};lead=min(terms,key=position.__getitem__);assert terms[lead]==1 and sum(columns[lead])<=4;pivots[lead]=terms
 reports=[]
 for target in meta['targets']:
  row={c:v%MOD for c,v in target['terms'] if v%MOD};steps=0;missing=None
  while row:
   col=min(row,key=position.__getitem__)
   if col not in pivots:missing=col;break
   factor=row[col]
   for c,v in pivots[col].items():
    value=(row.get(c,0)-factor*v)%MOD
    if value:row[c]=value
    elif c in row:del row[c]
   steps+=1
  reports.append({'name':target['name'],'power':target['power'],'in_degree_bounded_span':not row,'reduction_steps':steps,'residual_terms':len(row),'first_unspanned_monomial':None if missing is None else columns[missing]})
 column_index={tuple(mon):i for i,mon in enumerate(columns)};variables=S.symbols('x0:10');env={str(x):x for x in variables}
 for generator in meta['generators']:
  row={column_index[mon]:int(coef)%MOD for mon,coef in S.Poly(S.sympify(generator,locals=env),*variables).terms() if int(coef)%MOD}
  while row:
   col=min(row,key=position.__getitem__);assert col in pivots,'Original generator failed span control';factor=row[col]
   for c,v in pivots[col].items():
    value=(row.get(c,0)-factor*v)%MOD
    if value:row[c]=value
    elif c in row:del row[c]
 report={'chart':chart,'degree':degree,'modulus':MOD,'targets':reports,'original_generator_controls':'PASS','generator_control_count':len(meta['generators']),'scope':'Modular degree-bounded ideal-membership test only; negative results imply no global nonmembership or geometric conclusion.'}
 (OUT/(stem+'-targets.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['build','run','reduce']);parser.add_argument('chart',choices=['rank1-incident','rank1-disjoint']);parser.add_argument('degree',type=int);a=parser.parse_args();{'build':build,'run':run,'reduce':reduce_targets}[a.mode](a.chart,a.degree)
