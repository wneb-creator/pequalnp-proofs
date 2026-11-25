from pathlib import Path
import json,hashlib
q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search');p=Path('/tmp/oec/pequalnp-pilot-70/constructive')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def expected(m):
 n=m['ninputs'];g=m['structure'];ans=[]
 for i in range(len(g)-1):ans.append([s[n+i] for later in g[i+1:] for s in [later['left'],later['right']]])
 count=len(ans)
 branches=list(zip(m['variant_selectors'],[v['data'] for v in m['variants']])) if 'variant_selectors' in m else [(None,m['correlated'])]
 essentials=[]
 for selector,d in branches:
  r=d['real_inputs'];supports=[[i] for i in range(r)]+d.get('free_or_supports',d.get('free_or_sums'));edges=d['edges'];essential=sorted({v for e in edges for v in e})
  for v in essential:
   other=next(b if a==v else a for a,b in edges if v in (a,b));mask=1<<other
   assert not any(mask>>a&1 and mask>>b&1 for a,b in edges)
   mask|=1<<v;assert any(mask>>a&1 and mask>>b&1 for a,b in edges)
   inputs=[j for j,s in enumerate(supports) if v in s];ans.append(([] if selector is None else [-selector])+[fanin[j] for gate in g for fanin in [gate['left'],gate['right']] for j in inputs])
  essentials.append({'selector':selector,'essential_variables':essential})
 return ans,count,essentials
def checkmodel(m,log,clauses):
 a={abs(int(v)):int(v)>0 for line in log.read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)};assert len(a)==m['nv']
 assert all(any(a[abs(v)]==(v>0) for v in c) for c in clauses)
 return len(clauses)
def cnf(path):
 lines=path.read_text().splitlines();return lines,[list(map(int,l.split()[:-1])) for l in lines[1:]]
reports=[]
for stem,basedir in [('joint-ten10',p),('joint-noncollinear14',p),('matching-cut14-pairs',q)]:
 old=json.loads((basedir/(stem+'.map.json')).read_text());new=json.loads((q/(stem+'-live.map.json')).read_text());lines,bc=cnf(basedir/(stem+'.cnf'));nl,nc=cnf(q/(stem+'-live.cnf'));delta,gcount,ess=expected(old)
 assert nc==bc+delta and nl[1:len(lines)]==lines[1:]
 assert new['nv']==old['nv'] and new['clauses']==old['clauses']+len(delta)
 assert new['gate_liveness']=={'computed_only':True,'clauses':gcount}
 assert new['support_coverage']['clauses']==len(delta)-gcount and new['support_coverage']['branches']==ess
 assert new['support_coverage']['base_sha256']==sha(basedir/(stem+'.cnf')) and new['support_coverage']['source_sha256']==sha(q/'add_correlated_liveness.py')
 exceptions=['clauses','gate_liveness','support_coverage']
 if 'variant_selectors' in old:
  exceptions+=['cnf_file','cnf_sha256'];assert new['cnf_file']==str((q/(stem+'-live.cnf')).resolve()) and new['cnf_sha256']==sha(q/(stem+'-live.cnf'))
 assert {k:v for k,v in new.items() if k not in exceptions}=={k:v for k,v in old.items() if k not in exceptions}
 reports.append({'file':stem+'-live','gate_clauses':gcount,'coverage_clauses':len(delta)-gcount,'variables':new['nv'],'clauses':new['clauses'],'sha256':sha(q/(stem+'-live.cnf'))})
models=[]
for family,n in [('ten',6),('noncollinear',7)]:
 stem='joint-'+family+('11' if family=='ten' else '15')+'-smoke-v1'
 for branch in range(n):
  name=stem+f'-branch-{branch}';m=json.loads((p/(name+'.map.json')).read_text());_,bc=cnf(p/(name+'.cnf'));delta,_,_=expected(m)
  count=checkmodel(m,p/(name+'.solve.log'),bc+delta);models.append({'name':name,'verified_clauses':count})
name='matching-cut15-pairs-smoke';m=json.loads((q/(name+'.map.json')).read_text());_,bc=cnf(q/(name+'.cnf'));delta,_,_=expected(m);count=checkmodel(m,q/(name+'-solve.log'),bc+delta);models.append({'name':name,'verified_clauses':count})
report={'status':'PASS','source_sha256':sha(q/'add_correlated_liveness.py'),'production_outputs':reports,'models':models,'scope':'Gate-only liveness and target-essential underlying support coverage; no requirement to consume every initial signal.'}
Path('correlated-liveness-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
