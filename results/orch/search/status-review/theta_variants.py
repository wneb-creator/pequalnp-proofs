import json,itertools
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-65/status-review');out=p/'theta-variants';out.mkdir(exist_ok=True)
vs=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
def evals(gs):
 v=vs[:]
 for op,a,b in gs:v.append(v[a]&v[b] if op=='and' else v[a]|v[b])
 return v[-1]
def dt(gs,b,s):
 v=[i==b for i in range(10)];d=[i==s for i in range(10)]
 for op,a,c in gs:
  d.append((v[a] and d[c]) or (d[a] and v[c]) if op=='and' else d[a] or d[c])
  v.append(v[a] and v[c] if op=='and' else v[a] or v[c])
 return d[-1]
index=[]
for seed in [225,227]:
 d=json.loads((p/f'polarized-{seed}.json').read_text());target=evals(d['gates'])
 for l in range(3):
  for r in range(3):
   g=[x[:] for x in d['gates']];lv=[1,2,4];rv=[6,7,9]
   la=lv[:l]+lv[l+1:];ra=rv[:r]+rv[r+1:]
   g[4]=['or',*la];g[6]=['or',lv[l],14]
   g[5]=['or',*ra];g[7]=['or',rv[r],15]
   assert evals(g)==target
   assert not dt(g,1,7) and not dt(g,7,1)
   dd=dict(d);dd['gates']=g;dd['base_seed']=seed;dd['or_tree_omissions']=[l,r]
   name=f'polarized-{seed}-trees-{l}-{r}.json';(out/name).write_text(json.dumps(dd,indent=2)+'\n');index.append(str(out/name))
(p/'theta-variants-index.json').write_text(json.dumps(index,indent=2)+'\n')
print('saved',len(index),'exact variants',out)
