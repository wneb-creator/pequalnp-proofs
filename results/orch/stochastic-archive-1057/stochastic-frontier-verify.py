from pathlib import Path
import hashlib,json,subprocess
b=Path('/tmp/oec/pequalnp-pilot-81');tests=list(map(int,(b/'stochastic-tests.txt').read_text().split()))
files=subprocess.check_output(['rg','--files',str(b),'-g','stochastic-branch-biased-frontier-*.json','-g','stochastic-branch-biased-near-*.json','-g','stochastic-branch-biased-best.json','-g','stochastic-diverse-frontier-*.json','-g','stochastic-diverse-exact-*.json','-g','stochastic-diverse-trace-only-*.json','-g','stochastic-diverse-best.json','-g','stochastic-diverse-near-*.json'],text=True).splitlines()
truth=[sum(1<<x for x in range(16384) if x>>i&1) for i in range(14)];want=0
for l in range(7):
 for p in [l,(l+1)%7,(l+3)%7]:want|=truth[p]&truth[7+l]
summary=[]
for fn in files:
 text=Path(fn).read_text();d=json.loads(text);g=d['gates'];v=list(truth)
 for j,(op,a,c) in enumerate(g):
  assert a!=c and 0<=a<14+j and 0<=c<14+j
  v.append(v[a]&v[c] if op=='and' else v[a]|v[c])
 out=d['output'];falsepos=(v[out]&~want).bit_count();falseneg=(want&~v[out]).bit_count();traces=[]
 for bv,dv in [(0,7),(7,0)]:
  vv=[i==bv for i in range(14)];dd=[i==dv for i in range(14)]
  for op,a,c in g:
   dd.append((dd[a] and vv[c]) or (vv[a] and dd[c]) if op=='and' else dd[a] or dd[c]);vv.append(vv[a] and vv[c] if op=='and' else vv[a] or vv[c])
  traces.append([vv[out],dd[out]])
 expected=[i for i,x in enumerate(tests) if bool(v[out]>>x&1)!=(i<21)]
 for j,(bb,dd) in enumerate(traces):
  if bb:expected.append(58+j)
  if dd:expected.append(60+j)
 assert sorted(expected)==d['failed_bits'],(fn,expected,d['failed_bits'])
 summary.append({'source':fn,'sha256':hashlib.sha256(text.encode()).hexdigest(),'gates':len(g),'failed_boundary_bits':expected,'false_positives':falsepos,'false_negatives':falseneg,'bases_derivatives':traces,'full_witness':falsepos==falseneg==0 and all(not a and not c for a,c in traces)})
(b/'stochastic-frontier-verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print('Independently verified',len(summary),'snapshots on full16384rows and directtrace recurrence; actual witnesses=',sum(s['full_witness'] and s['gates']<=27 for s in summary))
