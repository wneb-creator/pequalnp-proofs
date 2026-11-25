from pathlib import Path
import importlib.util,json,itertools,collections
job=Path('/tmp/oec/pequalnp-pilot-79');spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,_,polys=ng.parse_input(job/'fresh_top_allzero_0.msolve');meta=json.loads((job/'root-allzero-d8-metadata.json').read_text());im=json.loads((job/'root-allzero-d8-invariant-metadata.json').read_text());cert=json.loads((job/'root-allzero-d8-invariant-exact-certificate.json').read_text());pairs=[(0,1),(0,2),(1,2)]
def action(m,p):
 out=[0]*7;sign=1;out[-1]=m[-1]
 for i in range(3):out[p[i]]=m[i]
 for k,(i,j) in enumerate(pairs):
  ii,jj=p[i],p[j]
  if ii>jj:ii,jj=jj,ii;sign*=(-1)**m[k+3]
  out[3+pairs.index((ii,jj))]=m[k+3]
 return tuple(out),sign
def act(poly,p):
 out=collections.defaultdict(int)
 for m,c in poly.items():
  n,s=action(m,p);out[n]+=s*c
 return {m:c for m,c in out.items() if c}
def add(*ps):
 out=collections.defaultdict(int)
 for p in ps:
  for m,c in p.items():out[m]+=c
 return {m:c for m,c in out.items() if c}
def divroot(poly):
 rem=dict(poly);q=collections.defaultdict(int)
 for m in sorted(rem,key=lambda e:e[-1],reverse=True):
  if m not in rem:continue
  c=rem[m]
  if m[-1]<2:continue
  e=m[:-1]+(m[-1]-2,);q[e]+=c;rem[m]-=c;rem[e]=rem.get(e,0)+24*c
 # Repeat because newly created lower terms may not have appeared originally.
 while any(m[-1]>=2 and c for m,c in rem.items()):
  m=max((m for m,c in rem.items() if c),key=lambda e:e[-1]);c=rem[m];e=m[:-1]+(m[-1]-2,);q[e]+=c;rem[m]-=c;rem[e]=rem.get(e,0)+24*c
 return {m:c for m,c in q.items() if c},{m:c for m,c in rem.items() if c}
mult=[collections.defaultdict(int) for p in polys]
for j,w in enumerate(cert['coefficients']):
 if w:
  i,m=meta['row_origins'][im['source_rows'][j]];mult[i][tuple(m)]+=w
full=collections.defaultdict(int)
for p,mul in zip(polys,mult):
 for m,c in mul.items():
  for e,d in p.items():full[tuple(a+b for a,b in zip(m,e))]+=c*int(d)
full={m:c for m,c in full.items() if c};q,red=divroot(full)
print('F',sum(len(m) for m in mult),'full',len(full),'reduced',len(red),'root_quotient',len(q),flush=True)
for tau in [(1,0,2),(0,2,1),(2,1,0)]:
 g=add(red,act(red,tau));print('tau',tau,'Gterms',len(g),'distinct_abs_coeffs',len(set(abs(c) for c in g.values())),flush=True)
 # Three cyclic conjugates of G must sum to the certificate denominator.
 summ=add(g,act(g,(1,2,0)),act(g,(2,0,1)));assert summ=={(0,)*7:cert['denominator']}
out={'variables':names,'denominator':cert['denominator'],'multipliers':[[[list(m),c] for m,c in p.items() if c] for p in mult],'F':[[list(m),c] for m,c in red.items()],'root_quotient':[[list(m),c] for m,c in q.items()]}
(job/'root-allzero-split-model.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
