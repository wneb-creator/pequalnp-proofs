from pathlib import Path
from collections import defaultdict
import re,json,hashlib,time,resource,itertools
import sympy as s
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1200*1024**2,1200*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
started=time.monotonic();job=Path('/tmp/oec/pequalnp-pilot-79');source=(job/'TopAllZeroSplit.lean').read_text();names=['a','b','c','l','m','n','h'];zero=(0,)*7
constants={m[1]:int(m[2]) for m in re.finditer(r'^def (k\d+) : ℤ := (-?\d+)$',source,re.M)}
def clean(a):return {m:c for m,c in a.items() if c}
def add(a,b):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+c
 return clean(d)
def mul(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,e in b.items():d[tuple(x+y for x,y in zip(m,n))]+=c*e
 return clean(d)
def power(a,b):
 assert set(b)<={zero};n=b.get(zero,0);assert 0<=n<=30;r={zero:1}
 for _ in range(n):r=mul(r,a)
 return r
def parse(txt):
 tok=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[()+*:^-]|ℂ',txt);assert ''.join(tok)==re.sub(r'\s+','',txt);pos=0
 def atom():
  nonlocal pos
  t=tok[pos];pos+=1
  if t=='(':
   v=expr()
   if tok[pos]==':':pos+=1;assert tok[pos]=='ℂ';pos+=1
   assert tok[pos]==')';pos+=1;return v
  if t=='-':return {m:-c for m,c in atom().items()}
  if t in ('ca','cm','cp'):
   a=atom();b=atom();return {'ca':add,'cm':mul,'cp':power}[t](a,b)
  if t=='cz':
   v=atom();assert set(v)<={zero};return v
  if t in constants:return clean({zero:constants[t]})
  if t in names:return {tuple(int(t==n) for n in names):1}
  return clean({zero:int(t)})
 def expr(minp=0):
  nonlocal pos
  v=atom();prec={'+':1,'-':1,'*':2,'^':3}
  while pos<len(tok) and tok[pos] in prec and prec[tok[pos]]>=minp:
   op=tok[pos];pos+=1;w=expr(prec[op]+(op!='^'))
   if op=='-':w={m:-c for m,c in w.items()}
   v={'+' : add,'-':add,'*':mul,'^':power}[op](v,w)
  return v
 out=expr();assert pos==len(tok);return out
polys={}
for m in re.finditer(r'^def ((?:p|m)\d+|fp|qp) \([^\n]+\n([^\n]+)',source,re.M):polys[m[1]]=parse(m[2].strip())
inputfile=job/'fresh_top_allzero_0.msolve';lines=inputfile.read_text().splitlines();assert lines[:2]==[','.join(names),'0'];vs=s.symbols(' '.join(names));loc=dict(zip(names,vs));orig=[s.Poly(s.sympify(t.replace('^','**'),locals=loc),*vs,domain=s.ZZ).as_dict() for t in ''.join(lines[2:]).split(',') if t]
assert len(orig)==20 and len(constants)==378
assert [polys['p'+str(i)] for i in range(20)]==orig
split=json.loads((job/'root-allzero-split-model.json').read_text())
for key,field in [('fp','F'),('qp','root_quotient')]:assert polys[key]=={tuple(m):c for m,c in split[field]}
identity={}
for i in range(20):
 mi=polys.get('m'+str(i),{});assert mi=={tuple(m):c for m,c in split['multipliers'][i]}
 identity=add(identity,mul(mi,orig[i]))
identity=add(identity,{m:-c for m,c in mul(polys['qp'],orig[0]).items()});assert identity==polys['fp']
pairs=[(0,1),(0,2),(1,2)]
def act(f,p):
 d=defaultdict(int)
 for m,c in f.items():
  n=[0]*7;n[-1]=m[-1];sign=1
  for i in range(3):n[p[i]]=m[i]
  for i,(a,b) in enumerate(pairs):
   a,b=p[a],p[b]
   if a>b:a,b=b,a;sign*=(-1)**m[i+3]
   n[3+pairs.index((a,b))]=m[i+3]
  d[tuple(n)]+=sign*c
 return clean(d)
combined={}
for perm in itertools.permutations(range(3)):
 combined=add(combined,act(polys['fp'],perm))
 for f in orig:assert act(f,perm) in orig
assert combined=={zero:split['denominator']}
assert '_root_' not in source and '\x22' not in source and '@[' not in source
assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|run_cmd|elab|macro)\b',source)
print(json.dumps({'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'original_20_Horner_polynomials_exact':True,'source_multiplier_support':sum(len(polys.get('m'+str(i),{})) for i in range(20)),'source_integer_constants':len(constants),'subcertificate_identity_exact':True,'F_terms':len(polys['fp']),'root_quotient_terms':len(polys['qp']),'S3_sum_identity_exact':True,'S3_preserves_original_equations':True,'constant_bits':split['denominator'].bit_length(),'scope':'exact arithmetic audit of generated Lean source; kernel compilation not asserted','seconds':time.monotonic()-started},indent=2))
