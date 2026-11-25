from pathlib import Path
import json,re,hashlib,sympy as s
from fractions import Fraction
job=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas');data=json.loads((job/'geometry-exceptional-horner-identities.json').read_text());target=repo/'ExceptionalRawReductionHorner.lean';src=target.read_text();ns=data['variables'];vs=s.symbols(' '.join(ns));z=(0,)*len(vs)
def add(a,b):
 c=a.copy()
 for m,v in b.items():c[m]=c.get(m,0)+v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   g=tuple(r+t for r,t in zip(m,n));c[g]=c.get(g,0)+v*w
 return {k:v for k,v in c.items() if v}
def parse(text):
 text=re.sub(r'\((-?\d+)/(\d+):ℂ\)',r'\1/\2',text);ts=re.findall(r'ea|em|ep|b[0-5]|r|-?\d+(?:/\d+)?|[()]',text);assert ''.join(ts)==re.sub(r'\s+','',text);it=iter(ts)
 def rec(t):
  if t in ns:return {tuple(int(n==t) for n in ns):1}
  if t!='(':return {z:Fraction(t)} if Fraction(t) else {}
  op=next(it)
  if op in ['ea','em','ep']:
   a=rec(next(it));b=rec(next(it))
   if op=='ea':c=add(a,b)
   elif op=='em':c=mul(a,b)
   else:
    c={z:1}
    for _ in range(int(b[z])):c=mul(c,a)
  else:c=rec(op)
  assert next(it)==')';return c
 f=rec(next(it));assert list(it)==[];return f
def poly(src):return s.Poly(s.sympify(src),*vs).as_dict()
defs={m.group(1):parse(m.group(2)) for m in re.finditer(r'^noncomputable def (\w+) [^\n]* := (.*)$',src,re.M)}
fe=[2,3,5,6,7]
for i,ident in enumerate(data['identities']):
 tag=ident['branch'];j=ident['index'];seg=src.split('lemma '+tag+'_direct'+str(j)+' ',1)[1].split('set_option',1)[0];q=parse(re.search(r'\(hQ : (.*?)=0\)',seg)[1]);hyps=[defs['raw'+str(fe[j])],*[defs[tag+'G'+str(n)] for n in range(3)],q];lhs=defs[tag+str(j)];assert lhs==poly(ident['target']) and hyps==[poly(h) for h in ident['polynomials']]
 line=re.search(r'    linear_combination (.*)',seg)[1];stm=line.split(' + ');ws=[parse(item.rsplit('*',1)[0]) for item in stm];assert [v.rsplit('*',1)[1] for v in stm]==['he','hG0','hG1','hG2','hQ'];assert ws==[poly(w) for w in ident['multipliers']];D=int(re.search(r'have hh : \((\d+):ℂ\)',seg)[1]);assert D==ident['multiplier'];rhs={}
 for w,g in zip(ws,hyps):rhs=add(rhs,mul(w,g))
 assert rhs==mul({z:D},lhs)
print('PASS ten actual Lean direct identities; primitive raw, branch, pivot, quartic hypotheses and all fifty multipliers match JSON exactly; exact equality in Q[b0,...,b5,r]. Source SHA256',hashlib.sha256(target.read_bytes()).hexdigest(),'JSON SHA256',hashlib.sha256((job/'geometry-exceptional-horner-identities.json').read_bytes()).hexdigest())
