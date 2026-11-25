import argparse,math,json
from fractions import Fraction
from functools import reduce
from pathlib import Path

def emit_horner(terms,names):
 assert all(Fraction(c).denominator==1 for c,e in terms)
 terms={tuple(e):int(c) for c,e in terms if c}
 def rec(d):
  if not d:return '0'
  if len(d)==1:
   e,c=next(iter(d.items()));fs=[]
   if c!=1 or not any(e):fs.append(str(c) if c>=0 else '('+str(c)+')')
   fs += [names[i] if k==1 else names[i]+' ^ '+str(k) for i,k in enumerate(e) if k]
   return ' * '.join(fs)
  # Factor the common monomial before the next Horner split.
  mins=tuple(min(e[i] for e in d) for i in range(len(names)))
  if any(mins):
   q={tuple(x-y for x,y in zip(e,mins)):v for e,v in d.items()}
   fs=[names[i] if k==1 else names[i]+' ^ '+str(k) for i,k in enumerate(mins) if k]
   return ' * '.join(fs)+' * ('+rec(q)+')'
  candidates=[i for i in range(len(names)) if any(e[i] for e in d)]
  i=max(candidates,key=lambda i:(sum(bool(e[i]) for e in d),-max(e[i] for e in d),-i))
  groups={}
  for e,c in d.items():
   k=e[i];f=list(e);f[i]=0;groups.setdefault(k,{})[tuple(f)]=c
  degrees=sorted(groups,reverse=True);last=degrees[0];out=rec(groups[last])
  for k in degrees[1:]:
   power=last-k;fac=names[i] if power==1 else names[i]+' ^ '+str(power)
   out='('+out+') * '+fac+' + ('+rec(groups[k])+')';last=k
  if last:
   fac=names[i] if last==1 else names[i]+' ^ '+str(last)
   out='('+out+') * '+fac
  return out
 return rec(terms)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('conventions');ap.add_argument('certificate');ap.add_argument('output');a=ap.parse_args()
 j=json.loads(Path(a.conventions).read_text());c=json.loads(Path(a.certificate).read_text());names=j['variable_order'];assert names==c['variable_order']
 cs=[[(Fraction(v),e) for v,e in x['terms']] for x in c['cofactors']];assert len(cs)==13
 den=reduce(math.lcm,(v.denominator for p in cs for v,e in p),1)
 args=' '.join(names);out=['import PEqualNP.Defs','import Mathlib','','namespace PEqualNP.Outside.L_gct_231','','set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','theorem normalized_incident_arithmetic_certificate ('+args+' : ℂ)']
 for k,g in enumerate(j['generators'],1):
  poly=emit_horner([(Fraction(v),e) for v,e in g['terms']],names)
  out.append('    (h'+str(k)+' : '+poly+' = 0)')
 out+=['    : False := by','  have hc : ('+str(den)+' : ℂ) = 0 := by','    linear_combination']
 first=True
 for k,p in enumerate(cs,1):
  if not p:continue
  expression=emit_horner([(v*den,e) for v,e in p],names)
  out.append('      '+('' if first else '+ ')+'('+expression+') * h'+str(k))
  first=False
 out+=['  norm_num at hc','','end PEqualNP.Outside.L_gct_231','']
 Path(a.output).write_text('\n'.join(out))
 print(json.dumps({'output':a.output,'bytes':Path(a.output).stat().st_size,'cleared_denominator_digits':len(str(den)),'scope':'Generated arithmetic theorem; must compile and be independently checked before use.'}))
if __name__=='__main__':main()
