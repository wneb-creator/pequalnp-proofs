from pathlib import Path
from fractions import Fraction
import math,json,sys,argparse
sys.set_int_max_str_digits(0)
a=argparse.ArgumentParser();a.add_argument('input');a.add_argument('output');a.add_argument('prefix');args=a.parse_args()
def read(path):
 tokens=Path(path).read_text().split();pos=0;polys=[]
 for unused in range(2):
  n=int(tokens[pos]);pos+=1;assert 0<n<=10000
  p=[]
  for i in range(n):
   num,den=int(tokens[pos]),int(tokens[pos+1]);pos+=2;assert den!=0;p.append(Fraction(num,den))
  assert p[-1]!=0;polys.append(p)
 assert pos==len(tokens);return polys
f,g=read(args.input);A,B=read(args.output)
result=[Fraction(0)]*max(len(f)+len(A)-1,len(g)+len(B)-1)
for p,q in [(f,A),(g,B)]:
 for i,a in enumerate(p):
  for j,b in enumerate(q):result[i+j]+=a*b
assert result[0]==1 and all(c==0 for c in result[1:])
den=math.lcm(*(c.denominator for c in A+B));AI=[int(c*den) for c in A];BI=[int(c*den) for c in B]
inputs_integral=all(c.denominator==1 for c in f+g)
meta={'status':'PASS_EXACT_FRACTION_MULTIPLICATION','input_degrees':[len(f)-1,len(g)-1],'multiplier_degrees':[len(A)-1,len(B)-1],'scale_digits':len(str(den)),'total_integer_coefficient_digits':sum(len(str(c)) for c in AI+BI),'source_inputs_integral':inputs_integral}
prefix=Path(args.prefix);prefix.with_suffix('.verified.json').write_text(json.dumps(meta,indent=2)+'\n');prefix.with_suffix('.integer-certificate.json').write_text(json.dumps({'first_multiplier':[str(c) for c in AI],'second_multiplier':[str(c) for c in BI],'scale':str(den)},indent=2)+'\n');print(json.dumps(meta),flush=True)
