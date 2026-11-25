import re,json
from pathlib import Path
from blif_validate import translate
base=Path('/tmp/oec/pequalnp-pilot-85/abc-search')
def evaluate_expr(expr,values):
 toks=re.findall(r'[A-Z]|[!*+()]',expr);pos=0
 def atom():
  nonlocal pos
  t=toks[pos];pos+=1
  if t=='!':return not atom()
  if t=='(':
   v=disjunction();assert toks[pos]==')';pos+=1;return v
  return values[t]
 def conjunction():
  nonlocal pos
  v=atom()
  while pos<len(toks) and toks[pos]=='*':pos+=1;w=atom();v=v and w
  return v
 def disjunction():
  nonlocal pos
  v=conjunction()
  while pos<len(toks) and toks[pos]=='+':pos+=1;w=conjunction();v=v or w
  return v
 v=disjunction();assert pos==len(toks);return v
count=0
for line in (base/'expanded.genlib').read_text().splitlines()[6:]:
 m=re.match(r'GATE (\w+) (\d+) Y=([^;]+);',line);assert m
 name,area,expr=m.groups();pins=sorted(set(re.findall('[A-Z]',expr)))
 text='.model macro_test\n.inputs '+' '.join('x'+str(i) for i in range(14))+'\n.outputs f\n.gate '+name+' '+' '.join(pin+'=x'+str(i) for i,pin in enumerate(pins))+' Y=f\n.end\n'
 path=base/'macro-test.blif';path.write_text(text)
 r=translate(path);assert r['gate_count']==int(area),(name,r['gate_count'],area)
 for x in range(1<<len(pins)):
  ws=[bool(x>>i&1) for i in range(14)]
  for op,a,b in r['gates']:
   va=False if a==-1 else ws[a];vb=False if b==-1 else ws[b]
   ws.append(va and vb if op==0 else va or vb if op==1 else not va)
  actual=False if r['output']==-1 else ws[r['output']]
  expected=evaluate_expr(expr,{pin:bool(x>>i&1) for i,pin in enumerate(pins)})
  assert actual==expected,(name,x)
  count+=1
 print(name,'gates',area,'assignments',1<<len(pins))
print('PASS:',count,'macro truth-table rows; all advertised costs equal explicit unit-gate expansions')
