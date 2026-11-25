from pathlib import Path
import json
j=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};family=[];report=[]
for p,lbad in[(0,2),(0,8),(0,12),(1,1),(1,3),(1,9)]:
 pencil=[l for l in range(13)if(p+l)%13 in D];badN=[x for x in range(13)if(x+lbad)%13 in D];g=[];outs=[];shared=[]
 def add(op,a,b):
  w=26+len(g);g.append([op,a,b]);return w
 def OR(w):
  u=w[0]
  for v in w[1:]:u=add(1,u,v)
  return u
 for l in pencil:
  N=[x for x in range(13)if(x+l)%13 in D];q=next(x for x in N if x in badN);pair=add(1,min(p,q),max(p,q));shared.append(pair);other=OR([x for x in N if x not in[p,q]]);Nwire=add(1,pair,other);outs.append(add(0,13+l,Nwire))
 outs.append(add(0,13+lbad,OR(shared)))
 for l in range(13):
  if l in pencil or l==lbad:continue
  N=OR([x for x in range(13)if(x+l)%13 in D]);outs.append(add(0,13+l,N))
 out=OR(outs);assert len(g)==64 and out==89 and g[0]==[1,0,1]
 terms=[{1<<i}for i in range(26)]
 for op,a,b in g:
  t=terms[a]|terms[b]if op else{x|y for x in terms[a]for y in terms[b]};t={x for x in t if not any(x!=y and x&y==y for y in t)};assert len(t)<1000;terms.append(t)
 expected={(1<<x)|(1<<(13+l))for x in range(13)for l in range(13)if(x+l)%13 in D};expected.add((1<<p)|(1<<(13+lbad)));assert terms[out]==expected
 name=f'meta3773-single-extra64-p{p}-l{lbad}.json';obj={'source':'CAS-verified target plus one extra edge; invalid for target','input_count':26,'active':64,'output':out,'gates':g,'extra_edge':[p,lbad]};(j/name).write_text(json.dumps(obj,indent=2)+'\n');family.append(g);report.append({'file':name,'gates':64,'minterms':len(expected),'extra_edge':[p,lbad]})
text='-6\n'+''.join(str(len(g))+'\n'+'\n'.join(' '.join(map(str,x))for x in g)+'\n'for g in family);(j/'meta3773-warm-single-extra-family.txt').write_text(text);print(json.dumps(report))
