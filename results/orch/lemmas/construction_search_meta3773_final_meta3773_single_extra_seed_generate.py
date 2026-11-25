from pathlib import Path
import json
j=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};p=0;lbad=2;pencil=[l for l in range(13)if(p+l)%13 in D];badN=[x for x in range(13)if(x+lbad)%13 in D];g=[];outs=[];shared=[]
def add(op,a,b):
 w=26+len(g);g.append([op,a,b]);return w
def OR(w):
 u=w[0]
 for v in w[1:]:u=add(1,u,v)
 return u
for l in pencil:
 N=[x for x in range(13)if(x+l)%13 in D];q=next(x for x in N if x in badN);pair=add(1,p,q);shared.append(pair);other=OR([x for x in N if x not in[p,q]]);Nwire=add(1,pair,other);outs.append(add(0,13+l,Nwire))
outs.append(add(0,13+lbad,OR(shared)))
for l in range(13):
 if l in pencil or l==lbad:continue
 N=OR([x for x in range(13)if(x+l)%13 in D]);outs.append(add(0,13+l,N))
out=OR(outs);assert len(g)==64 and out==89 and g[0]==[1,0,1]
terms=[{1<<i}for i in range(26)]
for op,a,b in g:
 t=terms[a]|terms[b]if op else{x|y for x in terms[a]for y in terms[b]}
 t={x for x in t if not any(x!=y and x&y==y for y in t)};assert len(t)<1000;terms.append(t)
expected={(1<<x)|(1<<(13+l))for x in range(13)for l in range(13)if(x+l)%13 in D};expected.add((1<<p)|(1<<(13+lbad)));assert terms[out]==expected
obj={'source':'CAS-verified graph function plus one extra edge; invalid for target','input_count':26,'active':64,'output':out,'gates':g,'extra_edge':[p,lbad]}
(j/'meta3773-single-extra-edge64.json').write_text(json.dumps(obj,indent=2)+'\n');(j/'meta3773-warm-single-extra-edge64.txt').write_text(str(len(g))+'\n'+'\n'.join(' '.join(map(str,x))for x in g)+'\n');print(json.dumps({'gates':64,'exact_minimal_monomials':len(expected),'extra_edge':[p,lbad],'statement':'output equals target OR(p0 ANDl2), independently checked by exact minimal-monomial propagation'}))
