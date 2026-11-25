from pathlib import Path
import json,sys,hashlib,itertools
p=Path(sys.argv[1]);d=json.loads(p.read_text());g=d['gates'];out=d['output'];assert d['input_count']==26 and len(g)==d['active'];assert type(out)is int and 0<=out<26+len(g)
assert g[0]in[[1,0,1],[0,0,13],[1,0,13],[1,2,13]]
terms=[{1<<i}for i in range(26)]
for i,(op,a,b)in enumerate(g):
 assert type(op)is int and op in(0,1)and type(a)is int and type(b)is int and 0<=a<26+i and 0<=b<26+i
 t=terms[a]|terms[b]if op else{x|y for x in terms[a]for y in terms[b]}
 assert len(t)<=10000
 t={x for x in t if not any(x!=y and x&y==y for y in t)};terms.append(t)
D={0,1,3,9};base={(1<<p)|(1<<(13+l))for p in range(13)for l in range(13)if(p+l)%13 in D};extra=terms[out]-base;missing=base-terms[out]
def ev(mask):
 w=[bool(mask>>i&1)for i in range(26)]
 for op,a,b in g:w.append((w[a]or w[b])if op else(w[a]and w[b]))
 return w[out]
examples=[]
for pnt in range(13):
 right=[l for l in range(13)if(pnt+l)%13 not in D];mask=(1<<pnt)|sum(1<<(13+l)for l in right)
 if ev(mask):examples.append({'posted_negative_left_S':[pnt],'right_common_nonneighbors':right,'input_mask':mask,'candidate_result':True,'required_result':False})
obj={'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'gates':len(g),'minimal_monomials':len(terms[out]),'missing_monomials':[[i for i in range(26)if m>>i&1]for m in sorted(missing)],'extra_monomials':[[i for i in range(26)if m>>i&1]for m in sorted(extra)],'posted_counterexamples':examples,'valid_target':len(g)<=63 and not extra and not missing,'scope':'Exact finite minimal-monomial CAS audit; not a Lean proof'}
print(json.dumps(obj,indent=2))
