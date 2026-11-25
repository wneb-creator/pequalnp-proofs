from pathlib import Path
import json,hashlib
p=Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis');mapping=json.loads((p/'nested-near63-map.json').read_text());perm=mapping['permutation'];raw=json.loads((p/'nested-near63-gates-raw.json').read_text());g=json.loads((p/'nested-near63-gates.json').read_text());edges={(i,13+l) for i in range(13) for l in range(13) if (i+l)%13 in {0,1,3,9}};es={tuple(sorted(e)) for e in edges};assert sorted(perm)==list(range(26)) and {tuple(sorted((perm[u],perm[v]))) for u,v in edges}==es
positives={(1<<u)|(1<<v) for u,v in edges};negatives=set()
for s in range(8192):
 t=sum(1<<l for l in range(13) if all(not(s>>i&1) or (i+l)%13 not in {0,1,3,9} for i in range(13)));closed=sum(1<<i for i in range(13) if all(not(t>>l&1) or (i+l)%13 not in {0,1,3,9} for l in range(13)))
 if closed==s:negatives.add(s|(t<<13))
rows=sorted(positives|negatives);assert len(rows)==756
def evaluate(gs,r):
 vs=[bool(r>>i&1) for i in range(26)]
 for j,(op,u,v) in enumerate(gs):assert op in (0,1) and 0<=u<26+j and 0<=v<26+j;vs.append(vs[u] or vs[v] if op else vs[u] and vs[v])
 return vs
for r in rows:
 tr=sum(1<<perm[i] for i in range(26) if r>>i&1);assert tr in rows and evaluate(raw,r)[-1]==evaluate(g,tr)[-1]
vs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
for op,u,v in g:vs.append(vs[u]|vs[v] if op else vs[u]&vs[v])
pm=sum((r in positives)<<k for k,r in enumerate(rows));nm=((1<<len(rows))-1)^pm;clean=[not(x&nm) for x in vs];dirty=[26+j for j,(op,u,v) in enumerate(g) if not op and not clean[26+j]];single=[(26+j,i) for i in range(26) for j,(op,u,v) in enumerate(g) if not op and evaluate(g,1<<i)[26+j]];errors=[]
for j,(op,u,v) in enumerate(g):
 w=26+j;readers=[k for k,(_,a,b) in enumerate(g) if k>j and w in (a,b)]
 if j<len(g)-1 and not readers:errors.append(['dead',j])
 if clean[w] and len(readers)>1:errors.append(['clean_fanout',j])
 if any(clean[w] and (g[k][0]==0 or not clean[26+k]) for k in readers):errors.append(['clean_reader',j])
 if not vs[w]&pm:errors.append(['zero_positive',j])
 for i in range(26):
  if not(vs[w]&pm&~vs[i]) and not(vs[i]&nm&~vs[w]):errors.append(['primary_dominance',j,i])
 if j+1<len(g):
  q,a,b=g[j+1]
  if w not in (a,b) and (u,v,op)>(a,b,q):errors.append(['lex',j])
miss=[r for k,r in enumerate(rows) if r in positives and not(vs[-1]>>k&1)];fp=[r for k,r in enumerate(rows) if r in negatives and vs[-1]>>k&1]
assert g[0]==[1,0,1] and len(g)==63 and len(dirty)==2 and not single and len(miss)==6 and not fp and not errors
r={'scope':'Complementary incomplete nested63 phase preparation only; no witness or phase substitution yet','canonical_sha256':hashlib.sha256((p/'nested-near63-gates.json').read_bytes()).hexdigest(),'input_permutation_edge_and_row_action_verified':True,'raw_and_canonical_output_match_under_permutation':True,'regenerated_boundary_rows':len(rows),'size':len(g),'ANDs':sum(not op for op,u,v in g),'dirty_AND_wires':dirty,'singleton_accepting_ANDs':single,'missing_positive_rows':miss,'false_positives':fp,'normalization_violations':errors,'verdict':'APPROVED semantics'}
q=Path('/tmp/oec/pequalnp-pilot-121/nested63-phase-semantics-independent-review.json');q.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
