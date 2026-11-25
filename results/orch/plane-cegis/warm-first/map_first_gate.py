import argparse,itertools,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--data',required=True);ap.add_argument('--gates',required=True);ap.add_argument('--pair',nargs=2,type=int,required=True);ap.add_argument('--output',required=True);ap.add_argument('--record',required=True);a=ap.parse_args()
d=json.loads(Path(a.data).read_text());g=json.loads(Path(a.gates).read_text());n=d['n'];assert n==26
pair=a.pair;assert len(set(pair))==2 and all(0<=v<26 for v in pair)
assert (pair[0]<13)==(pair[1]<13)
assert any(op==1 and set((u,v))==set(pair) for op,u,v in g)
D={0,1,3,9}
def norm(v):
 v=tuple(x%3 for x in v);z=next(x for x in v if x);return tuple(x*(1 if z==1 else 2)%3 for x in v)
v=(1,0,0);pts=[]
for i in range(13):pts.append(norm(v));v=(v[2],(v[0]+v[2])%3,v[1])
lines=[frozenset((l+x)%13 for x in D) for l in range(13)]
def det(m):return (m[0]*(m[4]*m[8]-m[5]*m[7])-m[1]*(m[3]*m[8]-m[5]*m[6])+m[2]*(m[3]*m[7]-m[4]*m[6]))%3
permutation=None
for matrix in itertools.product(range(3),repeat=9):
 if next((x for x in matrix if x),0)!=1 or not det(matrix):continue
 pp=tuple(pts.index(norm(tuple(sum(matrix[3*r+k]*v[k] for k in range(3)) for r in range(3)))) for v in pts)
 ll=tuple(lines.index(frozenset(pp[p] for p in L)) for L in lines)
 plus=pp+tuple(13+(-ll[(-l)%13])%13 for l in range(13))
 if pair[0]>=13:plus=tuple(x+13 if x<13 else x-13 for x in plus)
 if [plus[x] for x in pair]==[0,1]:permutation=plus;break
assert permutation is not None and set(permutation)==set(range(26))
E={tuple(sorted(e)) for e in d['edges']}
assert {tuple(sorted((permutation[u],permutation[v]))) for u,v in E}==E
def act(row):return sum(1<<permutation[i] for i in range(26) if row&(1<<i))
assert {act(r) for r in d['rows']}==set(d['rows'])
out=[]
for op,u,v in g:
 u=permutation[u] if u<26 else u;v=permutation[v] if v<26 else v;u,v=sorted((u,v));out.append([op,u,v])
def evaluate(gs,row):
 vals=[bool(row&(1<<i)) for i in range(26)]
 for op,u,v in gs:vals.append(vals[u] or vals[v] if op else vals[u] and vals[v])
 return vals[-1]
assert all(evaluate(g,r)==evaluate(out,act(r)) for r in d['rows'])
Path(a.output).write_text(json.dumps(out)+'\n')
Path(a.record).write_text(json.dumps({'matrix':matrix,'selected_pair':pair,'permutation':permutation,'dual_used':pair[0]>=13,'edges_preserved':len(E),'rows_preserved':len(d['rows']),'gates':len(g)},indent=2)+'\n')
