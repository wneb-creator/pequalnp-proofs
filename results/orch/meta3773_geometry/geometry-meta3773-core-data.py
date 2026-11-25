from pathlib import Path
import itertools as it,json,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
D={0,1,3,9};ps=[i for i in range(13)if i!=9];ls=[i for i in range(13)if i!=0]
edges=[(i,12+j)for i,p in enumerate(ps)for j,l in enumerate(ls)if(p+l)%13 in D]
ng=[sum(1<<(j-12)for a,j in edges if a==i)for i in range(12)]
A={0,1,3};B={15,16,18};AM=sum(1<<i for i in A);BM=sum(1<<i for i in B)
def maximal_independent(forbidden=0):
 out=set();lp=((1<<12)-1)&~forbidden;rp=((1<<12)-1)&~(forbidden>>12)
 for x in range(1<<12):
  if x&~lp:continue
  bad=0
  for i in range(12):
   if x>>i&1:bad|=ng[i]
  y=rp&~bad
  if all((x>>i&1)or i not in range(12)or not(lp>>i&1)or(ng[i]&y)for i in range(12)):
   out.add(x|(y<<12))
 return out
negbase=maximal_independent();nega=maximal_independent(AM);negb=maximal_independent(BM)
neg=sorted(negbase|nega|negb|{1<<i for i in A|B})
pos=[(1<<i)|(1<<j)for i,j in edges];rows=pos+neg
N=len(rows);words=(N+63)//64
inputs=[[sum(1<<(k%64)for k,m in enumerate(rows)if k//64==w and m>>i&1)for w in range(words)]for i in range(24)]
care=[];truth=[]
for out in range(3):
 care.append([sum(1<<(k%64)for k in range(N)if k//64==w and(out==0 or k>=len(pos)))for w in range(words)])
 truth.append([sum(1<<(k%64)for k,m in enumerate(rows)if k//64==w and((out==0 and k<len(pos))or(out==1 and k>=len(pos)and m&AM)or(out==2 and k>=len(pos)and m&BM)))for w in range(words)])
gates=[['or',0,1],['or',24,3]];aout=25;outs=[]
for i in range(12):
 adj=[j for a,j in edges if a==i];w=adj[0]
 for j in adj[1:]:gates.append(['or',w,j]);w=24+len(gates)-1
 gates.append(['and',i,w]);w=24+len(gates)-1;outs.append(w)
fout=outs[0]
for w in outs[1:]:gates.append(['or',fout,w]);fout=24+len(gates)-1
gates.append(['or',15,16]);gates.append(['or',24+len(gates)-1,18]);bout=24+len(gates)-1
assert len(gates)==60
for m in rows:
 vals=[bool(m>>i&1)for i in range(24)]
 for op,i,j in gates:vals.append(vals[i]or vals[j]if op=='or'else vals[i]and vals[j])
 expect=any(m>>i&1 and m>>j&1 for i,j in edges)
 assert vals[fout]==expect
 if not expect:assert vals[aout]==bool(m&AM)and vals[bout]==bool(m&BM)
data={'n':24,'target_active':58,'edges':edges,'rows':rows,'positive_count':len(pos),'negative_maximal_counts':[len(negbase),len(nega),len(negb)],'words':words,'inputs':inputs,'care':care,'truth':truth,'seed':{'gates':gates,'outputs':[fout,aout,bout]}}
Path('geometry-meta3773-core-data.json').write_text(json.dumps(data))
with Path('geometry-meta3773-core-data.txt').open('w')as f:
 f.write(f'24 {N} {words} 3 58\n')
 for row in inputs+care+truth:f.write(' '.join(map(str,row))+'\n')
 f.write(f'{len(gates)}\n')
 for op,i,j in gates:f.write(f'{1 if op=="and" else 0} {i} {j}\n')
 f.write(' '.join(map(str,[fout,aout,bout]))+'\n')
print(json.dumps({'edges':len(edges),'rows':N,'negative_counts':data['negative_maximal_counts'],'seed_gates':len(gates),'outputs':[fout,aout,bout]}))
