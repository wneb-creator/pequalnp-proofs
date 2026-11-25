from pathlib import Path
import sys,json
src,dst=map(Path,sys.argv[1:3])
n,s=10,18;A=(1<<n)+n+s+2
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
pad=lambda j:p(7,j,0)
with src.open() as f:head=f.readline().split()
assert head[:2]==['p','cnf'];oldvars,oldclauses=map(int,head[2:])
pol=[oldvars+1+j for j in range(s)]
flip=[oldvars+1+s+i for i in range(n+s)]
F=[]
def add(*c):F.append(c)
for j in range(s):
 add(-pad(j),-pol[j]);add(-pad(j),-flip[n+j])
 for sd in [1,2]:
  add(pad(j),-p(sd,j,n+j))
  for k in range(n+j):
   for op in range(4):
    neg=(op==3) if sd==1 else (op==2)
    base=[-p(0,j,op),-p(sd,j,k),flip[k]]
    if k<n:add(*base,pol[j] if neg else -pol[j])
    elif neg:
     add(*base,pol[k-n],pol[j]);add(*base,-pol[k-n],-pol[j])
    else:
     add(*base,-pol[k-n],pol[j]);add(*base,pol[k-n],-pol[j])
add(-pol[-1],flip[-1])
# Forward threshold counter: at most19 charged binary gates/complements.
charged=[-pad(j) for j in range(s)]+flip
nv=oldvars+s+n+s
last={}
for i,lit in enumerate(charged):
 curr={}
 for k in range(1,min(i+1,20)+1):nv+=1;curr[k]=nv
 add(-lit,curr[1])
 for k,v in last.items():
  if k in curr:add(-v,curr[k])
  if k+1 in curr:add(-v,-lit,curr[k+1])
 last=curr
add(-last[20])
with src.open() as fi,dst.open('w') as fo:
 fi.readline();fo.write(f'p cnf {nv} {oldclauses+len(F)}\n')
 for line in fi:fo.write(line)
 for clause in F:fo.write(' '.join(map(str,clause))+' 0\n')
print(json.dumps({'old_variables':oldvars,'variables':nv,'added_clauses':len(F),'bytes':dst.stat().st_size,'polarity_first':pol[0],'flip_first':flip[0]}))
