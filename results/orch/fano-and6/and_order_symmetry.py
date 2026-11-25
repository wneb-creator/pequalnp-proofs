import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument("metadata");p.add_argument("cnf");p.add_argument("output");a=p.parse_args()
d=json.loads(Path(a.metadata).read_text());rows=Path(a.cnf).read_text().splitlines();nv,nc=map(int,rows[0].split()[2:]);extra=[]
def new():
 global nv
 nv+=1
 return nv
def add(*xs):extra.append(" ".join(map(str,xs))+" 0")
for j in range(1,d["k"]):
 old=d["selectors"][j-1];cur=d["selectors"][j]
 guard=[cur[0][-1],cur[1][-1]]
 xs=old[0]+old[1];ys=cur[0][:-1]+cur[1][:-1]
 pref=new();add(pref)
 for x,y in zip(xs,ys):
  add(*guard,-pref,-x,y)
  nex=new();add(-nex,pref);add(-nex,-x,y);add(-nex,x,-y);add(-pref,x,y,nex);add(-pref,-x,-y,nex);pref=nex
Path(a.output).write_text(f"p cnf {nv} {nc+len(extra)}\n"+"\n".join(rows[1:]+extra)+"\n")
print("ordered variables",nv,"clauses",nc+len(extra),"new clauses",len(extra))
