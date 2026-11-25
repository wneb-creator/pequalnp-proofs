import itertools,json
from pathlib import Path
root=Path("/tmp/oec/pequalnp-pilot-157")
d=json.loads((root/"fano-6and-t0.json").read_text());lines=[frozenset(u for u,v in d["edges"] if v==7+j) for j in range(7)];lineids={s:i for i,s in enumerate(lines)}
perms=[]
for perm in itertools.permutations(range(7)):
 images=[frozenset(perm[i] for i in line) for line in lines]
 if all(im in lineids for im in images):perms.append(tuple(perm)+tuple(7+lineids[im] for im in images))
assert len(perms)==168
masks=[i for i in range(1,1<<14) if i<128 or i%128==0]
def key(mask):return tuple((mask>>i)&1 for i in range(14))
def pair(a,b):return (a,b) if key(a)<=key(b) else (b,a)
images={m:[sum(1<<perm[i] for i in range(14) if m>>i&1) for perm in perms] for m in masks}
seen=set();reps=[]
for a in masks:
 for b in masks:
  if pair(a,b) in seen:continue
  orbit={pair(x,y) for x,y in zip(images[a],images[b])}
  seen.update(orbit);reps.append(min(orbit,key=lambda q:key(q[0])+key(q[1])))
assert len(seen)==len(masks)*(len(masks)+1)//2
rows=(root/"fano-6and-t0-ordered.cnf").read_text().splitlines();parts=rows[0].split();nv=int(parts[2]);nc=int(parts[3]);extra=[];choices=[]
for a,b in reps:
 nv+=1;choices.append(nv)
 for side,mask in enumerate([a,b]):
  for i,sel in enumerate(d["selectors"][0][side]):extra.append(f"{-nv} {sel if mask>>i&1 else -sel} 0")
extra.append(" ".join(map(str,choices))+" 0")
(root/"fano-6and-t0-automorphisms.cnf").write_text(f"p cnf {nv} {nc+len(extra)}\n"+"\n".join(rows[1:]+extra)+"\n")
(root/"fano-first-gate-orbits.json").write_text(json.dumps(dict(automorphisms=perms,representatives=reps,configurations=len(seen))))
print("automorphisms",len(perms),"first-gate configurations",len(seen),"orbits",len(reps),"variables",nv,"clauses",nc+len(extra))
