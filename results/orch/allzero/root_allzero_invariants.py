from pathlib import Path
import json,itertools,collections,sys
job=Path('/tmp/oec/pequalnp-pilot-79');degree=int(sys.argv[1]);base='root-allzero-d'+str(degree)
meta=json.loads((job/(base+'-metadata.json')).read_text());cols=[tuple(x) for x in meta['columns']];origins=[(i,tuple(m)) for i,m in meta['row_origins']];index={m:i for i,m in enumerate(cols)}
perms=list(itertools.permutations(range(3)));pairs=[(0,1),(0,2),(1,2)]
def action(m,p):
 out=[0]*7;sign=1;out[-1]=m[-1]
 for i in range(3):out[p[i]]=m[i]
 for k,(i,j) in enumerate(pairs):
  ii,jj=p[i],p[j]
  if ii>jj:ii,jj=jj,ii;sign*=(-1)**m[k+3]
  out[3+pairs.index((ii,jj))]=m[k+3]
 return tuple(out),sign
canon={};representatives=[]
for m in cols:
 if m in canon:continue
 orbit={}
 for p in perms:
  e,s=action(m,p);orbit.setdefault(e,set()).add(s)
 if any(len(v)>1 for v in orbit.values()):
  for e in orbit:canon[e]=None
 else:
  representative=min(orbit,key=index.get);rs=next(iter(orbit[representative]));j=len(representatives);representatives.append(representative)
  for e,sgns in orbit.items():canon[e]=(j,next(iter(sgns))*rs)
assert representatives[-1]==(0,)*7
with (job/(base+'.matrix')).open() as fp:
 oldcols,oldrows=map(int,next(fp).split());rows=[]
 for line in fp:
  vals=list(map(int,line.split()));rows.append({cols[vals[2*k+1]]:vals[2*k+2] for k in range(vals[0])})
seen=set();newrows=[];neworigins=[]
for source,row in enumerate(rows):
 total=collections.defaultdict(int)
 for p in perms:
  for m,c in row.items():
   e,s=action(m,p);total[e]+=s*c
 total={e:c for e,c in total.items() if c}
 if not total:continue
 # Store only the representative coefficient of this invariant polynomial.
 compressed=tuple(sorted((j,total.get(m,0)) for j,m in enumerate(representatives) if total.get(m,0)))
 # Verify invariance, including signed stabilizers, without assuming it.
 expanded={m:total.get(representatives[js[0]],0)*js[1] for m,js in canon.items() if js is not None}
 assert all(total.get(m,0)==expanded.get(m,0) for m in cols)
 if compressed in seen:continue
 seen.add(compressed);newrows.append(compressed);neworigins.append(source)
newbase=base+'-invariant'
with (job/(newbase+'.matrix')).open('w') as f:
 f.write(f'{len(representatives)} {len(newrows)}\n')
 for row in newrows:f.write(str(len(row))+' '+' '.join(str(j)+' '+str(c) for j,c in row)+'\n')
(job/(newbase+'-metadata.json')).write_text(json.dumps({'classification':'S3-invariant Reynolds sums; independently reconstructed polynomial certificate still required','variables':meta['variables'],'columns':representatives,'source_matrix':base+'.matrix','source_rows':neworigins,'permutations':perms,'degree':degree},separators=(',',':'))+'\n')
print(json.dumps({'rows':len(newrows),'cols':len(representatives),'nnz':sum(map(len,newrows))}),flush=True)
