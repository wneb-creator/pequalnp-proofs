from pathlib import Path
import re,ast,collections,json
source=Path('results/orch/lemmas/lower-bound/Selected256.lean').read_text()
D={m.group(1):m.group(2) for m in re.finditer(r'^def ([A-Za-z0-9_]+)[^\n]*\n(.*?)(?=^(?:def|theorem|lemma|set_option|end) |\Z)',source,re.M|re.S)}
words={}
for name,body in D.items():
 if re.fullmatch(r'(compactWords\d+|ax\d+Words|word\d+_\d+)',name):
  words[name]={int(i):int(v,16) for i,v in re.findall(r'^  \| (\d+) => 0x([0-9a-f]+)',body,re.M)}
for name in list(words):
 m=re.fullmatch(r'word(\d+)_(\d+)',name)
 if m:
  table='ax'+m[1]+'Words';base=int(m[2])*8
  words.setdefault(table,{}).update({base+i:v for i,v in words[name].items()})
def read(table,start,width):
 i,j=divmod(start,4096);v=words[table].get(i,0)>>j
 if j+width>4096:v|=words[table].get(i+1,0)<<(4096-j)
 return v&((1<<width)-1)
metadata={}
pat=r'\| (\d+) => let v := readCompactBits (\w+) \((\d+) \+ (\d+)\*i\) (\d+)\s+let n := v >>> (\d+)\s+let bits := readCompactBits \w+ \((\d+) \+ (\d+)\*\(v &&& (\d+)\)\) \((\d+)\*n\)\s+compactIDsFromBits bits (\d+) n'
for name,body in D.items():
 if re.fullmatch(r'(compactPoolIDs\d+|ax\d+PoolIDs)',name):
  group=name.replace('compactPoolIDs','compact').replace('PoolIDs','')
  for match in re.findall(pat,body):
   k,table,off,stride,width,shift,base,st2,mask,bw,bw2=match
   nums=list(map(int,(k,off,stride,width,shift,base,st2,mask,bw,bw2)))
   k,off,stride,width,shift,base,st2,mask,bw,bw2=nums
   assert stride==width and st2==bw==bw2 and mask==(1<<shift)-1
   metadata[(group,k)]=(table,off,stride,width,shift,base,mask,bw)
spans={};allnodes={}
for l in Path('/tmp/oec/pequalnp-pilot-184/search/all-pools.tsv').read_text().splitlines():
 if not l.startswith('PICKS\t'):continue
 f=l.split('\t');group,k,i=f[1],int(f[2]),int(f[3]);ids=ast.literal_eval(f[4]);key=(group,k,i)
 table,off,stride,width,shift,base,mask,bw=metadata[(group,k)]
 v=read(table,off+stride*i,width);n=v>>shift;start=base+bw*(v&mask)
 got=[read(table,start+bw*j,bw) for j in range(n)]
 assert got==ids,(key,got,ids)
 span=(table,start,bw,n)
 spans.setdefault(span,[]).append(key)
 allnodes[str(key)]=span
valid=[x for x in spans if x[-1]>0];overlap=[]
for table in {x[0] for x in valid}:
 ss=sorted(x for x in valid if x[0]==table)
 for a,b in zip(ss,ss[1:]):
  if a[1]+a[2]*a[3]>b[1]:overlap.append((a,b))
print('states',len(allnodes),'unique_storage_spans',len(spans),'shared_spans',sum(len(x)>1 for x in spans.values()),'partial_overlaps',len(overlap))
print('overlap_examples',overlap[:4])
Path('/tmp/oec/pequalnp-pilot-184/search/pool-storage.json').write_text(json.dumps({'nodes':allnodes,'spans':[{'span':s,'nodes':ns} for s,ns in spans.items()],'overlaps':overlap},indent=2))
