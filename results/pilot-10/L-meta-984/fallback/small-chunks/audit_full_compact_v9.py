from pathlib import Path
import re,hashlib,json
B=Path('/tmp/oec/pequalnp-pilot-10');F=B/'fresh-full-proof/meta984'
s=(F/'Full984-compact-v9.lean').read_text();old=(F/'Full984-compact-v8.lean').read_text()
def ds(t):
 ms=list(re.finditer(r'^(?:def|theorem|lemma|abbrev|structure|inductive)\s+(\w+)',t,re.M))
 return {m[1]:t[m.start():ms[k+1].start() if k+1<len(ms) else len(t)].split('\nset_option ')[0].split('\nend PEqualNP.Outside.L_meta_984.Cert')[0].strip() for k,m in enumerate(ms)}
a,d=ds(old),ds(s)
assert hashlib.sha256(s.encode()).hexdigest()=='c777b1369bc0dd65a76f7f5c5590c65b4af53e328c714b8122f91912b24b5f5d'
assert len(s.encode())==512150 and len(s.splitlines())==6232
for n in a.keys()|d.keys():
 if not re.fullmatch(r'C\d+_(?:b\d+|j\d+|checked)',n):assert a.get(n)==d.get(n),n
assert s[:s.index('def C0_initial')]==old[:old.index('def C0_initial')]
assert not any(re.fullmatch(r'C\d+_j\d+',n) for n in d)
total=chunkcount=0
for i in range(31):
 name=f'C{i}';meta=json.loads((B/f'independent-search/984/compact/compact{i}.meta.json').read_text());size=sum(meta['states'].values());cap=meta['budget'];chunks={}
 for n,t in d.items():
  if re.fullmatch(name+r'_b\d+',n):
   m=re.fullmatch(r'theorem '+n+r' : span '+name+r'_F (\d+) (\d+) = true := by decide \+kernel',t);assert m,n
   count,offset=map(int,m.groups());assert count==min(128,size-offset) and count>0;chunks[n]=(offset,count)
 ordered=sorted(chunks,key=lambda n:chunks[n][0]);end=0
 for index,n in enumerate(ordered):
  assert n==f'{name}_b{index}' and chunks[n][0]==end;end+=chunks[n][1]
 assert end==size
 expected=f'theorem {name}_checked : ∀ s ≤ {cap}, ∀ j < {name}_N s, {name}_Z s j = true := by\n  apply certFlat_sound\n  change span {name}_F {size} 0 = true\n  exact '
 assert d[name+'_checked'].startswith(expected)
 expr=d[name+'_checked'][len(expected):]
 tokens=re.findall(r'\(|\)|span_join|C\d+_b\d+',expr)
 assert ''.join(tokens)==re.sub(r'\s+','',expr)
 pos=0;leaves=[]
 def parse():
  global pos
  t=tokens[pos];pos+=1
  if t=='(':
   assert tokens[pos]=='span_join';pos+=1
   left=parse();right=parse();assert tokens[pos]==')';pos+=1
   assert left[0]+left[1]==right[0],(i,left,right)
   return(left[0],left[1]+right[1],1+max(left[2],right[2]))
  assert t in chunks,t;leaves.append(t);return(*chunks[t],0)
 interval=parse();assert pos==len(tokens) and interval[:2]==(0,size) and leaves==ordered
 assert interval[2]<=6
 total+=size;chunkcount+=len(chunks)
 print('PASS graph',i,'states',size,'chunks',len(chunks),'balancedjoin depth',interval[2])
assert total==27783 and chunkcount==230
posted=json.loads((B/'desk-next-3.json').read_text())['gap']['statement'];last=s[s.index('theorem PEqualNP.Outside.L_meta_984 : '):]
assert re.sub(r'\s+',' ',last.split(' := by',1)[0].split(' : ',1)[1]).strip()==re.sub(r'\s+',' ',posted).strip()
assert re.findall(r'Cert\.C(\d+)_lower',last)==[str(i) for i in range(31)]
assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|admit|opaque|run_tac|elab|macro|initialize)\b|_root_|"|#',s)
for m in re.finditer(r'^set_option (\S+) .*$',s,re.M):assert m[1] in ['maxRecDepth','maxHeartbeats','synthInstance.maxSize','synthInstance.maxHeartbeats'] and m[0].endswith(' in')
names=list(d)
for j,n in enumerate(names):
 for use in set(re.findall(r'\bC\d+_\w+\b',d[n])):assert use==n or (use in d and names.index(use)<j),(n,use)
print('PASS v9 source-only audit: all230 chunks≤128 cover27783 states exactly once; every nestedjoin has contiguous intervals and correct summed conclusion; all other declarations/header/statement identical to reviewed v8.')
print('Source SHA256',hashlib.sha256(s.encode()).hexdigest(),'bytes',len(s.encode()),'remaining bytes below512KiB',524288-len(s.encode()))
print('Scope: UNCOMPILED fallback. No full Lean theorem or repository checker verdict claimed.')
