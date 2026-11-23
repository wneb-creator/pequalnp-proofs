import json, hashlib, re, time
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-7')
def sha(f):return hashlib.sha256((P/f).read_bytes()).hexdigest()
def value(bits):
 a,b,c,d,e,f=bits;x=b+c;y=2-e-f
 return (y if d else max(x,y,x+y-1)) if a else (0 if d else x)
def encode(w,rows):
 out=0
 for row in reversed(rows):out=2*out+((w>>row)&1)
 return out
start=time.monotonic(); reports=[]
manifest=json.loads((P/'root982-all-pair-manifest.json').read_text())
assert sorted(e['case'] for e in manifest)==list(range(31))
for entry in manifest:
 case=entry['case'];oldfile=f'term-context-982-seed{case}-reduced-data.json' if case in (0,8) else f'root982-core{case}-data.json';newfile=f'root982-slice-core{case}.json'
 old=json.loads((P/oldfile).read_text());new=json.loads((P/newfile).read_text())
 n=old['n'];K=old['K'];pool=old['score_pool_truth_rows'];q=len(pool);k=K+3*q
 expected=[]
 for j in (3,4,5):expected.extend(t[j] for t in pool)
 expected.extend(old['paired_rows'][:K])
 for j in (0,1,2):expected.extend(t[j] for t in pool)
 expected.extend(old['paired_rows'][K:])
 assert new['K']==k and new['original_K']==K and new['score_count']==q
 assert new['paired_rows']==expected and set(expected)==set(range(1<<n))
 assert all(v in old['negative_rows'] for v in expected[:k])
 assert all(v in old['positive_rows'] for v in expected[k:])
 for key in ('states','advice','roots','vertex_perms','inverse_perms','full_truth_words_hex','score_pool_truth_rows'):
  assert old[key]==new[key],(case,key)
 words=[int(v,16) for v in old['full_truth_words_hex']]
 oldw=[int(v,16) for v in old['encoded_words_hex']];neww=[int(v,16) for v in new['encoded_words_hex']]
 assert [encode(v,expected) for v in words]==neww
 assert sorted(range(len(words)),key=oldw.__getitem__)==sorted(range(len(words)),key=neww.__getitem__)
 assert len(set(oldw))==len(oldw) and len(set(neww))==len(neww)
 assert all(((w>>(3*q))&((1<<K)-1))==(o&((1<<K)-1)) and (w>>(k+3*q))==(o>>K) for o,w in zip(oldw,neww))
 inps=[encode(sum(1<<a for a in range(1<<n) if (a>>j)&1),expected) for j in range(n)]
 assert [int(v,16) for v in new['inputs_hex']]==inps
 statecount=0
 for layer in new['states']:
  for ids in layer:
   values=[neww[j] for j in ids]
   assert values==sorted(values) and len(set(values))==len(values)
   statecount+=1
 coordinate_checks=0
 for gi,perm in enumerate(new['vertex_perms']):
  action=new['full_coordinate_perms'][gi]
  assert sorted(action)==list(range(2*k))
  assert all((j<k)==(action[j]<k) for j in range(2*k))
  def transform(a):
   return sum((1<<j) for j,v in enumerate(perm) if (a>>v)&1)
  for j,v in enumerate(expected):
   assert expected[action[j]]==transform(v)
   coordinate_checks+=1
  assert all(action[new['full_coordinate_perms'][new['inverse_perms'][gi]][j]]==j for j in range(2*k))
  for offset in (0,k):
   block=expected[offset:offset+3*q]
   for j,row in enumerate(block):
    rank=sum(x==row for x in block[:j])
    targets=[i for i,x in enumerate(block) if x==transform(row)]
    assert action[offset+j]==offset+targets[rank]
  assert action[3*q:k]==[3*q+j for j in old['pair_perms'][gi]]
  assert action[k+3*q:]==[k+3*q+j for j in old['pair_perms'][gi]]
 scalarchecks=0
 for full,w in zip(words,neww):
  for j,t in enumerate(pool):
   fromtruth=tuple((full>>a)&1 for a in t)
   fromfields=tuple((w>>a)&1 for a in (k+j,k+q+j,k+2*q+j,j,q+j,2*q+j))
   assert fromtruth==fromfields
   assert value(fromtruth)==value(fromfields)
   scalarchecks+=1
 reports.append({'case':case,'status':'PASS','original_file':oldfile,'slice_file':newfile,'old_sha256':sha(oldfile),'new_sha256':sha(newfile),'K':k,'P':q,'words':len(words),'states':statecount,'coordinate_direction_checks':coordinate_checks,'scalar_score_checks':scalarchecks})
 print(json.dumps(reports[-1]),flush=True)
d=json.loads((P/'root982-slice-core28.json').read_text());s=(P/'SliceCheckpoint28Leaf0.lean').read_text()
def leanlist(name):
 text=re.search(r'def '+name+r' : List Nat := \[([^\]]*)\]',s).group(1)
 return [int(t.strip(),0) for t in text.split(',') if t.strip()]
state=[int(d['encoded_words_hex'][i],16) for i in d['states'][9][0]]
assert leanlist('state')==state
assert leanlist('forbidden')==[0,(1<<(2*d['K']))-1]+[int(x,16) for x in d['inputs_hex']]
assert 'Slice.reject forbidden 623 94 10 9 state = true' in s
out={'status':'PASS','generator_sha256':sha('root982_slice_data.py'),'script_sha256':sha('c7_audit_slice982.py'),'seconds':time.monotonic()-start,'cases':reports,'totals':{'states':sum(x['states'] for x in reports),'words':sum(x['words'] for x in reports),'scalar_score_checks':sum(x['scalar_score_checks'] for x in reports),'coordinate_direction_checks':sum(x['coordinate_direction_checks'] for x in reports)},'case28_leaf0':{'status':'PASS','source_sha256':sha('SliceCheckpoint28Leaf0.lean'),'remaining':9,'index':0,'depth':10,'K':623,'P':94,'state_function_indices':d['states'][9][0]},'caveats':['score_pool_coordinates, score_pool_codes, score_width are retained from the original encoding and must not be used as slice-coordinate fields.','Numeric order was verified for all stored function words, not claimed for arbitrary functions.','This data audit is not a substitute for kernel-checked closure and symmetry transport.']}
(P/'c7-slice982-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','totals':out['totals'],'seconds':out['seconds']}),flush=True)
