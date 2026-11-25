import argparse,collections,hashlib,itertools,json,random,time
from pathlib import Path
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
FULL=(1<<1024)-1
INPUTS=[sum(1<<r for r in range(1024)if r>>i&1)for i in range(10)]
def target(r):return any((r>>a&1)and(r>>b&1)for a,b in EDGES)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(path):
 x=json.loads(Path(path).read_text());assert isinstance(x,(dict,list)),('invalid JSON shape',path);return x
def integer(x):return isinstance(x,int)and not isinstance(x,bool)
def gray_max(matrix):
 rows=len(matrix);cols=len(matrix[0])if rows else 0
 score=[0]*cols;best=0;bestmask=0;bestcols=[];previous=0
 for step in range(1,1<<rows):
  mask=step^(step>>1);changed=mask^previous;r=changed.bit_length()-1;direction=1 if mask&changed else -1
  for j in range(cols):score[j]+=direction*matrix[r][j]
  value=sum(x for x in score if x>0)
  if value>best:best=value;bestmask=mask;bestcols=[j for j,x in enumerate(score)if x>0]
  previous=mask
 return best,[r for r in range(rows)if bestmask>>r&1],bestcols

def brute_max(matrix):
 nr=len(matrix);nc=len(matrix[0])if nr else 0
 best=0
 for a in range(1<<nr):
  for b in range(1<<nc):
   best=max(best,sum(matrix[r][c]for r in range(nr)if a>>r&1 for c in range(nc)if b>>c&1))
 return best

def exact(matrix,rows,cols):
 small=[[matrix[r][c]for c in cols]for r in rows]
 if not rows or not cols:return {'cost':0,'rows':[],'columns':[],'enumerated_subsets':1,'orientation':'empty'}
 if len(rows)<=len(cols):
  v,a,b=gray_max(small);rr=[rows[i]for i in a];cc=[cols[j]for j in b];orientation='rows';count=1<<len(rows)
 else:
  v,b,a=gray_max([list(x)for x in zip(*small)]);rr=[rows[i]for i in a];cc=[cols[j]for j in b];orientation='columns';count=1<<len(cols)
 assert v==sum(matrix[r][c]for r in rr for c in cc)
 assert v>=0
 # Recompute through the opposite orientation, without retaining a witness.
 vv=gray_max([list(x)for x in zip(*small)])[0]if orientation=='rows'else gray_max(small)[0]
 assert v==vv,('orientation mismatch',v,vv)
 if len(rows)+len(cols)<=9:assert v==brute_max(small)
 return {'cost':v,'rows':rr,'columns':cc,'enumerated_subsets':count,'orientation':orientation}

def selftest():
 rng=random.Random(237387)
 for nr in range(1,5):
  for nc in range(1,5):
   for _ in range(10):
    m=[[rng.randrange(-9,10)for _ in range(nc)]for _ in range(nr)]
    assert gray_max(m)[0]==brute_max(m)
 assert gray_max([[-1,-2],[-3,-4]])[0]==0
 assert gray_max([[10,-100],[-100,10]])[0]==10
 return 162

def main():
 p=argparse.ArgumentParser(description='Exact independent integer rectangle/bank audit; no floating point or LP solver.')
 p.add_argument('--matrices',required=True);p.add_argument('--banks',required=True);p.add_argument('--out',required=True)
 p.add_argument('--claimed',help='Optional list/dict of per-bank exact witness records to compare.')
 a=p.parse_args();started=time.monotonic();tests=selftest()
 mats=read(a.matrices);banks=read(a.banks)
 if isinstance(mats,dict):mats=mats.get('certificates',mats.get('matrices',[mats]))
 if isinstance(banks,dict):banks=banks.get('banks',[banks])
 assert isinstance(mats,list)and all(isinstance(c,dict)for c in mats)
 assert isinstance(banks,list)and all(isinstance(b,dict)for b in banks)
 assert len({b['node']for b in banks})==len(banks)
 bankfacts=[]
 for b in banks:
  assert isinstance(b['state'],list)and all(isinstance(v,str)for v in b['state'])
  vals=[int(v,16)for v in b['state']];assert all(0<=v<=FULL for v in vals)
  assert integer(b['remaining'])and b['remaining']>=0
  known=set(INPUTS)|{0,FULL}
  for gate in b.get('history',[]):
   assert isinstance(gate,list)and len(gate)==3
   op,left,right=gate;assert op in (0,1,2,3)
   left=int(left,16);right=int(right,16)
   assert left in known and right in known,('unknown history operand',b['node'])
   value=(left&right)if op==0 else(left|right)if op==1 else(left&(FULL^right))if op==2 else((FULL^left)&right)
   known.add(value)
  assert all(v in known for v in vals),('bank root missing provenance',b['node'])
  bankfacts.append({'node':b['node'],'root_count':len(vals),'remaining':b['remaining'],'tight':len(vals)==b['remaining']+1,'distinct_signatures':len(set(vals)),'history_gates':len(b.get('history',[]))})
 profiles={};results=[]
 for c in mats:
  name=c['name'];pos=c['positive_rows'];neg=c['negative_rows'];weights=c['weights']
  assert isinstance(name,str)and all(integer(r)and 0<=r<1024 for r in pos+neg)
  assert all(target(r)for r in pos)and all(not target(r)for r in neg),('row classification',name)
  assert isinstance(weights,list)and len(weights)==len(pos)
  assert all(isinstance(row,list)and len(row)==len(neg)and all(integer(v)for v in row)for row in weights)
  total=sum(map(sum,weights));assert integer(c['total'])and total==c['total']
  matrixkey=hashlib.sha256(json.dumps({'p':pos,'n':neg,'w':weights},sort_keys=True).encode()).hexdigest()
  for b,facts in zip(banks,bankfacts):
   costs=[];ids=[]
   for valtext in b['state']:
    val=int(valtext,16);rs=[r for r,x in enumerate(pos)if val>>x&1];cs=[j for j,x in enumerate(neg)if not(val>>x&1)]
    key=(matrixkey,tuple(rs),tuple(cs))
    if key not in profiles:profiles[key]=exact(weights,rs,cs)
    costs.append(profiles[key]['cost']);ids.append(key)
   cost=sum(costs);margin=total-cost
   result={'matrix':name,'matrix_hash':matrixkey,'node':b['node'],'root_count':len(costs),'remaining':b['remaining'],'tight':facts['tight'],'root_costs':costs,'cost_sum':cost,'target_total':total,'margin':margin,'excludes_tight_bank':facts['tight']and margin>0}
   results.append(result)
   print(json.dumps(result),flush=True)
 claimed_status=None
 if a.claimed:
  claimed=read(a.claimed)
  if isinstance(claimed,dict):claimed=claimed.get('witnesses',claimed.get('results',[claimed]))
  assert isinstance(claimed,list)
  for w in claimed:
   name=w.get('matrix',w.get('certificate',w.get('name')));node=w.get('node',w.get('source_bank'))
   hits=[x for x in results if x['matrix']==name and x['node']==node];assert len(hits)==1,('claim not identified',name,node)
   actual=hits[0]
   for key in ['root_costs','cost_sum','margin']:
    if key in w:assert w[key]==actual[key],('claimed mismatch',key,name,node)
   bank=next(b for b in banks if b['node']==node)
   if 'remaining' in w:assert w['remaining']==actual['remaining']
   if 'total' in w:assert w['total']==actual['target_total']
   if 'source_bank_sha256' in w:assert w['source_bank_sha256']==hashlib.sha256(json.dumps(bank,sort_keys=True).encode()).hexdigest()
   if 'state'in w:
    assert list(map(lambda s:int(s,16),w['state']))==list(map(lambda s:int(s,16),bank['state']))
  claimed_status='PASS'
 output={'status':'PASS','selftests':tests,'matrices_source':a.matrices,'matrices_sha256':sha(a.matrices),'banks_source':a.banks,'banks_sha256':sha(a.banks),'claimed_sha256':sha(a.claimed)if a.claimed else None,'claimed_status':claimed_status,'bank_facts':bankfacts,'results':results,'profiles':[{'matrix_hash':k[0],'positive_support':list(k[1]),'negative_support':list(k[2]),**v}for k,v in profiles.items()],'seconds':time.monotonic()-started,'source_sha256':sha(__file__)}
 Path(a.out).write_text(json.dumps(output,indent=2)+'\n')
 print(json.dumps({'FINAL':'PASS','matrices':len(mats),'banks':len(banks),'pairs':len(results),'unique_profiles':len(profiles),'positive_cuts':sum(r['excludes_tight_bank']for r in results),'seconds':output['seconds'],'selftests':tests}),flush=True)
if __name__=='__main__':main()
