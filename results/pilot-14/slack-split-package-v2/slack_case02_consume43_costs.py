from pathlib import Path
from functools import lru_cache
import itertools,json,time
p=Path(__file__).parent;d=json.loads((p/'Data414.json').read_text())
n=414;mask=(1<<n)-1;full=(1<<(2*n))-1
phase=lambda a:a^full if(a>>477)&1 else a
sep=lambda a:((a>>n)^a)&mask
rawOriginal=[(int(a,0)<<n)|int(b,0)for a,b in d['raw']]
raw=tuple(phase(a)for a in rawOriginal)
@lru_cache(None)
def ops(a,b):return tuple(sorted({phase(x&y)for x in(a,a^full)for y in(b,b^full)}))
def covered(v):
 c=0
 for a in v:c|=sep(a)
 return c==mask
@lru_cache(None)
def cost(s,dep,v):
 if not covered(v):return(False,0,1)
 if dep==0 or len(v)<=1:return(True,1,1)
 calls=trials=1
 def take(ss,dd,ww):
  nonlocal calls,trials
  yes,c,t=cost(ss,dd,tuple(sorted(ww)));calls+=c;trials+=t
  return yes
 if s:
  for a in set(v):
   if take(0,dep,v+(a,)):return(True,calls,trials)
 for i,j in itertools.combinations(range(len(v)),2):
  r=tuple(a for k,a in enumerate(v)if k not in(i,j))
  for z in ops(v[i],v[j]):
   if take(s,dep-1,r+(z,)):return(True,calls,trials)
   if s:
    if take(0,dep-1,r+(z,v[i])):return(True,calls,trials)
    if take(0,dep-1,r+(z,v[j])):return(True,calls,trials)
 return(False,calls,trials)
start=time.monotonic();g=phase((rawOriginal[0]^full)&rawOriginal[2]);root=(g,)+raw;z=phase((root[1]^full)&(root[3]^full));v=(z,)+tuple(a for i,a in enumerate(root)if i not in(1,3))
nodes=[];indices={};moves=[]
def emit(kind,move,s,dep,w):
 if not covered(w):return
 key=(s,dep,tuple(sorted(w)))
 if key not in indices:
  yes,c,t=cost(*key);assert not yes
  indices[key]=len(nodes);nodes.append({'slack':s,'depth':dep,'v':[hex(a)for a in key[2]],'calls':c,'trials':t})
 moves.append({'kind':kind,'move':move,'node':indices[key]})
for i,a in enumerate(v):emit('duplicate',[i],0,3,(a,)+v)
for i,a in enumerate(v):
 for j,b in enumerate(v):
  if i==j:continue
  rest=tuple(x for k,x in enumerate(v)if k not in(i,j))
  for op,(sa,sb)in enumerate(((0,0),(0,1),(1,0),(1,1))):
   z=phase((a^(full if sa else 0))&(b^(full if sb else 0)))
   emit('merge',[i,j,op],1,2,(z,)+rest)
   emit('retain_a',[i,j,op],0,2,(z,a)+rest)
   emit('retain_b',[i,j,op],0,2,(z,b)+rest)
summary={'root_cost':cost(1,3,tuple(sorted(v))),'unique_children':len(nodes),'ordered_valid_moves':len(moves),'sum_unique_calls':sum(r['calls']for r in nodes),'max_child':max(enumerate(nodes),key=lambda x:x[1]['calls'])[0],'seconds':time.monotonic()-start}
print(json.dumps(summary),flush=True)
(p/'SlackOneCase02Sign2Consume43Children.json').write_text(json.dumps({'summary':summary,'root':[hex(a)for a in v],'nodes':nodes,'moves':moves},separators=(',',':'))+'\n')
