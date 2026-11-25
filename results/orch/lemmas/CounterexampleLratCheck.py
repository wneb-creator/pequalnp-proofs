import argparse,json,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('cnf');p.add_argument('proof');a=p.parse_args();start=time.monotonic()
clauses={};pending=[];declared=None;input_count=0
with Path(a.cnf).open() as f:
 for line in f:
  t=line.split()
  if not t or t[0]=='c':continue
  if t[0]=='p':
   assert len(t)==4 and t[1]=='cnf';declared=(int(t[2]),int(t[3]));continue
  for z in map(int,t):
   if z:pending.append(z)
   else:input_count+=1;clauses[input_count]=tuple(dict.fromkeys(pending));pending=[]
assert not pending and declared is not None and input_count==declared[1]
assert all(abs(v)<=declared[0] for c in clauses.values() for v in c)

def rup(c,hints):
 assignment={}
 for lit in c:
  var=abs(lit);val=lit<0
  if var in assignment and assignment[var]!=val:return True
  assignment[var]=val
 for cid in hints:
  assert cid>0,'RAT hints unsupported: refusing rather than guessing'
  assert cid in clauses,('Missing/deleted hint clause',cid)
  unassigned=[];satisfied=False
  for lit in clauses[cid]:
   var=abs(lit)
   if var not in assignment:unassigned.append(lit)
   elif assignment[var]==(lit>0):satisfied=True;break
  if satisfied:continue
  if not unassigned:return True
  assert len(unassigned)==1,('Hint is not unit',cid,unassigned)
  lit=unassigned[0];assignment[abs(lit)]=lit>0
 return False

additions=deletions=0;empty=False;max_id=input_count
with Path(a.proof).open() as f:
 for lineno,line in enumerate(f,1):
  t=line.split()
  if not t or t[0]=='c':continue
  assert len(t)>=3,(lineno,t)
  cid=int(t[0])
  if t[1]=='d':
   ids=list(map(int,t[2:]));assert ids[-1]==0
   for x in ids[:-1]:assert x>0;clauses.pop(x,None)
   deletions+=len(ids)-1;continue
  nums=list(map(int,t[1:]));z=nums.index(0)
  c=tuple(dict.fromkeys(nums[:z]));hints=nums[z+1:]
  assert hints and hints[-1]==0 and 0 not in hints[:-1],(lineno,'Bad hint terminator')
  assert cid>max_id,(lineno,'Nonincreasing clause ID')
  assert rup(c,hints[:-1]),(lineno,'RUP check failed')
  clauses[cid]=c;max_id=cid;additions+=1
  if not c:empty=True
assert empty,'No empty clause was derived: not a refutation'
print(json.dumps({'verdict':'VERIFIED RUP-only LRAT refutation','input_clauses':input_count,'checked_additions':additions,'deleted_clauses':deletions,'seconds':time.monotonic()-start}))
