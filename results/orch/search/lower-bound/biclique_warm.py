import argparse,json,time
from collections import deque
from pathlib import Path

EDGES=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def target(mask):return any((mask>>a)&(mask>>b)&1 for a,b in EDGES)
def evaluate(gates,mask):
 values=[bool(mask&(1<<i)) for i in range(14)]
 for op,a,b in gates:
  assert 0<=a<=b<len(values)
  values.append(values[a] or values[b] if op else values[a] and values[b])
 return values[-1]

def rectangle_cover(false_masks,budget,seconds):
 allowed=[127]*7
 for mask in false_masks:
  for right in range(7):
   if mask&(1<<(7+right)):allowed[right]&=~(mask&127)
 left_dist=[100]*128;left_dist[0]=0
 for m in range(128):
  for part in [1<<i for i in range(7)]+[3,5]:
   left_dist[m|part]=min(left_dist[m|part],left_dist[m]+1)
 unique={}
 for a in range(1,128):
  common=sum(1<<r for r,n in enumerate(allowed) if a&n==a)
  b=common
  while b:
   coverage=sum(1<<i for i,(x,y) in enumerate(EDGES) if a&(1<<x) and b&(1<<(y-7)))
   if coverage:
    trim_a=sum(1<<x for x in range(7) if any(coverage&(1<<i) and ex==x for i,(ex,_) in enumerate(EDGES)))
    trim_b=sum(1<<(y-7) for y in range(7,14) if any(coverage&(1<<i) and ey==y for i,(_,ey) in enumerate(EDGES)))
    cost=left_dist[trim_a]+trim_b.bit_count()
    record=(cost,trim_a,trim_b)
    if coverage not in unique or record<unique[coverage]:unique[coverage]=record
   b=(b-1)&common
 rectangles=[(cov,*entry) for cov,entry in unique.items()]
 options=[[i for i,r in enumerate(rectangles) if r[0]&(1<<edge)] for edge in range(21)]
 deadline=time.monotonic()+seconds;memo={};nodes=0
 def search(remaining,cost):
  nonlocal nodes
  nodes+=1
  if nodes%1024==0 and time.monotonic()>deadline:raise TimeoutError('cover search deadline')
  if not remaining:return []
  if cost<2:return None
  if memo.get(remaining,-1)>=cost:return None
  memo[remaining]=cost
  candidates=[]
  for edge in range(21):
   if remaining&(1<<edge):
    opts=[i for i in options[edge] if rectangles[i][1]<=cost]
    if not opts:return None
    if not candidates or len(opts)<len(candidates):candidates=opts
  candidates.sort(key=lambda i:(-((rectangles[i][0]&remaining).bit_count()/rectangles[i][1]),rectangles[i][1]))
  for i in candidates:
   cov,weight,_,_=rectangles[i]
   ans=search(remaining&~cov,cost-weight)
   if ans is not None:return [i]+ans
  return None
 answer=search((1<<21)-1,budget)
 return None if answer is None else [rectangles[i] for i in answer],{'allowed_columns':allowed,'rectangles':len(rectangles),'nodes':nodes}

def build_gates(rectangles):
 gates=[[1,0,1],[1,0,2]];sums={1<<i:i for i in range(14)};sums.update({3:14,5:15})
 def add(op,a,b):
  gates.append([op,min(a,b),max(a,b)]);return 13+len(gates)
 def raw(wanted):
  if wanted in sums:return sums[wanted]
  usable=[(m,w) for m,w in sums.items() if m&wanted==m]
  previous={0:None};queue=deque([0])
  while wanted not in previous:
   m=queue.popleft()
   for part,wire in usable:
    nxt=m|part
    if nxt not in previous:previous[nxt]=(m,part,wire);queue.append(nxt)
  parts=[];m=wanted
  while m:
   old,part,wire=previous[m];parts.append((part,wire));m=old
  parts.reverse();mask,wire=parts[0]
  for part,next_wire in parts[1:]:
   mask|=part
   if mask in sums:wire=sums[mask]
   else:wire=add(1,wire,next_wire);sums[mask]=wire
  return wire
 lefts=sorted({a for _,_,a,_ in rectangles},key=lambda a:(a.bit_count(),a))
 for a in lefts:raw(a)
 terms=[add(0,raw(a),raw(b<<7)) for _,_,a,b in rectangles]
 output=terms[0]
 for term in terms[1:]:output=add(1,output,term)
 renamed={i:i for i in range(16)};ordered=gates[:2]
 while len(ordered)<len(gates):
  ready=[]
  for i,(op,a,b) in enumerate(gates[2:],2):
   if 14+i not in renamed and a in renamed and b in renamed:
    x,y=sorted((renamed[a],renamed[b]));ready.append(((x,y,op),i))
  assert ready
  (a,b,op),i=min(ready);renamed[14+i]=14+len(ordered);ordered.append([op,a,b])
 assert renamed[output]==13+len(ordered)
 unpadded=len(ordered)
 while len(ordered)<26:wire=13+len(ordered);ordered.append([1,wire,wire])
 return ordered,unpadded

def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--log',required=True);parser.add_argument('--output',required=True);parser.add_argument('--seconds',type=float,default=5)
 args=parser.parse_args()
 false_masks=[127,16256]
 for line in Path(args.log).read_text().splitlines():
  words=line.split()
  if words and words[0]=='selected_row':false_masks.append(int(words[3]))
 solution,stats=rectangle_cover(false_masks,25,args.seconds)
 stats['false_masks']=false_masks;stats['found']=solution is not None
 if solution is not None:
  gates,count=build_gates(solution);assert len(gates)==26
  assert all(evaluate(gates,(1<<a)|(1<<b)) for a,b in EDGES)
  assert all(not evaluate(gates,m) for m in false_masks)
  full=all(evaluate(gates,m)==target(m) for m in range(1<<14))
  stats.update(unpadded=count,rectangles_used=solution,gates=gates,checked_all_16384=full)
  Path(args.output+'.hint').write_text('26\n'+''.join(f'{op} {a} {b}\n' for op,a,b in gates))
 Path(args.output+'.json').write_text(json.dumps(stats,indent=2)+'\n')
 print(json.dumps({k:v for k,v in stats.items() if k not in ('gates','rectangles_used')},sort_keys=True))
if __name__=='__main__':main()
