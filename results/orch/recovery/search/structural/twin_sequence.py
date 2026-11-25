from collections import deque
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
N=[set() for _ in range(10)]
for a,b in E:N[a].add(b);N[b].add(a)
V=set(range(10))
def close(S):return S|{v for v in V if not N[v]-S}
def step(S,r):
 R=N[r]-S
 cl={v for v in V-S if N[v]-S==R} if r not in S and R else set()
 return close(S|cl),cl
start=frozenset(close(set()))
Q=deque([start]);prev={start:None}
while Q:
 S=Q.popleft()
 if len(S)==10:break
 for r in V:
  T,cl=step(set(S),r);T=frozenset(T)
  if T not in prev:
   prev[T]=(S,r,cl,set(T)-set(S)-cl);Q.append(T)
path=[]
while prev[S]:
 P,r,cl,iso=prev[S];path.append((set(P),r,cl,iso,set(S)));S=P
path.reverse()
for row in path:print(row)
print('rounds',len(path),'states',len(prev))
