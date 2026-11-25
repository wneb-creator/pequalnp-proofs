from collections import deque
import json,time

def functions(n):
    return [sum(1<<s for s in range(1<<n) if s>>i&1) for i in range(n)]

def solve(n,edges,limit):
    start=time.monotonic()
    fv=functions(n)
    initial=tuple((v,int(i==1),int(i==0)) for i,v in enumerate(fv))
    target=sum(1<<s for s in range(1<<n) if any((s>>i&1) and (s>>j&1) for i,j in edges))
    target=(target,0,0)
    seen={tuple(sorted(set(initial)))}
    frontier=[(initial,[])]
    for d in range(1,limit+1):
        nxt=[]
        for ws,prog in frontier:
            for i,a in enumerate(ws):
                for j in range(i):
                    b=ws[j]
                    for op in [0,1]:
                        if op==0:
                            c=(a[0]|b[0],a[1]|b[1],a[2]|b[2])
                        else:
                            c=(a[0]&b[0], ((a[0]>>1)&1)&b[1] | a[1]&((b[0]>>1)&1), ((a[0]>>2)&1)&b[2] | a[2]&((b[0]>>2)&1))
                        if c==target:
                            print(json.dumps({'n':n,'edges':edges,'depth':d,'prog':prog+[(op,i,j)],'secs':time.monotonic()-start}),flush=True)
                            return
                        # Keep multiplicities of two because distinct indices may be semantically identical.
                        if ws.count(c)>=2: continue
                        key=tuple(sorted(ws+(c,)))
                        if key in seen: continue
                        seen.add(key)
                        nxt.append((ws+(c,),prog+[(op,i,j)]))
        frontier=nxt
        print(json.dumps({'n':n,'depth':d,'frontier':len(frontier),'seen':len(seen),'secs':time.monotonic()-start}),flush=True)
        if len(frontier)>300000: return
if __name__=='__main__':
    solve(2,[(0,1)],4)
    solve(3,[(0,1),(0,2)],5)
    solve(3,[(0,1),(0,2),(1,2)],6)
