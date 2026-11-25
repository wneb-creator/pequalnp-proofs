from pathlib import Path
import json,time

START=time.monotonic()
HERE=Path(__file__).resolve().parent
MASK=(1<<64)-1
variables=[0,2,3,5,6,9]
bank={}
for j,i in enumerate(variables):
    bank[sum(((x>>j)&1)<<x for x in range(64))]=f'x{i}'
def var(i):
    j=variables.index(i)
    return sum(((x>>j)&1)<<x for x in range(64))
for a,b in ((2,5),(9,3),(6,0),(3,6)):
    bank[var(a)|var(b)]=f'(x{a}|x{b})'
for xs in ((2,5,9),(9,3,0),(6,0,2),(3,6,5)):
    t=0
    for i in xs:t|=var(i)
    bank[t]='('+'|'.join(f'x{i}' for i in xs)+')'
bank[0]='false'
target=(var(0)&var(5))|(var(2)&var(3))|(var(6)&var(9))
dp=[[{},{}] for _ in range(4)]
dp[0][0]=bank
dp[0][1]={MASK^t:('not',t,0) for t in bank}
def expr(t,k,n):
    e=dp[k][n][t]
    if isinstance(e,str):return e
    if e[0]=='not':return '!'+expr(e[1],e[2],0)
    op,a,ka,na,b,kb,nb=e
    return '('+expr(a,ka,na)+op+expr(b,kb,nb)+')'
result={'bank':bank,'target':target,'counts':[]}
for k in range(4):
    if k:
        for n in (0,1):
            if n:
                for t in dp[k][0]:dp[k][1].setdefault(MASK^t,('not',t,k))
            for ka in range(k):
                kb=k-1-ka
                for na in range(n+1):
                    nb=n-na
                    for a in dp[ka][na]:
                        for b in dp[kb][nb]:
                            for op,c in (('&',a&b),('|',a|b)):
                                dp[k][n].setdefault(c,(op,a,ka,na,b,kb,nb))
    row={'binary':k,'monotone':len(dp[k][0]),'one_not':len(dp[k][1]),'seconds':time.monotonic()-START}
    result['counts'].append(row)
    print(json.dumps(row),flush=True)
    for n in (0,1):
        if target in dp[k][n]:
            result['witness']={'binary':k,'not':n,'expression':expr(target,k,n)}
            print(json.dumps(result['witness']),flush=True)
(HERE/'one-not-residual-result.json').write_text(json.dumps(result,indent=2)+'\n')
