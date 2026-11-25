from pathlib import Path
import itertools,json,time,resource,math,functools
OUT=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard')
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
def put(p,key,c):
    value=p.get(key,0)+c
    if value:p[key]=value
    else:p.pop(key,None)
def product(p,q):
    r={}
    for (a,m),c in p.items():
        for (b,n),d in q.items():
            put(r,(tuple(x+y for x,y in zip(a,b)),tuple(sorted(m+n))),c*d)
    return r
S=[[{} for j in range(4)] for i in range(4)]
for k in range(3):
    e=tuple(int(j==k) for j in range(3))
    for r in range(3):
        put(S[0][r+1],(e,(3*r+k,)),1)
        put(S[r+1][0],(e,(3*r+k,)),1)
        if k==r:
            put(S[0][r+1],(e,()),-1)
            put(S[r+1][0],(e,()),-1)
        put(S[r+1][r+1],(e,(9+3*r+k,)),2)
    for r,(i,j) in enumerate([(2,3),(1,3),(1,2)]):
        for a,b in [(i,j),(j,i)]:
            put(S[a][b],(e,(3*r+k,)),-1)
            if k==r:put(S[a][b],(e,()),3)
M=[[{} for j in range(4)] for i in range(4)]
for i,j in itertools.product(range(4),repeat=2):
    for r,s in itertools.product(range(4),repeat=2):
        for key,c in S[r][s].items():put(M[i][j],key,H[i][r]*H[s][j]*c)
    put(M[i][j],((0,0,0),()),1)
start=time.monotonic();total={}
for perm in itertools.permutations(range(4)):
    p={((0,0,0),()):1}
    for i in range(4):p=product(p,M[i][perm[i]])
    for key,c in p.items():put(total,key,c)
put(total,((0,0,0),()),-24)
assert all(sum(a)>=2 for a,m in total)
exponents=[a for d in range(2,5) for a in itertools.product(range(d+1),repeat=3) if sum(a)==d]
polys=[{m:c for (b,m),c in total.items() if a==b} for a in exponents]
assert len(polys)==31 and all(polys)
divisors={d:functools.reduce(math.gcd,(abs(c) for a,p in zip(exponents,polys) if sum(a)==d for c in p.values())) for d in range(2,5)}
polys=[{m:c//divisors[sum(a)] for m,c in f.items()} for a,f in zip(exponents,polys)]
print('GENERATED',len(polys),'terms',sum(map(len,polys)),'divisors',divisors,flush=True)
actions=json.loads(Path('/tmp/oec/pequalnp-pilot-78/construct_search/s4-hadamard-actions.json').read_text())
for action in actions:
    mapping=[v for v,s in action['variables']];signs=[s for v,s in action['variables']]
    gm=[];gs=[]
    for f in polys:
        transformed={}
        for m,c in f.items():
            sign=math.prod(signs[v] for v in m)
            put(transformed,tuple(sorted(mapping[v] for v in m)),c*sign)
        matches=[]
        for j,target in enumerate(polys):
            if transformed==target:matches.append((j,1))
            if transformed=={m:-c for m,c in target.items()}:matches.append((j,-1))
        assert len(matches)==1,(action['permutation'],len(matches))
        j,sign=matches[0];gm.append(j);gs.append(sign)
    action['generatormap']=gm;action['generatorsign']=gs
    print('ACTION_VERIFIED',action['permutation'],flush=True)
result={'coefficient_ring':'Z','variables':[f'p{i}' for i in range(9)]+[f'b{i}' for i in range(9)],'matrix_scale':8,'hadamard':H,'parameter_exponents':exponents,'degree_divisors':divisors,'polynomials':[[[list(m),c] for m,c in sorted(f.items())] for f in polys],'actions':actions}
(OUT/'chart.json').write_text(json.dumps(result,separators=(',',':')))
print(json.dumps({'pass':True,'generators':31,'action_identities':24*31,'terms':sum(map(len,polys)),'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}),flush=True)
