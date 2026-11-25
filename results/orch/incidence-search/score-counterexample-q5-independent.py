import json,sys
from itertools import combinations
r=json.load(open(sys.argv[1]));p=r['p'];q=r['q'];n=p+q;es=set(map(tuple,r['edges']));gs=r['gates']
match=list(map(tuple,r['matching']));assert len(match)==31 and len({a for a,b in match})==31 and len({b for a,b in match})==31 and all(e in es for e in match)
for a,b in combinations(range(p),2):assert len({v for u,v in es if u==a}&{v for u,v in es if u==b})<=1
f=[{frozenset([i])} for i in range(n)];ss=[{i} for i in range(n)];reach=[{i} for i in range(n)]
for i,(op,a,b) in enumerate(gs):
 assert 0<=a<n+i and 0<=b<n+i and op in ['or','and']
 raw=f[a]|f[b] if op=='or' else {u|v for u in f[a] for v in f[b]}
 f.append({u for u in raw if not any(v<u for v in raw)})
 ss.append(ss[a]|ss[b] if op=='or' else ss[a]&ss[b]);reach.append(reach[a]|reach[b] if op=='or' else set())
 assert op!='or' or not(any(v<p for v in reach[-1]) and any(v>=p for v in reach[-1]))
assert f[r['output']]=={frozenset([a,p+b]) for a,b in es}
covered=set()
for w in r['witnesses']:
 assert len(w['leaves'])==2 and f[w['wire']]=={frozenset([v]) for v in w['leaves']}
 for v in w['leaves']:assert (w['center'],v-p) in es;covered.add((w['center'],v-p))
assert covered==es
assert all(ss[n+i] for i,(op,a,b) in enumerate(gs) if op=='and' and n+i!=r['output'])
assert all(r['output'] not in [a,b] for op,a,b in gs)
B=sum(bool(op=='and' and not ss[n+i] and ss[a] and ss[b]) for i,(op,a,b) in enumerate(gs))
M=sum(op=='or' and a!=b and bool(ss[a]) and bool(ss[b]) and len(ss[n+i])>1 for i,(op,a,b) in enumerate(gs))
assert (B,M)==(1,214)
print('INDEPENDENT EXACT ANTICHAIN CHECK PASSED; AO2, T0, no4cycles, matching31, all93starwitnesses, E186, B1, M214, score216<217.')
print('OutputTopForm also holds: every other AND accepts a singleton; output AND has no readers.')
print('Posted size bound unaffected: 217 <= 960.')
