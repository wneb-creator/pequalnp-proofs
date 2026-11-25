import itertools, json, time

n=6; target_edges=16
start=time.monotonic(); budget=10.0
pop=[mask.bit_count() for mask in range(1<<n)]
compatible=[[pop[a&b]<=1 for b in range(1<<n)] for a in range(1<<n)]
options=[[mask for mask in range(1<<n) if mask>>a&1] for a in range(n)]
base=[sum(1<<(b-1) for b in range(1,7) if (a-b)%7 in (0,1,3)) for a in range(1,7)]
orbit=set()
for perm in itertools.permutations(range(n)):
 orbit.add(tuple(sorted(sum(((row>>b)&1)<<perm[b] for b in range(n)) for row in base)))
nodes=0; count=0; outside=[]; patterns={}
class BudgetReached(Exception):pass

def visit(rows,total,remaining):
 global nodes,count
 nodes+=1
 if nodes%1000==0 and time.monotonic()-start>budget:raise BudgetReached
 if not remaining:
  if total==target_edges:
   count+=1
   pattern=tuple(sorted(pop[row] for row in rows));patterns[pattern]=patterns.get(pattern,0)+1
   if tuple(sorted(rows)) not in orbit and len(outside)<3:outside.append(rows.copy())
  return
 for mask in remaining[0]:
  value=total+pop[mask]
  if value>target_edges:continue
  future=[[other for other in opts if compatible[mask][other]] for opts in remaining[1:]]
  if any(not opts for opts in future):continue
  if value+sum(min(pop[other] for other in opts) for opts in future)>target_edges:continue
  if value+sum(max(pop[other] for other in opts) for opts in future)<target_edges:continue
  visit(rows+[mask],value,future)
complete=True
try:visit([],0,options)
except BudgetReached:complete=False
print(json.dumps({'n':n,'edges':target_edges,'fixed_diagonal':True,'complete':complete,
                  'recursion_nodes':nodes,'labelled_graphs':count,
                  'known_fano66_column_orbit_size':len(orbit),
                  'all_found_isomorphic_to_fano66':not outside,'outside_examples':outside,
                  'row_degree_patterns':{str(key):value for key,value in patterns.items()},
                  'elapsed_seconds':time.monotonic()-start},indent=2))
