from pathlib import Path
exec(open(str(Path(__file__).with_name('projection.py'))).read().split('rows7=')[0])
for k in range(1,8):
 stats={}
 for S in itertools.combinations(range(13),k):
  r=facts(sum(1<<i for i in S))
  key=(r['induced_max_false_count'],r['missing_max_false'],r['point_triples'])
  stats[key]=stats.get(key,0)+1
 print(k,stats)
