import argparse,ast,json,re
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('log');ap.add_argument('output');a=ap.parse_args()
E=[(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
pins=[sum(1<<r for r in range(1<<14) if r>>v&1) for v in range(14)]
target=0
for p,q in E:target|=pins[p]&pins[q]
reports=[]
for line in Path(a.log).read_text().splitlines():
 m=re.fullmatch(r'best (\d+) trial (\d+) gates (\[.*\])',line)
 if not m:continue
 gs=ast.literal_eval(m.group(3));w=pins[:]
 for i,(op,p,q) in enumerate(gs):
  assert op in (0,1) and 0<=p<14+i and 0<=q<14+i
  w.append((w[p]|w[q]) if op else (w[p]&w[q]))
 used={14+len(gs)-1}
 for i in range(len(gs)-1,-1,-1):
  if 14+i in used:used.update(gs[i][1:])
 report={'trial':int(m.group(2)),'advertised_score':int(m.group(1)),'correct_full_cube':w[-1]==target,'live_gates':sum(14+i in used for i in range(len(gs))),'live_or_gates':sum(14+i in used and g[0]==1 for i,g in enumerate(gs))}
 if report['advertised_score']<128:
  assert report['correct_full_cube'] and report['live_or_gates']==report['advertised_score']
 reports.append(report)
result={'rows':16384,'reports':reports,'all_correct_cost_claims_verified':True}
Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
