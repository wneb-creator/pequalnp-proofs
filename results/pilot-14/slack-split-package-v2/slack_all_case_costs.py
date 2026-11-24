from pathlib import Path
import json,subprocess,sys,time
p=Path(__file__).parent
pairs=[(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]
rows=[];start=time.monotonic()
for i,j in pairs:
 for sign in range(4):
  with (p/f'slack-case-{i}-{j}-{sign}.out').open('w')as out,(p/f'slack-case-{i}-{j}-{sign}.err').open('w')as err:
   subprocess.run([sys.executable,str(p/'slack_case_child_costs.py'),str(i),str(j),str(sign)],stdout=out,stderr=err,check=True,cwd='/workspace/pequalnp-proofs')
  d=json.loads((p/f'SlackOneCase{i}{j}Sign{sign}Children.json').read_text());nodes=d['nodes'];dups=[];consume=[];retain=[]
  for m in d['moves']:
   cost=nodes[m['node']]['calls']
   if m['kind']=='duplicate':dups.append([m['move'][0],cost]);continue
   a,b,op=m['move']
   if a>b:continue
   pair=a*(19-a)//2+b-a-1
   index=4*pair+op
   if m['kind']=='merge':consume.append([index,cost])
   else:retain.append([index*2+(m['kind']=='retain_b'),cost])
  row={'pair':[i,j],'sign':sign,'summary':d['summary'],'duplicates':dups,'covered_consume':consume,'covered_retain':retain,'hard_consume':[x for x in consume if x[1]>60],'hard_retain':[x for x in retain if x[1]>60]}
  rows.append(row)
  print(json.dumps({'pair':[i,j],'sign':sign,'root_calls':d['summary']['root_cost'][1],'hard_duplicates':[x for x in dups if x[1]>60],'hard_consume':row['hard_consume'],'hard_retain':row['hard_retain']}),flush=True)
(p/'SlackOneAllCaseCosts.json').write_text(json.dumps({'rows':rows,'seconds':time.monotonic()-start,'sign_convention':'Two-bit sign on original raw inputs; bit1 flips first input, bit0 flips second. Initial child list g::raw.map phase. Unordered pairs lexicographic; op index00,01,10,11.'},separators=(',',':'))+'\n')
