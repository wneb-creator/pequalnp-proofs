import argparse
from collections import Counter,defaultdict
import json,time
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--case',type=int);a=p.parse_args()
 r=Path('/tmp/oec/pequalnp-pilot-7')
 entries=json.loads((r/'root982-all-pair-manifest.json').read_text())
 output=[]
 for entry in entries:
  case=entry['case']
  if a.case is not None and case!=a.case:continue
  name=f'term-context-982-seed{case}-reduced-data.json' if case in [0,8] else f'root982-core{case}-data.json'
  d=json.loads((r/name).read_text());oldk=d['K'];pool=d['score_pool_truth_rows'];pcount=len(pool);n=d['n']
  extra_neg=[w[j] for j in [3,4,5] for w in pool]
  extra_pos=[w[j] for j in [0,1,2] for w in pool]
  rows=extra_neg+d['paired_rows'][:oldk]+extra_pos+d['paired_rows'][oldk:]
  k=oldk+3*pcount
  assert len(rows)==2*k and set(rows)==set(range(1<<n))
  def encode(w):return sum(((w>>row)&1)<<i for i,row in enumerate(rows))
  words=[int(w,16) for w in d['full_truth_words_hex']]
  oldencoded=[int(w,16) for w in d['encoded_words_hex']]
  newencoded=[encode(w) for w in words]
  assert sorted(range(len(words)),key=oldencoded.__getitem__)==sorted(range(len(words)),key=newencoded.__getitem__)
  inputs=[encode(sum(1<<v for v in range(1<<n) if v>>i&1)) for i in range(n)]
  fullperms=[]
  for gi,perm in enumerate(d['vertex_perms']):
   def source(row):return sum(((row>>perm[j])&1)<<j for j in range(n))
   def extra_action(values):
    byrow=defaultdict(list)
    for i,row in enumerate(values):byrow[row].append(i)
    seen=Counter();action=[]
    for row in values:
     rank=seen[row];seen[row]+=1
     action.append(byrow[source(row)][rank])
    assert sorted(action)==list(range(len(values)))
    return action
   low=extra_action(extra_neg)+[3*pcount+j for j in d['pair_perms'][gi]]
   high=extra_action(extra_pos)+[3*pcount+j for j in d['pair_perms'][gi]]
   action=low+[k+j for j in high]
   assert sorted(action)==list(range(2*k))
   assert all((j<k)==(action[j]<k) for j in range(2*k))
   assert all(rows[action[j]]==source(rows[j]) for j in range(2*k))
   fullperms.append(action)
  assert fullperms[0]==list(range(2*k))
  for gi,inv in enumerate(d['inverse_perms']):
   assert all(fullperms[gi][fullperms[inv][j]]==j for j in range(2*k))
  updated=dict(d)
  updated.update({'original_K':oldk,'K':k,'score_count':pcount,'paired_rows':rows,
    'encoded_words_hex':[hex(w) for w in newencoded],'inputs_hex':[hex(w) for w in inputs],
    'full_coordinate_perms':fullperms,'layout':'D,E,F below old negative rows; A,B,C below old positive rows',
    'original_encoded_order_preserved':True})
  updated.pop('pair_perms',None)
  path=r/f'root982-slice-core{case}.json';path.write_text(json.dumps(updated,indent=2)+'\n')
  summary={'case':case,'old_K':oldk,'K':k,'P':pcount,'states':sum(map(len,d['states'])),'word_order_preserved':True,'all_assignment_rows':True,'coordinate_actions_checked':len(fullperms)}
  output.append(summary);print(json.dumps(summary),flush=True)
 (r/('root982-slice-summary'+('' if a.case is None else '-'+str(a.case))+'.json')).write_text(json.dumps(output,indent=2)+'\n')
if __name__=='__main__':main()
