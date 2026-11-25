from pathlib import Path
import json,importlib.util,time
p=Path('/tmp/oec/pequalnp-pilot-79');chart=3;cert=json.loads((p/'centered-two-macaulay-3-d9-exact-certificate.json').read_text());meta=json.loads((p/'centered-two-macaulay-3-d9-metadata.json').read_text());spec=importlib.util.spec_from_file_location('ng',p/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng);names,prime,polys=ng.parse_input(p/'centered-two-coordinate-3-rational.msolve')
groups=[{} for _ in polys]
for coefficient,(index,mult) in zip(cert['coefficients'],meta['row_origins']):
 if coefficient:
  for monom,value in polys[index].items():
   key=tuple(a+b for a,b in zip(mult,monom));groups[index][key]=groups[index].get(key,0)+coefficient*int(value)
groups=[{k:v for k,v in group.items() if v} for group in groups]
print('leaf_normal_supports',list(map(len,groups)),flush=True)
def add(a,b):
 result=a.copy()
 for k,v in b.items():result[k]=result.get(k,0)+v
 return{k:v for k,v in result.items() if v}
summary=[]
for mode in ['min_output','max_cancellation','min_peak']:
 nodes={str(i):g for i,g in enumerate(groups) if g};history=[];peak=max(map(len,nodes.values()));counter=0
 while len(nodes)>1:
  labels=list(nodes);best=None
  for ia,a in enumerate(labels):
   for b in labels[ia+1:]:
    merged=add(nodes[a],nodes[b]);la,lb,lc=len(nodes[a]),len(nodes[b]),len(merged)
    score={'min_output':(lc,la+lb),'max_cancellation':(lc-la-lb,lc),'min_peak':(max(la,lb,lc),lc)}[mode]
    if best is None or score<best[0]:best=(score,a,b,merged)
  _,a,b,merged=best;la,lb=len(nodes[a]),len(nodes[b]);del nodes[a];del nodes[b];label='m'+str(counter);counter+=1;nodes[label]=merged;peak=max(peak,len(merged));history.append({'left':a,'right':b,'left_support':la,'right_support':lb,'result':label,'result_support':len(merged)})
 assert next(iter(nodes.values()))=={(0,)*8:cert['denominator']}
 out={'mode':mode,'peak_support':peak,'history':history};summary.append(out);print(json.dumps(out),flush=True)
(p/'centered-two-chart3-chunk-statistics.json').write_text(json.dumps({'leaf_supports':list(map(len,groups)),'strategies':summary},indent=2)+'\n')
