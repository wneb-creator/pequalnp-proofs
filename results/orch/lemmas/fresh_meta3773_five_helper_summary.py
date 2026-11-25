from pathlib import Path
import json,itertools,re
s=Path(__file__).resolve().parent
v=json.loads((s/'fresh-meta3773-five-point-types.json').read_text())[1];P=5;R=v['raw_count'];nei=[{i for i,j in v['E']if j==y}for y in range(P,R)];features=list(map(frozenset,v['free']));group=[]
for perm in itertools.permutations(range(P)):
 line=[]
 for a in nei:
  b={perm[p]for p in a}
  if b not in nei:break
  line.append(P+nei.index(b))
 if len(line)!=len(nei):continue
 raw=[*perm,*line];fp=[]
 for support in features:
  b=frozenset(raw[i]for i in support)
  if b not in features:break
  fp.append(R+features.index(b))
 if len(fp)==len(features):group.append(tuple(raw+fp))
assert len(group)==12
summary=[];seen_masks=set()
for m in (31,47,55,62):
 base=tuple(range(R))+tuple(R+i for i in range(7)if m>>i&1);ss=set(base);stab=[q for q in group if {q[i]for i in base}==ss];orbit={sum(1<<(q[i]-R)for i in base if i>=R)for q in group};assert m==min(orbit) and not (seen_masks&orbit);seen_masks|=orbit
 for d in range(4):
  cases={min(tuple(sorted(q[i]for i in t))for q in stab)for t in itertools.combinations_with_replacement(base,d)};pref=f'fresh-meta3773-five-1-{m}-{d}-';p=s/(pref+'progress.json');j=json.loads(p.read_text())if p.exists()else {'total':len(cases),'tested':0,'hits':[]};assert j['total']==len(cases) and not j['hits'];ids=set();logs=sorted(s.glob(pref+'*.log'))
  for f in logs:
   x=f.read_text();assert 'result True' not in x
   for n,tot in re.findall(r'case (\d+) of (\d+) result False',x):assert int(tot)==len(cases);ids.add(int(n))
  assert ids==set(range(1,j['tested']+1));z=s/(pref+'cone.json');cn=json.loads(z.read_text())['next_cone']if z.exists()else None
  summary.append({'helper_mask':m,'extra_primitive_reads':d,'allowed_internal_excess':3-d,'orbit_count':len(cases),'finished_prefix':j['tested'],'finished':j['tested']==len(cases),'last_root_cone_checkpoint':cn,'false_suffix_cache_bytes':(s/(pref+'deadstates.bin')).stat().st_size if(s/(pref+'deadstates.bin')).exists()else 0,'complete_log_files':len(logs)})
assert len(seen_masks)==21
print(json.dumps({'scope':'all four exterior-feature orbits with exactly five used helpers, only listed finished prefixes excluded','strata':summary,'completed_strata':sum(x['finished'] for x in summary),'completed_representatives':sum(x['finished_prefix']for x in summary),'all_representatives':sum(x['orbit_count']for x in summary),'witnesses':0},indent=2))
