from pathlib import Path
import json
p=Path(__file__).parent;data=json.loads((p/'Data414.json').read_text());domains=json.loads((p/'Domains12.json').read_text());raw=[tuple(int(a,0)for a in s)for s in data['raw']]
for marker in(4,6,7):
 indices=[j for j,(a,b)in enumerate(data['pairs'])if(a>>marker)&1 and(b>>marker)&1]
 assert len(indices)==94
 sel=[indices[j%94]for j in range(252)];keep=[i for i in range(9)if i!=marker]
 vals=[tuple(sum(((raw[i][side]>>ix)&1)<<j for j,ix in enumerate(sel))for side in range(2))for i in keep]
 assert all(0<a<(1<<252)-1 or 0<b<(1<<252)-1 for a,b in vals)
 domains.append({'kind':'positive','marker':marker,'bound':10,'pos':sel,'neg':sel,'embedding':keep,'raw':vals,'distinct_pairs':94})
(p/'Domains15.json').write_text(json.dumps(domains,separators=(',',':'))+'\n')
def cpp(value):
 if isinstance(value,list):return'{'+','.join(cpp(x)for x in value)+'}'
 return str(value)
selectors=[[d['pos'],d['neg']]for d in domains]
words=[[[((s[side]>>(64*w))&((1<<64)-1))for side in range(2)for w in range(4)]for s in d['raw']]for d in domains]
source=(p/'live_theta12.cpp').read_text().splitlines();out=[]
for line in source:
 if line.startswith('static constexpr int projectIndex'):line='static constexpr int projectIndex[D][2][252] = '+cpp(selectors)+';'
 if line.startswith('static constexpr U oldRaw'):line='static constexpr U oldRaw[D][8][8] = '+cpp(words)+';'
 line=line.replace('int D=12','int D=15').replace('(q<3?13:11)','(q<3?13:q<12?11:10)')
 out.append(line)
(p/'live_positive15.cpp').write_text('\n'.join(out)+'\n')
print('domains',len(domains),'positive raw counts',[len(d['raw'])for d in domains[12:]])
