from pathlib import Path
import itertools,json,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30));job=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};points=[0,1,2,3,6,7];K=len(points);lines=sorted({(d-p)%13 for d in D for p in points});R=K+len(lines);edges=[(i,K+j) for i,p in enumerate(points) for j,l in enumerate(lines) if (p+l)%13 in D];outside=[p for p in range(13) if p not in points];groups=[];free=[];wire=R
for p in outside:
 ls=[l for l in lines if (p+l)%13 in D];raw=[K+lines.index(l) for l in ls];d=len(raw);assert 2<=d<=4;variants=[]
 if d==2:variants=[[[raw[0],raw[1]]]]
 if d==3:
  for excluded in range(3):variants.append([[raw[i] for i in range(3) if i!=excluded],[wire,raw[excluded]]])
 if d==4:
  for pair in itertools.combinations(range(4),2):
   remaining=[i for i in range(4) if i not in pair]
   for third,last in [remaining,list(reversed(remaining))]:variants.append([[raw[i] for i in pair],[wire,raw[third]],[wire+1,raw[last]]])
  for partner in range(1,4):variants.append([[raw[0],raw[partner]],[raw[i] for i in range(1,4) if i!=partner],[wire,wire+1]])
 for var in variants:
  support={i:{i} for i in range(R)}
  for off,(a,b) in enumerate(var):assert a<wire+off and b<wire+off;support[wire+off]=support[a]|support[b]
  assert support[wire+d-2]==set(raw) and len(var)==d-1
 groups.append({'outside_point':p,'in_patch_lines':ls,'raw_wires':raw,'first_free_wire':wire,'variants':variants});free.extend({'wire':wire+i,'op':'or','inputs':ab} for i,ab in enumerate(variants[0]));wire+=d-1
assert K==6 and len(lines)==11 and R==17 and wire==30 and len(free)==13
adj=[0]*R
for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
positive=sorted({(1<<a)|(1<<b) for a,b in edges});negative=[]
for m in range(1<<R):
 if any((m>>a&1) and (m>>b&1) for a,b in edges):continue
 if all(m>>v&1 or adj[v]&m for v in range(R)):negative.append(m)
out={'classification':'Six-point PG(2,3) patch with11lines; compatible free outside-star OR trees. Local28 implies global63; no witness yet.','difference_set':sorted(D),'point_inputs':points,'line_inputs':lines,'raw_inputs':R,'inputs_with_free_or_signals':wire,'edges':edges,'outside_groups':groups,'default_free_ors':free,'positive_raw_masks':positive,'maximal_negative_raw_masks':negative,'global_cost':{'free_or_prefix':len(free),'remaining_outside_or_gates':21-len(free),'outside_and_gates':7,'patch_gate_budget':28,'final_or_gates':7,'sum':63}};(job/'meta3773-six-dense-patch-data.json').write_text(json.dumps(out,indent=2)+'\n')
def cpp(xs):return '{'+','.join(cpp(x) if isinstance(x,list) else str(x) for x in xs)+'}'
header='constexpr int K=6,R=17,N=30,G=112,TARGET=28,BASE=35;\nconst vector<int> point_ids'+cpp(points)+',line_ids'+cpp(lines)+',outside_ids'+cpp(outside)+';\nconst vector<vector<vector<pair<int,int>>>> free_variants'+cpp([g['variants'] for g in groups])+';\n';(job/'meta3773_six_dense_patch_data.hpp').write_text(header);print(json.dumps({'point_inputs':points,'line_inputs':lines,'raw_inputs':R,'free_or_count':len(free),'positive_rows':len(positive),'negative_rows':len(negative),'group_variant_counts':[len(g['variants']) for g in groups]}),flush=True)
