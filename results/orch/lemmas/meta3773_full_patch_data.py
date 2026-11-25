from pathlib import Path
import itertools,json,resource,hashlib
resource.setrlimit(resource.RLIMIT_CORE,(0,0));job=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};points=[0,1,2,5];lines=sorted({(d-p)%13 for d in D for p in points});edges=[(i,4+j) for i,p in enumerate(points) for j,l in enumerate(lines) if (p+l)%13 in D];assert len(edges)==16 and len(lines)==10;outside=[4,3,6,7,8,9,10,11,12];groups=[];free=[];nextwire=14
for p in outside:
 ls=[l for l in lines if (p+l)%13 in D];raw=[4+lines.index(l) for l in ls];assert len(ls) in [2,3];variants=[]
 if len(raw)==2:
  variants=[{'choice':0,'gates':[[raw[0],raw[1]]]}];free.append({'wire':nextwire,'op':'or','inputs':raw});default=0
 else:
  for choice in range(3):
   pair=[raw[i] for i in range(3) if i!=choice];variants.append({'choice':choice,'gates':[pair,[nextwire,raw[choice]]]})
  default=2
  for off,pair in enumerate(variants[default]['gates']):free.append({'wire':nextwire+off,'op':'or','inputs':pair})
 groups.append({'outside_point':p,'in_patch_lines':ls,'raw_wires':raw,'first_free_wire':nextwire,'default_choice':default,'variants':variants});nextwire+=len(raw)-1
assert nextwire==29
adj=[0]*14
for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
positives=sorted({(1<<a)|(1<<b) for a,b in edges});neg=[]
for m in range(1<<14):
 if any((m>>a&1) and (m>>b&1) for a,b in edges):continue
 if all(m>>v&1 or adj[v]&m for v in range(14)):neg.append(m)
assert len(neg)==16
assert free[0]['inputs']==[4+lines.index(9),4+lines.index(12)]
assert {(9*d)%13 for d in D}==D
assert (9*9-3)%13==0 and (9*12-3)%13==1
out={'classification':'Exact local PG(2,3) four-arc patch with compatible free OR chains from nine outside stars; local18 gates imply global63 after stated assembly. No18-gate witness yet.','difference_set':sorted(D),'point_inputs':points,'line_inputs':lines,'raw_inputs':14,'inputs_with_free_or_signals':29,'edges':edges,'outside_groups':groups,'default_free_ors':free,'positive_raw_masks':positives,'maximal_negative_raw_masks':neg,'global_cost':{'free_or_prefix':15,'remaining_outside_or_gates':12,'outside_and_gates':9,'patch_gate_budget':18,'final_or_gates':9,'sum':63},'head_normalization':{'first_gate_global_inputs':[22,25],'point_map':'p -> 9*p+3 mod13','line_map':'l -> 9*l-3 mod13','then_swap_bipartitions':True,'result_first_gate_inputs':[0,1]}};(job/'meta3773-full-patch-data.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'raw_inputs':14,'free_signals':15,'positive_rows':len(positives),'negative_rows':len(neg),'bytes':(job/'meta3773-full-patch-data.json').stat().st_size}),flush=True)
