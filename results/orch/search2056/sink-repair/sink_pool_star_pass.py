from pathlib import Path
import json,hashlib,datetime,collections,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
from normalize_andbudget_sinks import load,make_sinks
base=Path('/tmp/oec/pequalnp-pilot-121');mine=base/'not-elimination';module=load(base/'andcount2056/andcount_budget_profile_sink2056.py','encoder');norm=load(mine/'normalize_andbudget_model.py','normalizer');geometry=module.geometry();module.geometry=lambda:geometry;edges,rows=geometry;P=(1<<52)-1
pool_path=Path('/workspace/pequalnp-proofs/results/orch/search2056/nested-stratified/final-populations.json');records=json.loads(pool_path.read_text());best=json.loads((mine/'plane2056-strata4-analysis.json').read_text())['best'];records+=best
seen=set();reports=[];witnesses=[];skipped=0;best_exact=None;best_nonlinear=None
for ri,r in enumerate(records):
 key=json.dumps(r['gates'])+str(r['output'])
 if key in seen:continue
 seen.add(key);gates=r['gates'];supports=[{i} for i in range(26)];ands=[]
 for j,(op,a,b) in enumerate(gates):
  assert 0<=a<26+j and 0<=b<26+j
  if op:supports.append(supports[a]|supports[b])
  else:
   ands.append({'left':sorted(supports[a]),'right':sorted(supports[b])});supports.append({26+len(ands)-1})
 if any(i<26 for i in supports[r['output']]):skipped+=1;continue
 model={'ands':ands,'output':sorted(i-26 for i in supports[r['output']])};_,original=module.evaluate(model,rows)
 ordinary={'gates':gates,'output':r['output'],'constant_false':False,'size':len(gates)};assert module.ordinary_eval(ordinary,rows)==original
 new,report=make_sinks(module,norm,model,max(16,len(ands)));vals,value=module.evaluate(new,rows);missing=[k for k in range(52) if not(value>>k&1)];fp=(value&~P).bit_count();entry={'record':ri,'mode':r['mode'],'original_raw':(original^P).bit_count(),'before_bound':norm.cost(model)[0],'after_bound':norm.cost(new)[0],'missing':len(missing),'false_positives':fp,'removed_output_references':report['deleted_output_reference_occurrences']}
 if fp==0:
  positions={k:i for i,k in enumerate(missing)};full=(1<<len(missing))-1;options=[]
  for j in range(len(new['ands'])):
   if vals[26+j]&~P:continue
   cover=sum(1<<positions[k] for k in missing if vals[26+j]>>k&1)
   if cover:options.append((cover,1,('existing',j)))
  for k in missing:
   point,line=edges[k]
   for j in new['output']:
    rec=new['ands'][j]
    # Choose one center per gate, so simultaneous repairs cannot enlarge both operands.
    if len(rec['left'])==1 and rec['left'][0]<26:
     endpoint=rec['left'][0]; other=line if endpoint==point else point if endpoint==line else None
     if other is not None and other not in rec['right']:options.append((1<<positions[k],1,('extend',[j,'right',other])))
    elif len(rec['right'])==1 and rec['right'][0]<26:
     endpoint=rec['right'][0]; other=line if endpoint==point else point if endpoint==line else None
     if other is not None and other not in rec['left']:options.append((1<<positions[k],1,('extend',[j,'left',other])))
  for k in missing:options.append((1<<positions[k],2,('atomic',k)))
  if len(missing)<=12:
   dp={0:(0,[])}
   for cov,cost,choice in options:
    previous=list(dp.items())
    for have,(weight,choices) in previous:
     after=have|cov;proposal=(weight+cost,choices+[choice])
     if after not in dp or proposal[0]<dp[after][0]:dp[after]=proposal
   entry['repair_method']='exact membership cover on at most12 missing edges'
  else:
   remaining=full;choices=[];weight=0
   while remaining:
    cov,cost,choice=max(options,key=lambda item:((item[0]&remaining).bit_count()/item[1],-item[1]))
    assert cov&remaining;remaining&=~cov;choices.append(choice);weight+=cost
   dp={full:(weight,choices)}
   entry['repair_method']='bounded greedy membership cover'
  assert full in dp
  repaired=json.loads(json.dumps(new))
  for kind,index in dp[full][1]:
   if kind=='existing':repaired['output'].append(index)
   elif kind=='extend':
    j,side,other=index;repaired['ands'][j][side]=sorted(set(repaired['ands'][j][side]+[other]))
   else:
    p,l=edges[index];repaired['output'].append(len(repaired['ands']));repaired['ands'].append({'left':[p],'right':[l]})
  repaired['output']=sorted(set(repaired['output']));_,v=module.evaluate(repaired,rows);assert v==P
  final,rr=make_sinks(module,norm,repaired,len(repaired['ands']));actual=module.materialize(final);assert module.ordinary_eval(actual,rows)==P
  pointFlags=[sum(1<<k for k,e in enumerate(edges) if i in e) if i<13 else 0 for i in range(26)]
  lineFlags=[sum(1<<k for k,e in enumerate(edges) if i in e) if i>=13 else 0 for i in range(26)]
  joint=[0]*26
  for op,a,b in actual['gates']:
   if op:pointFlags.append(pointFlags[a]|pointFlags[b]);lineFlags.append(lineFlags[a]|lineFlags[b]);joint.append(joint[a]|joint[b])
   else:pointFlags.append(0);lineFlags.append(0);joint.append((pointFlags[a]&lineFlags[b])|(lineFlags[a]&pointFlags[b]))
  bad=52-(joint[actual['output']]&P).bit_count();entry['repaired_missing_read1_edges']=bad
  if bad and (best_nonlinear is None or actual['size']<best_nonlinear['circuit']['size']):
   best_nonlinear={'record':ri,'circuit':actual,'and_model':final,'missing_read1_edges':bad,'metrics':entry}
   (mine/'sink-star-pool-best-nonlinear.json').write_text(json.dumps(best_nonlinear,indent=2)+'\n')
  entry.update({'repair_membership_cost':dp[full][0],'repair_choices':dp[full][1],'repaired_bound':norm.cost(final)[0],'repaired_actual_size':actual['size']})
  if best_exact is None or actual['size']<best_exact['circuit']['size']:
   best_exact={'record':ri,'circuit':actual,'and_model':final,'metrics':entry}
   (mine/'sink-star-pool-best-exact.json').write_text(json.dumps(best_exact,indent=2)+'\n')
  if actual['size']<=63:
   witnesses.append(best_exact);(mine/'sink-star-pool-WITNESS.json').write_text(json.dumps({'circuit':actual,'and_model':final,'metrics':entry},indent=2)+'\n')
 reports.append(entry)
 if ri%20==0:print(json.dumps({'processed_record':ri,'missing':len(missing),'best_exact_size':None if best_exact is None else best_exact['circuit']['size']}),flush=True)
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'finite repair pass complete; no target witness' if not witnesses else 'candidate found; full verification required','input_records':len(records),'unique_records':len(seen),'processed':len(reports),'skipped_primary_outputs':skipped,'records_with_output_references':sum(r['removed_output_references']>0 for r in reports),'records_with_reduced_accounting_bound':sum(r['after_bound']<r['before_bound'] for r in reports),'exact_repairs_checked':sum('repaired_actual_size' in r for r in reports),'minimum_exact_repair_size':None if best_exact is None else best_exact['circuit']['size'],'minimum_nonlinear_exact_size':None if best_nonlinear is None else best_nonlinear['circuit']['size'],'witness_count':len(witnesses),'input_pool_sha256':hashlib.sha256(pool_path.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(mine/'sink-star-pool-pass.json').write_text(json.dumps({'summary':summary,'records':reports},indent=2)+'\n');print(json.dumps(summary,indent=2))
