import argparse,gc,hashlib,importlib.util,json,os,pathlib,random,shutil,signal,subprocess,time
spec=importlib.util.spec_from_file_location('fullbase','/tmp/oec/pequalnp-pilot-21/search/cegis-full.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
helper_spec=importlib.util.spec_from_file_location('stronghelpers','/tmp/oec/pequalnp-pilot-21/search/cegis-symbolic-five.py')
h=importlib.util.module_from_spec(helper_spec);helper_spec.loader.exec_module(h)
stream_spec=importlib.util.spec_from_file_location('streamingwriter','/tmp/oec/pequalnp-pilot-21/search/streaming_cnf.py')
sw=importlib.util.module_from_spec(stream_spec);stream_spec.loader.exec_module(sw)
cost_spec=importlib.util.spec_from_file_location('normalformalcount','/tmp/oec/pequalnp-pilot-21/search/formal_cost.py')
fc=importlib.util.module_from_spec(cost_spec);cost_spec.loader.exec_module(fc)
ROOT=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/full-normal-or-sinks-cost-stream')
ROOT.mkdir(exist_ok=True)

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as src:
  for chunk in iter(lambda:src.read(1048576),b''):h.update(chunk)
 return h.hexdigest()

def atmost_three(c,xs):
 previous=None;states=[]
 for x in xs:
  current=[c.var() for _ in range(3)]
  c.add(-x,current[0])
  if previous is not None:
   for j in range(3):c.add(-previous[j],current[j])
   for j in range(1,3):c.add(-x,-previous[j-1],current[j])
   c.add(-x,-previous[2])
  previous=current;states.append(current)
 return states

def normal_partition(c, ops, aa, bb, boundary):
 own=boundary['own_complement']
 assert len(ops)==38 and len(own)==13
 for value in own:c.add(-value)
 costs=fc.exact_costs(c,ops,aa,bb,13,{})
 c.add(*(row[5] for row in costs[-13:]))
 return costs


def validate_partition(gates, outputs):
 assert len(gates)==38 and sum(op for _,_,op in gates)>=2
 assert all(not gates[o-13][2] for o in outputs)
 def values(x):
  ws=[bool(x>>p&1) for p in range(13)]
  for a,b,op in gates:ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
  return [ws[o] for o in outputs]
 own=[values(8191^sum(1<<p for p in f.LINES[w]))[w] for w in range(13)]
 singles={p:values(1<<p) for p in range(13)}
 nonordinary=[any(not singles[p][w] for p in f.LINES[w]) for w in range(13)]
 assert not any(own) and sum(nonordinary)>=5
 costs=[1]*13
 for a,b,op in gates:costs.append(min(costs[a],costs[b]) if op else min(5,costs[a]+costs[b]))
 output_costs=[costs[o] for o in outputs]
 assert max(output_costs)==5
 for x in range(8192):
  actual=values(x)
  assert all(not actual[w] or any(x>>p&1 for p in f.LINES[w]) for w in range(13))
 return {'original_and_count':sum(op for _,_,op in gates),'own_complement_positive':[],
         'nonordinary_outputs':[w for w in range(13) if nonordinary[w]],
         'formal_output_costs':output_costs,'all8192_global_upper_rows_checked':True}


def main():
 global ROOT
 ap=argparse.ArgumentParser(description='Complementary normal38-gate OR-sink query: all own-complements false, >=5nonordinary and some formal false cost5; fullband.')
 ap.add_argument('--seconds',type=int,default=5400)
 ap.add_argument('--case',type=int,choices=[-1,0,1,2],default=-1)
 ap.add_argument('--sat',action='store_true',help='Use satisfiable-instance solver tuning.')
 ap.add_argument('--all-rows',action='store_true',help='Constrain all3003 band rows from the first query.')
 ap.add_argument('--prepare-only',action='store_true')
 args=ap.parse_args()
 ROOT=ROOT/f'case-{args.case}';ROOT.mkdir(exist_ok=True)
 started=time.monotonic();deadline=started+args.seconds;rng=random.Random(102438)
 samples={r for r in range(len(f.ROWS)) if any(not(f.TARGETS[w]>>r&1) for w in range(13))}
 samples.update(rng.sample(range(len(f.ROWS)),100))
 if args.all_rows:samples=set(range(len(f.ROWS)))
 goals=list(range(13));ng=38;base=list(f.INPUTS);meta=[None]*13;proof=True
 for it in range(100):
  remaining=int(deadline-time.monotonic())
  if remaining<=0:break
  f.CNF=sw.streaming_class(f.b.CNF,ROOT/f'continuous-{it:03d}.clauses.part')
  c,ops,aa,bb=f.encode(base,meta,goals,ng,samples,True)
  pair=(0,1) if args.case<0 else [(0,1),(1,3),(1,2)][args.case]
  c.add(aa[0][pair[0]]);c.add(bb[0][pair[1]]);c.add(*ops)
  for op in ops:c.add(*(other for other in ops if other!=op))
  for op in ops[25:]:c.add(-op)
  if args.case>=0:atmost_three(c,[v for a,b in zip(aa,bb) for v in (a[0],b[0])])
  supports=h.reachability(c,aa,bb,meta,goals)
  h.live_sinks(c,aa,bb,len(base),len(goals))
  h.lex_internal(c,ops,aa,bb,len(goals))
  boundary=h.offband_rows(c,ops,aa,bb)
  exotic=h.nonordinary_lower_bound(c,boundary,minimum=5)
  h.nonordinary_support(c,exotic,supports[-13:])
  normal_partition(c,ops,aa,bb,boundary)
  stem=f'continuous-{it:03d}';cnf=ROOT/(stem+'.cnf');log=ROOT/(stem+'.log');lrat=ROOT/(stem+'.lrat.gz')
  c.save(cnf);(ROOT/(stem+'-rows.json')).write_text(json.dumps(sorted(samples))+'\n')
  print('SOLVE',it,'rows',len(samples),'vars',c.n,'clauses',len(c.cs),'proof',proof,'budget',remaining,flush=True)
  del c;gc.collect()
  if args.prepare_only:
   print('PREPARED_ONLY',flush=True);return
  tuning='--sat' if args.sat else '--unsat'
  argv=[f.SOLVER,tuning,'-t',str(remaining),str(cnf)]
  if proof:argv=[f.SOLVER,tuning,'--lrat','-t',str(remaining),str(cnf),str(lrat)]
  diskstop=False;lastnote=0;interrupted=None
  with log.open('w') as output:
   proc=subprocess.Popen(argv,stdout=output,stderr=subprocess.STDOUT,preexec_fn=lambda:os.setpriority(os.PRIO_PROCESS,0,15))
   (ROOT/(stem+'-pid.json')).write_text(json.dumps({'solver_pid':proc.pid,'runner_pid':os.getpid()})+'\n')
   while proc.poll() is None:
    now=time.monotonic();free=shutil.disk_usage(ROOT).free
    if free<6.5*2**30 and interrupted is None:
     diskstop=True;interrupted=now;proc.send_signal(signal.SIGINT)
     print('DISK_FLOOR_INTERRUPT','freeGiB',round(free/2**30,2),flush=True)
    if now>=deadline and interrupted is None:
     interrupted=now;proc.send_signal(signal.SIGINT)
     print('BUDGET_INTERRUPT',flush=True)
    if interrupted is not None and now-interrupted>30 and proc.poll() is None:proc.terminate()
    if now-lastnote>=60:
     print('RUNNING','elapsed',round(now-started),'freeGiB',round(free/2**30,2),'proofMiB',round(lrat.stat().st_size/2**20,1) if lrat.exists() else 0,flush=True)
     lastnote=now
    time.sleep(5)
   code=proc.wait()
  status,gates,_=f.b.extract(log,ops,aa,bb,[])
  print('RESULT',status,'exit',code,'elapsed',round(time.monotonic()-started),flush=True)
  if status=='unsat':
   record={'status':'UNSAT_ENCODING','all_output_roots_or':True,'or_sink_normalization':'Lean-checked FirstAnd normalization; encoder and symmetry separately audited','minimum_globally_nonordinary':5,'minimum_original_and':2,'all_own_complements_false':True,'some_formal_false_cost5':True,'formal_cost_justification':'Lean-checked FalsePruning.some_large_cost','partition_scope':'OR-sink normalized candidates with all own-complements false; active abnormal query covers the complementary class','additional_partial_offband_rows':104,'cnf':str(cnf),'cnf_sha256':digest(cnf),'proof':str(lrat) if proof else None,'rows':len(samples),'first_pair':pair,'fanout_zero_max':3 if args.case>=0 else None,'pair_case':args.case,'at_least_two_and':True,'ordered':True,'exact_support':True,'live_internals':True,'output_sinks':True,'single_and_normalization':'Lean-checked OneAndWork theorem; normalization and encoder separately audited'}
   (ROOT/'unsat.json').write_text(json.dumps(record,indent=2)+'\n')
   print('UNSAT_ENCODING',str(cnf),flush=True);return
  if status=='sat':
   vals=list(base)
   for a,b,op in gates:vals.append(vals[a]&vals[b] if op else vals[a]|vals[b])
   outs=list(range(25,38));bad=[]
   for goal,o in zip(goals,outs):
    diff=vals[13+o]^f.TARGETS[goal];bad.append([r for r in range(len(f.ROWS)) if diff>>r&1])
   print('ERRORS',[len(rows) for rows in bad],flush=True)
   assert len(samples)!=len(f.ROWS) or not any(bad),'SAT model violates an encoded row'
   if not any(bad):
    if args.case>=0:assert sum((a==0)+(b==0) for a,b,_ in gates)<=3
    result={'gates':gates,'out':[13+o for o in outs],'rows':len(f.ROWS)}
    result['partition_validation']=validate_partition(gates,result['out'])
    for x in f.ROWS:
     ws=[bool(x>>i&1) for i in range(13)]
     for a,b,op in gates:ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
     assert all(ws[result['out'][w]]==any(bool(x>>p&1) for p in f.LINES[w]) for w in range(13))
    (ROOT/'counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
    print('FOUND',it,flush=True);return
   for rows in bad:rng.shuffle(rows);samples.update(rows[:16])
  if diskstop and lrat.exists():
   record={'status':'incomplete_trace_removed_for_disk_floor','path':str(lrat),'bytes':lrat.stat().st_size,'sha256':digest(lrat)}
   (ROOT/(stem+'-removed-proof.json')).write_text(json.dumps(record,indent=2)+'\n');lrat.unlink();proof=False
   print('SWITCHING_TO_WITNESS_SEARCH_WITHOUT_PROOF',flush=True)
  if status!='sat' and not diskstop:break
 print('FINISHED elapsed',round(time.monotonic()-started),flush=True)
if __name__=='__main__':main()
