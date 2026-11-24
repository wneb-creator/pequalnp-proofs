import argparse,gc,hashlib,importlib.util,json,os,pathlib,random,shutil,signal,subprocess,time
spec=importlib.util.spec_from_file_location('fullbase','/tmp/oec/pequalnp-pilot-21/search/cegis-full.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
helper_spec=importlib.util.spec_from_file_location('stronghelpers','/tmp/oec/pequalnp-pilot-21/search/cegis-symbolic-five.py')
h=importlib.util.module_from_spec(helper_spec);helper_spec.loader.exec_module(h)
stream_spec=importlib.util.spec_from_file_location('streamingwriter','/tmp/oec/pequalnp-pilot-21/search/streaming_cnf.py')
sw=importlib.util.module_from_spec(stream_spec);stream_spec.loader.exec_module(sw)
ROOT=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/collective-diagnostic533')
ROOT.mkdir(exist_ok=True)
line_masks={sum(1<<p for p in L) for L in f.LINES}
six_masks={x for x in range(8192) if x.bit_count()==6 and any((x&line)==line for line in line_masks)}
triple_masks={line^(1<<p) for line in line_masks for p in range(13) if line>>p&1}
f.ROWS=sorted(six_masks|line_masks|triple_masks)
assert len(six_masks)==468 and len(line_masks)==13 and len(triple_masks)==52
f.INPUTS=[sum(1<<r for r,x in enumerate(f.ROWS) if x>>p&1) for p in range(13)]
f.TARGETS=[sum(1<<r for r,x in enumerate(f.ROWS) if all(x>>p&1 for p in L)) for L in f.LINES]
assert len(f.ROWS)==533

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as src:
  for chunk in iter(lambda:src.read(1048576),b''):h.update(chunk)
 return h.hexdigest()

def main():
 ap=argparse.ArgumentParser(description='Auxiliary533-row collective-avoidance diagnostic; not full-band synthesis. ANDroots, all533rows, binaryLRAT, and6.5GiB disk floor.')
 ap.add_argument('--seconds',type=int,default=5400)
 ap.add_argument('--prepare-only',action='store_true')
 args=ap.parse_args()
 started=time.monotonic();deadline=started+args.seconds;rng=random.Random(102438)
 samples=set(range(len(f.ROWS)))
 goals=list(range(13));ng=38;base=list(f.INPUTS);meta=[None]*13;proof=True
 for it in range(100):
  remaining=int(deadline-time.monotonic())
  if remaining<=0:break
  f.CNF=sw.streaming_class(f.b.CNF,ROOT/f'continuous-{it:03d}.clauses.part')
  c,ops,aa,bb=f.encode(base,meta,goals,ng,samples,True)
  c.add(aa[0][0]);c.add(bb[0][1])
  for op in ops[25:]:c.add(op)
  h.reachability(c,aa,bb,meta,goals)
  h.live_sinks(c,aa,bb,len(base),len(goals))
  h.lex_internal(c,ops,aa,bb,len(goals))
  stem=f'continuous-{it:03d}';cnf=ROOT/(stem+'.cnf');log=ROOT/(stem+'.log');lrat=ROOT/(stem+'.lrat.gz')
  c.save(cnf);(ROOT/(stem+'-rows.json')).write_text(json.dumps(sorted(samples))+'\n')
  print('SOLVE',it,'rows',len(samples),'vars',c.n,'clauses',len(c.cs),'proof',proof,'budget',remaining,flush=True)
  del c;gc.collect()
  if args.prepare_only:
   print('PREPARED_ONLY',flush=True);return
  argv=[f.SOLVER,'--unsat','-t',str(remaining),str(cnf)]
  if proof:argv=[f.SOLVER,'--unsat','--lrat','-t',str(remaining),str(cnf),str(lrat)]
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
   record={'status':'UNSAT_DIAGNOSTIC_ENCODING','scope':'533-row auxiliary problem, not the posted full-band theorem','cnf':str(cnf),'cnf_sha256':digest(cnf),'proof':str(lrat) if proof else None,'rows':len(samples),'row_families':{'line_containing_sixsets':468,'exact_lines':13,'deleted_point_triples':52},'first_pair':[0,1],'live_internals':True,'output_sinks':True,'exact_support':True,'lex_internal_order':True,'and_roots':True,'ordered':True,'full_band_only_guards':False}
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
    dual={'gates':gates,'out':[13+o for o in outs],'rows':len(f.ROWS)}
    for x in f.ROWS:
     ws=[bool(x>>i&1) for i in range(13)]
     for a,b,op in gates:
      assert 0<=a<len(ws) and 0<=b<len(ws)
      ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
     assert all(ws[dual['out'][w]]==all(bool(x>>p&1) for p in f.LINES[w]) for w in range(13))
    original=[(a,b,not op) for a,b,op in gates]
    errors=[0]*13
    derivative={8191^x for x in line_masks|triple_masks}
    for x in range(8192):
     ws=[bool(x>>i&1) for i in range(13)]
     for a,b,op in original:ws.append((ws[a] and ws[b]) if op else (ws[a] or ws[b]))
     wanted=[any(bool(x>>p&1) for p in L) for L in f.LINES]
     for w in range(13):
      assert not ws[dual['out'][w]] or wanted[w]
      if x in derivative:assert ws[dual['out'][w]]==wanted[w]
      if x.bit_count() in (7,8):errors[w]+=ws[dual['out'][w]]!=wanted[w]
    result={'scope':'auxiliary533-row diagnostic, full-band errors explicitly counted','gates':original,'out':dual['out'],'dual_gates':gates,'diagnostic_rows':533,'global_upper_checked_rows':8192,'derivative_rows':65,'band_rows_checked':3003,'band_errors_per_output':errors}
    (ROOT/'diagnostic-witness.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DIAGNOSTIC_FOUND','band_errors',errors,flush=True)
    if not any(errors):
     result['scope']='full original-band counterexample, independently scalar checked'
     (ROOT/'counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
     print('FOUND_ORIGINAL_BAND_COUNTEREXAMPLE',it,flush=True)
    return
   for rows in bad:rng.shuffle(rows);samples.update(rows[:16])
  if diskstop and lrat.exists():
   record={'status':'incomplete_trace_removed_for_disk_floor','path':str(lrat),'bytes':lrat.stat().st_size,'sha256':digest(lrat)}
   (ROOT/(stem+'-removed-proof.json')).write_text(json.dumps(record,indent=2)+'\n');lrat.unlink();proof=False
   print('SWITCHING_TO_WITNESS_SEARCH_WITHOUT_PROOF',flush=True)
  if status!='sat' and not diskstop:break
 print('FINISHED elapsed',round(time.monotonic()-started),flush=True)
if __name__=='__main__':main()
