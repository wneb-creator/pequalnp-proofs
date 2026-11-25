"""Final pair39 retry: fixed prefix, FULL cone, checked blocking and capacity.

The full cone additionally requires the frozen prefix aggregate to have a
reader. UNSAT therefore does not exclude the original unresolved local family.
"""
import argparse,datetime,hashlib,json,random,shutil,subprocess,sys,time
from pathlib import Path

ORIGINAL=Path('/tmp/oec/pequalnp-pilot-85/linear_network/star-cut')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--solver',required=True)
    ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--out',required=True)
    ap.add_argument('--control-only',action='store_true')
    args=ap.parse_args()
    out=Path(args.out);out.mkdir(exist_ok=True)
    sources=out/'sources';sources.mkdir(exist_ok=True)
    names=['synthesize_reference.py','search.py','normalized.py',
           'blocking_cuts.py','blocking_cuts_compact.py','reader_capacity.py']
    hashes={}
    for name in names:
        src=ORIGINAL/name;shutil.copy2(src,sources/name)
        hashes[name]=hashlib.sha256(src.read_bytes()).hexdigest()
    shutil.copy2(Path(__file__),sources/'final_retry_source.py')
    hashes['final_retry_source.py']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (out/'source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
    sys.path.insert(0,str(sources))
    import synthesize_reference as enc
    from search import star_prefix
    from normalized import add_normalization,normalize
    from blocking_cuts_compact import add_blocking_compact
    from reader_capacity import add_reader_capacity
    row=next(r for r in json.loads((ORIGINAL/'blocked-batch/summary.json').read_text())
             if r['original_case']==39)
    scope=row['scope']
    prefix,baseline=star_prefix(scope['side'],scope['chosen'])
    assert prefix==scope['prefix'] and len(prefix)==17
    scope={**scope,'original_case':39,'extra_restriction':'Every primary and every nonoutput gate has a reader; in particular the frozen prefix aggregate must be read.',
           'unsat_scope':'Strengthened fixed-prefix model only; not an exclusion of the original unresolved family.'}
    (out/'scope.json').write_text(json.dumps(scope,indent=2)+'\n')
    samples={x for x in range(1<<enc.N) if not (enc.TARGET>>x&1) or x.bit_count()<=2}
    initial_samples=sorted(samples)

    def build(rows,size,control=False):
        fixed=[g[:] for g in prefix]+[[1,0,1] for _ in range(size-len(prefix))]
        unlocked=set(range(len(prefix),size))
        if control:
            fixed=normalize(prefix,baseline)
            assert len(fixed)==size and not enc.evaluate(fixed)
            unlocked=set()
        cnf,schema=enc.make(rows,size,fixed=fixed,unlocked=unlocked,cone=True)
        tail=tuple(part[len(prefix):] for part in schema)
        keys=add_normalization(cnf,tail,len(prefix))
        blocking=add_blocking_compact(cnf,tail,prefix)
        # Capacity receives the FULL schema, never the sliced tail schema.
        capacity=add_reader_capacity(cnf,schema,input_count=enc.N)
        return cnf,schema,keys,blocking,capacity

    def query(directory,rows,size,seconds,control=False,deadline=None):
        directory.mkdir(exist_ok=True)
        cnf,schema,keys,blocking,capacity=build(rows,size,control)
        path=directory/'query.cnf';cnf.write(path)
        metadata={'gate_count':size,'frozen_prefix_gates':len(prefix),'samples':len(rows),
                  'variables':cnf.n,'clauses':len(cnf.clauses),'blocking':blocking,'capacity':capacity,
                  'extra_full_cone':True,'cnf_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        (directory/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
        (directory/'schema.json').write_text(json.dumps({'gates':schema,'tail_keys':keys})+'\n')
        (directory/'samples.json').write_text(json.dumps(rows)+'\n')
        if deadline is not None:
            seconds=min(seconds,int(deadline-time.monotonic()))
            if seconds<=0:
                return {'solver_exit':None,'status':'UNKNOWN','reason':'TIME_BUDGET_BEFORE_SOLVER'},[],None
        command=[args.solver,'--default','-t',str(seconds),str(path)]
        (directory/'command.json').write_text(json.dumps(command,indent=2)+'\n')
        log=directory/'solver.log'
        print('QUERY',directory.name,metadata,flush=True)
        del cnf
        with log.open('w') as f:proc=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
        result={'solver_exit':proc.returncode,'status':'UNKNOWN'}
        if proc.returncode==20:result['status']='UNSAT_STRENGTHENED_MODEL'
        elif proc.returncode==10:
            model={int(v) for line in log.read_text().splitlines() if line.startswith('v ')
                   for v in line[2:].split() if int(v)>0}
            gates=enc.decode(model,schema);delta=enc.evaluate(gates)
            errors=[x for x in range(1<<enc.N) if delta>>x&1]
            assert not any(x in rows for x in errors),'Decoded candidate violates a sampled row'
            candidate={'gates':gates,'gate_count':len(gates),'output':enc.N+len(gates)-1,
                       'errors':len(errors),'counterexamples':errors}
            (directory/'candidate.json').write_text(json.dumps(candidate,indent=2)+'\n')
            result.update({'status':'FOUND' if not errors else 'SAT_WITH_COUNTEREXAMPLES','errors':len(errors)})
            return result,errors,candidate
        elif proc.returncode!=0:result['status']='SOLVER_ERROR'
        return result,[],None

    control,_,candidate=query(out/'control25',initial_samples,25,30,True)
    assert control['status']=='FOUND' and candidate['gate_count']==25,'Positive control failed'
    control['status']='VALID25_CONTROL'
    (out/'control25/result.json').write_text(json.dumps(control,indent=2)+'\n')
    print('CONTROL',control,flush=True)
    if args.control_only:return
    started=time.monotonic();rng=random.Random(981193);summary=[]
    for round_id in range(20):
        remaining=int(args.seconds-(time.monotonic()-started))
        if remaining<=0:break
        result,errors,candidate=query(out/f'round-{round_id:02d}',sorted(samples),24,remaining,
                                      deadline=started+args.seconds)
        result.update({'round':round_id,'elapsed_seconds':time.monotonic()-started,
                       'timestamp':datetime.datetime.now(datetime.timezone.utc).isoformat()})
        (out/f'round-{round_id:02d}'/'result.json').write_text(json.dumps(result,indent=2)+'\n')
        summary.append(result)
        (out/'summary.json').write_text(json.dumps({'scope':scope,'results':summary},indent=2)+'\n')
        print('RESULT',result,flush=True)
        if result['status']=='FOUND':
            (out/'FOUND.json').write_text(json.dumps(candidate,indent=2)+'\n');return
        if result['status']!='SAT_WITH_COUNTEREXAMPLES':return
        samples.update(errors[:32]);samples.update(rng.sample(errors,min(64,len(errors))))
    print('UNKNOWN: retry time or round budget exhausted',flush=True)


if __name__=='__main__':main()
