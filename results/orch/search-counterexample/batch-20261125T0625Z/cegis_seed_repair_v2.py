import argparse
from datetime import datetime,timezone
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

BASE=Path('/tmp/oec/pequalnp-pilot-62')
GENERATOR=BASE/'global_or_seed_subset_cnf.py'
RUNNER=BASE/'solve_global_cnf_v8.py'
DATA=BASE/'global-first-or-symmetry.json'

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while chunk:=f.read(1048576):h.update(chunk)
    return h.hexdigest()

def choose_rows(pool,chosen,count,negative,false_counts=None):
    pool=set(pool)-set(chosen)
    answer=[]
    while pool and len(answer)<count:
        present=list(chosen)+answer
        def score(i):
            spread=min(((negative[i]^negative[j]).bit_count() for j in present),default=26)
            deficit=-false_counts[i] if false_counts is not None else 0
            return deficit,spread,-i
        selected=max(pool,key=score)
        answer.append(selected);pool.remove(selected)
    return answer

def seed_errors(witness,positive,negative):
    samples=positive+negative+[1<<i for i in range(26)]
    full=(1<<len(samples))-1
    values=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(26)]
    assert witness['input_count']==26 and len(witness['operand_wire_lists'])==witness['or_count']
    for a,b in witness['operand_wire_lists']:
        operands=[]
        for refs in [a,b]:
            assert refs and all(type(i) is int and 0<=i<len(values) for i in refs)
            v=full
            for i in refs:v &= values[i]
            operands.append(v)
        values.append(operands[0]|operands[1])
    result=full
    for i in witness['output_wire_list']:
        assert type(i) is int and 0<=i<len(values)
        result &= values[i]
    assert result&((1<<52)-1)==(1<<52)-1
    return [i for i in range(468) if result>>(52+i)&1]

def preserve_key_cnf(path,expected_hash):
    compressed=path.with_suffix(path.suffix+'.gz')
    if not compressed.exists():
        with path.open('rb') as source,compressed.open('wb') as dest,gzip.GzipFile(filename='',mode='wb',fileobj=dest,mtime=0) as z:
            shutil.copyfileobj(source,z)
    h=hashlib.sha256()
    with gzip.open(compressed,'rb') as z:
        while chunk:=z.read(1048576):h.update(chunk)
    assert h.hexdigest()==expected_hash
    path.unlink()
    return str(compressed)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--seed-witness',required=True)
    ap.add_argument('--free-gates',required=True)
    ap.add_argument('--tag',required=True)
    ap.add_argument('--generator-sha256',required=True)
    ap.add_argument('--runner-sha256',required=True)
    ap.add_argument('--rounds',type=int,default=8)
    ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--initial-rows',type=int,default=8)
    ap.add_argument('--initial-seed-good',action='store_true')
    ap.add_argument('--add-rows',type=int,default=12)
    args=ap.parse_args()
    assert args.tag and all(c.isalnum() or c in '-_' for c in args.tag)
    assert 0<args.rounds<=20 and 0<args.seconds<=900
    assert 0<args.initial_rows<=468 and 0<args.add_rows<=468
    assert digest(GENERATOR)==args.generator_sha256 and digest(RUNNER)==args.runner_sha256
    seed=Path(args.seed_witness).resolve();seed_hash=digest(seed)
    dependencies={str(p):digest(p) for p in [DATA,BASE/'multi_output_direct_cnf.py',BASE/'multi-output-baseline39.json']}
    controller_hash=digest(Path(__file__).resolve())
    data=json.loads(DATA.read_text());positive=data['positive_samples'];negative=data['negative_samples']
    assert len(positive)==52 and len(negative)==468
    bad=seed_errors(json.loads(seed.read_text()),positive,negative)
    assert bad
    initial_pool=[i for i in range(468) if i not in bad] if args.initial_seed_good else bad
    assert initial_pool
    selected=sorted(choose_rows(initial_pool,[],args.initial_rows,negative))
    overall={'started_utc':datetime.now(timezone.utc).isoformat(),'seed':str(seed),'seed_sha256':seed_hash,
       'seed_generic_errors':len(bad),'initial_rows_rejected_by_seed':args.initial_seed_good,'generator_sha256':args.generator_sha256,'runner_sha256':args.runner_sha256,
       'geometry_sha256':digest(DATA),'dependency_sha256':dependencies,'controller_sha256':controller_hash,'free_gates':args.free_gates,'or_count':50,'iterations':[],
       'scope':'Pinned-signature repair with growing selected negative rows; full verification required'}
    summary=BASE/(args.tag+'.summary.json')
    for iteration in range(args.rounds):
        assert digest(seed)==seed_hash and digest(GENERATOR)==args.generator_sha256 and digest(RUNNER)==args.runner_sha256
        assert all(digest(Path(p))==h for p,h in dependencies.items())
        stem=BASE/(args.tag+'-r'+str(iteration).zfill(2))
        rows=stem.with_suffix('.rows.json');rows.write_text(json.dumps(selected,indent=2)+'\n')
        encode=['python3',str(GENERATOR),'50','--seeded','--seed-witness',str(seed),'--allow-invalid-seed',
           '--free-gates',args.free_gates,'--dirty-singletons','--negative-indices',str(rows),'--cnf-only','--tag',stem.name]
        solve=['python3',str(RUNNER),str(stem),'--seconds',str(args.seconds),'--address-space-gib','1','--random-seed',str(iteration+1)]
        entry={'iteration':iteration,'started_utc':datetime.now(timezone.utc).isoformat(),
           'selected_generic_rows':selected.copy(),'encode_argv':encode,'solve_argv':solve,
           'generator_sha256':args.generator_sha256,'runner_sha256':args.runner_sha256,'seed_sha256':seed_hash,
           'dependency_sha256':dependencies,'controller_sha256':controller_hash}
        with stem.with_suffix('.encode.log').open('w') as log:completed=subprocess.run(encode,cwd=BASE,stdout=log,stderr=subprocess.STDOUT)
        entry['encoder_exit']=completed.returncode
        if completed.returncode:
            entry['result']='encoding_failed';overall['iterations'].append(entry);summary.write_text(json.dumps(overall,indent=2)+'\n');break
        cnf=stem.with_suffix('.cnf');entry['cnf_sha256']=digest(cnf);entry['cnf_bytes']=cnf.stat().st_size
        stem.with_suffix('.recipe.json').write_text(json.dumps(entry,indent=2)+'\n')
        with stem.with_suffix('.run.log').open('w') as log:completed=subprocess.run(solve,cwd=BASE,stdout=log,stderr=subprocess.STDOUT)
        entry['runner_exit']=completed.returncode
        status_path=stem.with_suffix('.status.json')
        entry['status']=json.loads(status_path.read_text()) if status_path.exists() else {'result':'runner_failed_without_status'}
        result=entry['status']['result'];entry['result']=result
        terminal=completed.returncode!=0 or result!='sat' or iteration+1==args.rounds
        if result=='sat' and completed.returncode==0:
            witness_path=stem.with_suffix('.witness.json');witness=json.loads(witness_path.read_text())
            assert not witness['full_positive_errors'] and not witness['full_singleton_errors']
            errors=witness['full_generic_negative_error_indices']
            assert not set(errors)&set(selected)
            entry['full_generic_errors']=len(errors);entry['witness_sha256']=digest(witness_path)
            if not errors:
                assert witness['is_global_counterexample_candidate']
                target=BASE/(args.tag+'.candidate.json');shutil.copyfile(witness_path,target)
                entry['result']='full_global_candidate';entry['candidate']=str(target);terminal=True
            elif not terminal:
                added=choose_rows(errors,selected,args.add_rows,negative,witness['full_generic_false_OR_counts'])
                assert added
                entry['added_generic_rows']=added
                selected=sorted(set(selected)|set(added))
                entry['result']='invalid_sample_candidate'
            else:entry['result']='invalid_sample_candidate_at_round_limit'
        elif result=='unsat':entry['result']='unsat_pinned_template_selected_rows'
        if iteration==0 or terminal:
            entry['retained_compressed_cnf']=preserve_key_cnf(cnf,entry['cnf_sha256'])
        else:
            assert stem.with_suffix('.recipe.json').is_file() and rows.is_file()
            cnf.unlink();entry['cnf_storage']='reproducible_from_preserved_recipe_sources_seed_rows_and_hash'
        entry['finished_utc']=datetime.now(timezone.utc).isoformat()
        overall['iterations'].append(entry);overall['last_result']=entry['result']
        summary.write_text(json.dumps(overall,indent=2)+'\n')
        stem.with_suffix('.iteration.json').write_text(json.dumps(entry,indent=2)+'\n')
        print(json.dumps({'iteration':iteration,'result':entry['result'],'rows':len(entry['selected_generic_rows']),
                         'full_generic_errors':entry.get('full_generic_errors')}),flush=True)
        if terminal:break
    overall['finished_utc']=datetime.now(timezone.utc).isoformat();summary.write_text(json.dumps(overall,indent=2)+'\n')

if __name__=='__main__':main()
