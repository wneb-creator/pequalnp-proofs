import argparse,datetime,json,subprocess,time
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--budget',type=int,default=600)
parser.add_argument('--stage-seconds',type=int,default=120)
parser.add_argument('--max-nots',type=int,choices=[0,1])
parser.add_argument('--seed',type=int,default=154)
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-154/counterexample')
wall=time.monotonic()
history=[]
rows=None
seed=None
verdict='time_budget'
for iteration in range(64):
    remaining=int(args.budget-(time.monotonic()-wall))
    if remaining<5:break
    stem='petersen-cegar-'+str(iteration).zfill(2)
    command=['python3',str(base/'petersen_sat.py'),'--gates','18','--stem',stem]
    if rows is None:command+=['--cofactor-rows']
    else:command+=['--rows',str(rows),'--seed-gates',str(seed)]
    if args.max_nots is not None:command+=['--max-nots',str(args.max_nots)]
    with (base/(stem+'-generation.log')).open('w') as f:
        subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,check=True)
    seconds=min(args.stage_seconds,remaining)
    p=subprocess.run(['python3',str(base/'solver_limit.py'),stem,'--seconds',str(seconds),
      '--seed',str(args.seed),'--memory-mib','256'],capture_output=True,text=True,check=True)
    print(p.stdout.strip(),flush=True)
    solved=json.loads((base/(stem+'-solver-result.json')).read_text())
    metadata=json.loads((base/(stem+'.json')).read_text())
    item={'iteration':iteration,'stem':stem,'rows':len(metadata['test_rows']),
      'variables':metadata['variables'],'clauses':metadata['clauses'],'solver':solved}
    history.append(item)
    if solved['exit_code']==20:
        verdict='unsat_on_necessary_rows';break
    if solved['exit_code']!=10:
        verdict='solver_inconclusive';break
    fresh=base/(stem+'-verification.json')
    if fresh.exists():fresh.unlink()
    with (base/(stem+'-verification.log')).open('w') as f:
        checked=subprocess.run(['python3',str(base/'petersen_verify.py'),stem],stdout=f,stderr=subprocess.STDOUT)
    assert checked.returncode in [0,1]
    verified=json.loads((base/(stem+'-verification.json')).read_text())
    errors=verified['errors']
    assert checked.returncode==(1 if errors else 0)
    item['full_table_errors']=len(errors)
    if not errors:
        verdict='verified_counterexample';break
    old=set(metadata['test_rows'])
    assert not old.intersection(errors)
    selected=[]
    remaining_errors=set(errors)
    while remaining_errors and len(selected)<16:
        x=max(remaining_errors,key=lambda x:(min((x^y).bit_count() for y in old),-x))
        selected.append(x);old.add(x);remaining_errors.remove(x)
    item['added_rows']=selected
    rows=base/(stem+'-next-rows.json')
    seed=base/(stem+'-next-seed.json')
    rows.write_text(json.dumps(sorted(old)))
    seed.write_text(json.dumps(verified['gates']))
    print(json.dumps(item),flush=True)
result={'verdict':verdict,'history':history,'elapsed_seconds':time.monotonic()-wall,
  'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'max_nots':args.max_nots}
(base/'petersen-cegar-result.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
