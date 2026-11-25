import argparse
import hashlib
import json
import resource
import subprocess
import time
from datetime import datetime,timezone
from pathlib import Path

from joint_decode import decode


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf',type=Path,required=True)
    parser.add_argument('--prefix',type=Path,required=True)
    parser.add_argument('--seconds',type=int,required=True)
    parser.add_argument('--preset',choices=('default','sat','unsat'),default='default')
    parser.add_argument('--seed',type=int,default=1)
    parser.add_argument('--solver',type=Path,default=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/kissat/build/kissat'))
    args = parser.parse_args()
    assert args.seconds > 0 and args.seed >= 0
    runpath = Path(str(args.prefix)+'-run.json')
    resultpath = Path(str(args.prefix)+'-result.json')
    solve_log = Path(str(args.prefix)+'-solve.log')
    assert not runpath.exists() and not resultpath.exists() and not solve_log.exists()
    command = [str(args.solver),'-s',f'--time={args.seconds}',f'--seed={args.seed}']
    if args.preset != 'default':
        command.append('--'+args.preset)
    command.append(str(args.cnf.resolve()))
    stamp = lambda:datetime.now(timezone.utc).isoformat()
    metadata = dict(started_at=stamp(),wall_limit_seconds=args.seconds,command=command,
                    cnf_sha256=hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
                    map_sha256=hashlib.sha256(args.cnf.with_suffix('.map.json').read_bytes()).hexdigest(),
                    solver_sha256=hashlib.sha256(args.solver.read_bytes()).hexdigest(),
                    backend='kissat',preset=args.preset,seed=args.seed)
    runpath.write_text(json.dumps(metadata,indent=2)+'\n')
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    with solve_log.open('w') as stream:
        code = subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT).returncode
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = dict(metadata,finished_at=stamp(),wall_seconds=time.monotonic()-started,
                  cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                  max_rss_kib=after.ru_maxrss,exit_code=code,
                  status={0:'UNKNOWN',10:'SAT',20:'UNSAT'}.get(code,'ERROR'))
    if code == 10:
        checked_path = Path(str(args.prefix)+'-verified.json')
        try:
            checked = decode(args.cnf.with_suffix('.map.json'),solve_log,checked_path)
            witness = Path(str(args.prefix)+'-witness.json')
            witness.write_text(json.dumps(checked['full_gates'],indent=2)+'\n')
            result.update(full_truth_table_verified=True,witness_file=str(witness),
                          selected_branch=checked['selected_branch_index'],
                          selected_variant=checked['selected_variant'],
                          full_gate_count=checked['full_gate_count'])
        except Exception as error:
            result.update(full_truth_table_verified=False,verification_error=repr(error))
    resultpath.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__ == '__main__':
    main()
