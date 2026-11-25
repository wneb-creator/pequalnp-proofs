import argparse
import hashlib
import json
import resource
import subprocess
import time
from datetime import datetime,timezone
from pathlib import Path

from joint_decode import decode


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf',type=Path,required=True)
    parser.add_argument('--phases',type=Path,required=True)
    parser.add_argument('--prefix',type=Path,required=True)
    parser.add_argument('--seconds',type=int,required=True)
    parser.add_argument('--helper',type=Path,default=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/phased'))
    parser.add_argument('--driver-source',type=Path,default=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/phased.cpp'))
    args = parser.parse_args()
    assert args.seconds > 0
    cnf = args.cnf.resolve()
    phases_path = args.phases.resolve()
    map_path = cnf.with_suffix('.map.json')
    model = json.loads(map_path.read_text())
    assert model['format'] == 'joint-correlated-v1'
    assert Path(model['cnf_file']).resolve() == cnf
    cnf_hash = sha256(cnf)
    assert cnf_hash == model['cnf_sha256']
    with cnf.open() as source:
        first_line = source.readline().split()
    assert first_line == ['p','cnf',str(model['nv']),str(model['clauses'])]
    literals = [int(word) for word in phases_path.read_text().split()]
    assert literals, 'Empty phase file'
    preferences = {}
    for literal in literals:
        assert literal != 0, 'Zero phase literal'
        variable,value = abs(literal),literal > 0
        assert variable <= model['nv'], 'Phase variable outside CNF range'
        assert variable not in preferences or preferences[variable] == value, 'Conflicting phase duplicates'
        preferences[variable] = value
    runpath = Path(str(args.prefix)+'-run.json')
    resultpath = Path(str(args.prefix)+'-result.json')
    solve_log = Path(str(args.prefix)+'-solve.log')
    checked_path = Path(str(args.prefix)+'-verified.json')
    witness_path = Path(str(args.prefix)+'-witness.json')
    assert not any(path.exists() for path in (runpath,resultpath,solve_log,checked_path,witness_path))
    command = [str(args.helper.resolve()),str(cnf),str(phases_path),str(args.seconds)]
    stamp = lambda:datetime.now(timezone.utc).isoformat()
    metadata = dict(started_at=stamp(),wall_limit_seconds=args.seconds,command=command,
                    backend='cadical-phased',configuration='sat',
                    cnf_sha256=cnf_hash,map_sha256=sha256(map_path),
                    phases_sha256=sha256(phases_path),helper_sha256=sha256(args.helper),
                    driver_source_sha256=sha256(args.driver_source),
                    wrapper_source_sha256=sha256(Path(__file__)),
                    decoder_source_sha256=sha256(Path(__file__).with_name('joint_decode.py')),
                    phase_literals=len(literals),distinct_phase_variables=len(preferences),
                    repeated_identical_phase_literals=len(literals)-len(preferences),
                    phase_semantics='Soft solver.phase preferences only; no assumptions or added clauses.')
    runpath.write_text(json.dumps(metadata,indent=2)+'\n')
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with solve_log.open('w') as stream:
        started = time.monotonic()
        code = subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT).returncode
        elapsed = time.monotonic()-started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = dict(metadata,finished_at=stamp(),wall_seconds=elapsed,
                  cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                  max_rss_kib=after.ru_maxrss,exit_code=code,
                  status={0:'UNKNOWN',10:'SAT',20:'UNSAT'}.get(code,'ERROR'))
    if code == 10:
        verification_started = time.monotonic()
        try:
            checked = decode(map_path,solve_log,checked_path)
            witness_path.write_text(json.dumps(checked['full_gates'],indent=2)+'\n')
            result.update(full_truth_table_verified=True,witness_file=str(witness_path),
                          selected_branch=checked['selected_branch_index'],
                          selected_variant=checked['selected_variant'],
                          full_gate_count=checked['full_gate_count'],
                          checked_cnf_clauses=checked['checked_cnf_clauses'],
                          checked_residual_assignments=checked['checked_residual_assignments'],
                          checked_full_assignments=checked['checked_full_assignments'])
        except Exception as error:
            result.update(full_truth_table_verified=False,verification_error=repr(error))
        result['verification_wall_seconds'] = time.monotonic()-verification_started
    assert sha256(cnf) == cnf_hash, 'CNF changed during solve'
    resultpath.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__ == '__main__':
    main()
