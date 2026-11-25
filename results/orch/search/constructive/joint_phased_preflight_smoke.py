import argparse
import json
import subprocess
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf',type=Path,required=True)
    parser.add_argument('--prefix',type=Path,required=True)
    args = parser.parse_args()
    metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
    cases = [('zero','0\n','Zero phase literal'),
             ('outside',str(metadata['nv']+1)+'\n','Phase variable outside CNF range'),
             ('conflict','1\n-1\n','Conflicting phase duplicates')]
    results = []
    for name,contents,message in cases:
        prefix = Path(str(args.prefix)+'-'+name)
        phase = Path(str(prefix)+'.phases')
        log = Path(str(prefix)+'.log')
        assert not phase.exists() and not log.exists()
        phase.write_text(contents)
        command = [sys.executable,str(Path(__file__).with_name('joint_phased_run.py')),
                   '--cnf',str(args.cnf),'--phases',str(phase),'--prefix',str(prefix),'--seconds','1']
        with log.open('w') as stream:
            code = subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT).returncode
        assert code != 0 and message in log.read_text()
        assert not Path(str(prefix)+'-run.json').exists()
        assert not Path(str(prefix)+'-solve.log').exists()
        results.append(dict(case=name,exit_code=code,solver_not_started=True,expected_error=message))
    report = dict(all_passed=True,cases=results)
    Path(str(args.prefix)+'-result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
