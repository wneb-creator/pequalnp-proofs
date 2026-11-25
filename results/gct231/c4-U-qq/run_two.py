from pathlib import Path
import json
import resource
import subprocess

base = Path(__file__).resolve().parent
job = base.parent

def verification_limits():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_FSIZE, (256 * 1024**2, 256 * 1024**2))

def verify_stage(command, logfile):
    with logfile.open('w') as output:
        try:
            result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT,
                                    preexec_fn=verification_limits, timeout=120)
            return {'returncode': result.returncode, 'status': 'PASS' if result.returncode == 0 else 'FAILED_NO_CERTIFICATE'}
        except subprocess.TimeoutExpired:
            return {'status': 'UNKNOWN_TIME_LIMIT'}

for case in (2, 3):
    source = job / ('neogb-c4-Usaturated' + str(case) + '-qq.in')
    prefix = base / ('case' + str(case))
    with prefix.with_suffix('.driver.log').open('w') as output:
        result = subprocess.run(['python3', str(job / 'sparse-engine/run_neogb_trace_primitive.py'),
                                 str(source), str(prefix), '--seconds', '120', '--memory-mib', '1024',
                                 '--pairs', '32', '--output-mib', '256'],
                                stdout=output, stderr=subprocess.STDOUT)
    assert result.returncode == 0
    status = json.loads(prefix.with_suffix('.run.json').read_text())
    print(case, status['status'], status['wall_seconds'], flush=True)
    if status['status'] != 'COMPLETED':
        continue
    sliced = base / ('case' + str(case) + '-slice.trace')
    stages = {}
    stages['slice'] = verify_stage(['python3', str(job / 'slice_neogb_trace.py'),
                                   str(prefix.with_suffix('.trace')), str(sliced)],
                                  base / ('case' + str(case) + '-slice.log'))
    if stages['slice']['status'] == 'PASS':
        certificate = base / ('case' + str(case) + '.certificate.json')
        stages['replay'] = verify_stage(['python3', str(job / 'replay_neogb_compact.py'),
                                        str(prefix.with_suffix('.f4.in')), str(sliced), str(certificate)],
                                       base / ('case' + str(case) + '-replay.log'))
        if stages['replay']['status'] == 'PASS':
            data = json.loads(certificate.read_text())
            print(case, {'unit_replayed': data['proved_nonzero_constant'],
                         'needed_steps': len(data['needed_steps'])}, flush=True)
    prefix.with_suffix('.verification.json').write_text(json.dumps(stages, indent=2) + '\n')
