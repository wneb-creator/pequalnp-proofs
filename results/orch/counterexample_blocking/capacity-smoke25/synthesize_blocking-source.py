"""Standard circuit CEGIS with independently checked single-reader cuts.

This search is separate from the exact official LRAT encoding. UNSAT here is
only an external solver result until a corresponding Lean certificate exists.
"""
import argparse
import hashlib
import importlib.util
import json
import random
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
CUT_DIR = Path('/tmp/oec/pequalnp-pilot-85/linear_network/star-cut')
sys.path.insert(0, str(CUT_DIR))
spec = importlib.util.spec_from_file_location('standard_synthesis', HERE / 'synthesize.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)
from blocking_cuts_compact import add_blocking_compact
from reader_capacity import add_reader_capacity


def make(samples, gates, not_count=None, capacity=False):
    cnf, schema = s.make(samples, gates, cone=True, ordered=True, distinct=True,
                         no_constants=True, not_count=not_count)
    # Sample auxiliaries occupy the last variables BEFORE adding the cuts.
    # The old phase-hint offset must use this saved count.
    base_variables = cnf.n
    stats = add_blocking_compact(cnf, schema, [])
    if capacity:
        stats['reader_capacity'] = add_reader_capacity(cnf, schema, input_count=s.N)
    return cnf, schema, base_variables, stats


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--gates', type=int, default=24)
    p.add_argument('--seconds', type=int, default=300)
    p.add_argument('--total-seconds', type=int, default=300)
    p.add_argument('--rounds', type=int, default=20)
    p.add_argument('--not-count', type=int)
    p.add_argument('--capacity', action='store_true')
    p.add_argument('--hint')
    p.add_argument('--samples', default=str(HERE / 'all-negative.json'))
    p.add_argument('--solver', required=True)
    p.add_argument('--profile', choices=['default', 'sat', 'unsat'], default='sat')
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('--out', required=True)
    args = p.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    sources = [Path(__file__), HERE / 'synthesize.py',
               CUT_DIR / 'blocking_cuts.py', CUT_DIR / 'blocking_cuts_compact.py',
               CUT_DIR / 'search.py', CUT_DIR / 'synthesize_reference.py',
               CUT_DIR / 'reader_capacity.py']
    hashes = {}
    for source in sources:
        text = source.read_bytes()
        (out / (source.stem + '-source.py')).write_bytes(text)
        hashes[str(source)] = hashlib.sha256(text).hexdigest()
    (out / 'source-hashes.json').write_text(json.dumps(hashes, indent=2) + '\n')
    samples = set(x for x in range(1 << s.N) if x.bit_count() <= 2)
    samples.update(json.loads(Path(args.samples).read_text()))
    rng = random.Random(9811)
    seed = json.loads(Path(args.hint).read_text())['gates'] if args.hint else None
    started = time.monotonic()
    for r in range(args.rounds):
        rows = sorted(samples)
        cnf, schema, base_variables, stats = make(rows, args.gates, args.not_count, args.capacity)
        path = out / f'round-{r:03d}.cnf'
        cnf.write(path)
        (out / f'round-{r:03d}-schema.json').write_text(json.dumps(schema))
        (out / f'round-{r:03d}-samples.json').write_text(json.dumps(rows))
        metadata = {'round': r, 'samples': len(rows), 'variables': cnf.n,
                    'base_variables': base_variables, 'clauses': len(cnf.clauses),
                    'cuts': stats, 'not_count_restriction': args.not_count,
                    'scope': 'Custom synthesis plus checked reader cuts; not official LRAT formula'}
        (out / f'round-{r:03d}-metadata.json').write_text(json.dumps(metadata, indent=2))
        print(json.dumps(metadata), flush=True)
        hint_path = None
        if seed is not None:
            hints = s.phase_hints(schema, seed, rows, base_variables)
            assert all(1 <= abs(v) <= base_variables for v in hints)
            hint_path = out / f'round-{r:03d}-phases.txt'
            hint_path.write_text(' '.join(map(str, hints)) + '\n')
            (out / f'round-{r:03d}-phase-seed.json').write_text(json.dumps({'gates': seed}))
        del cnf
        if args.prepare_only:
            print('Prepared; no solver launched', flush=True)
            return
        remaining = int(args.total_seconds - (time.monotonic() - started))
        if remaining <= 0:
            print('UNKNOWN: total time budget exhausted', flush=True)
            return
        command = [args.solver, '--' + args.profile, '-t',
                   str(min(args.seconds, remaining)), str(path)]
        if hint_path is not None:
            command += ['--phase-file', str(hint_path)]
        log = out / f'round-{r:03d}.solver.log'
        with log.open('w') as f:
            proc = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
        print('solver exit', proc.returncode, 'elapsed', round(time.monotonic() - started, 2), flush=True)
        if proc.returncode != 10:
            print('UNSAT for this custom formula; no Lean certificate' if proc.returncode == 20
                  else 'UNKNOWN', flush=True)
            return
        model = {int(v) for line in log.read_text().splitlines() if line.startswith('v ')
                 for v in line[2:].split() if int(v) > 0}
        gates = s.decode(model, schema)
        delta = s.evaluate(gates)
        errors = [x for x in range(1 << s.N) if delta >> x & 1]
        assert not set(errors) & samples, 'Decoded circuit violates a sampled row'
        result = {'gates': gates, 'output': s.N + len(gates) - 1,
                  'gate_count': len(gates), 'errors': len(errors), 'counterexamples': errors}
        (out / f'round-{r:03d}-candidate.json').write_text(json.dumps(result, indent=2))
        print('full truth-table mismatches', len(errors), flush=True)
        if not errors:
            if len(gates) <= 24:
                (out / 'FOUND.json').write_text(json.dumps(result, indent=2))
                print('FOUND exact circuit with at most24 gates', flush=True)
            return
        samples.update(errors[:32])
        samples.update(rng.sample(errors, min(32, len(errors))))
        seed = gates
    print('UNKNOWN: round budget exhausted', flush=True)


if __name__ == '__main__':
    main()
