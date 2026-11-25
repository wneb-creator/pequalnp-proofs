import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import runpy
import time

BASE = Path('/tmp/oec/pequalnp-pilot-87/counterexample')
CORE = runpy.run_path(str(BASE / 'synth.py'))
TARGET = CORE['target']
EVALUATE = CORE['evaluate']

lib = ctypes.CDLL(str(BASE / 'libcadical.so'))
lib.sat_init.argtypes = []
lib.sat_init.restype = ctypes.c_void_p
for name in ['add', 'assume', 'freeze']:
    getattr(lib, 'sat_' + name).argtypes = [ctypes.c_void_p, ctypes.c_int]
    getattr(lib, 'sat_' + name).restype = None
lib.sat_solve.argtypes = [ctypes.c_void_p]
lib.sat_solve.restype = ctypes.c_int
lib.sat_val.argtypes = [ctypes.c_void_p, ctypes.c_int]
lib.sat_val.restype = ctypes.c_int
lib.sat_set_option.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int]
lib.sat_set_option.restype = None
lib.sat_release.argtypes = [ctypes.c_void_p]
lib.sat_release.restype = None
CALLBACK = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p)
lib.sat_set_terminate.argtypes = [ctypes.c_void_p, ctypes.c_void_p, CALLBACK]


def add_row(cnf, row, typ, left, right):
    gates = len(typ)
    values = [cnf.var() for _ in range(11 + gates)]
    cnf.clause(-values[0])
    for a in range(10):
        cnf.clause(values[a + 1] if row >> a & 1 else -values[a + 1])
    for i in range(gates):
        p, q = cnf.var(), cnf.var()
        v = values[11 + i]
        for j, select in enumerate(left[i]):
            cnf.clause(-select, -p, values[j])
            cnf.clause(-select, p, -values[j])
        for j, select in enumerate(right[i]):
            cnf.clause(-select, -q, values[j])
            cnf.clause(-select, q, -values[j])
        a, o, n = typ[i]
        cnf.clause(-a, -v, p)
        cnf.clause(-a, -v, q)
        cnf.clause(-a, v, -p, -q)
        cnf.clause(-o, v, -p)
        cnf.clause(-o, v, -q)
        cnf.clause(-o, -v, p, q)
        cnf.clause(-n, -v, -p)
        cnf.clause(-n, v, p)
    cnf.clause(values[-1] if TARGET(row) else -values[-1])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--gates', type=int, default=19)
    parser.add_argument('--notmax', type=int, default=1)
    parser.add_argument('--seconds', type=int, default=180)
    parser.add_argument('--first', default='1,1,3')
    parser.add_argument('--seed', type=int, default=237387)
    parser.add_argument('--ordered', action='store_true')
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    positives = [1 << a | 1 << b for a, b in CORE['EDGES']]
    negatives = [r for r in range(1024) if not TARGET(r) and all(
        TARGET(r | 1 << a) for a in range(10) if not r >> a & 1)]
    assert len(set(positives)) == len(negatives) == 15
    rows = set(positives + negatives + [0, 1023])
    first = tuple(map(int, args.first.split(','))) if args.first else None
    cnf, typ, left, right = CORE['encode'](
        [], args.gates, first, args.notmax == 0, True, args.ordered,
        irredundant=True, notmax=args.notmax, roots_last=True)
    for row in sorted(rows):
        add_row(cnf, row, typ, left, right)
    # The original encoder and incremental row encoder must be identical.
    reference = CORE['encode'](
        sorted(rows), args.gates, first, args.notmax == 0, True, args.ordered,
        irredundant=True, notmax=args.notmax, roots_last=True)[0]
    assert cnf.nvars == reference.nvars and cnf.clauses == reference.clauses
    del reference
    start = time.monotonic()
    deadline = start + args.seconds

    @CALLBACK
    def terminated(_):
        return int(time.monotonic() >= deadline)

    solver = lib.sat_init()
    lib.sat_set_option(solver, b'quiet', 1)
    lib.sat_set_option(solver, b'seed', args.seed)
    lib.sat_set_terminate(solver, None, terminated)
    selectors = [v for groups in [typ, left, right] for group in groups for v in group]
    for v in selectors:
        lib.sat_freeze(solver, v)

    def install():
        count = len(cnf.clauses)
        for clause in cnf.clauses:
            for lit in clause:
                lib.sat_add(solver, lit)
            lib.sat_add(solver, 0)
        cnf.clauses.clear()
        return count

    print('configuration', vars(args), flush=True)
    print('encoder_sha256', hashlib.sha256((BASE / 'synth.py').read_bytes()).hexdigest(), flush=True)
    print('initial rows', len(rows), 'vars', cnf.nvars, 'clauses', install(), flush=True)
    iteration = 0
    try:
        while time.monotonic() < deadline:
            result = lib.sat_solve(solver)
            print('round', iteration, 'result', result, 'elapsed', time.monotonic() - start, flush=True)
            if result != 10:
                print('BOUNDED_SEARCH_UNSAT' if result == 20 else 'UNKNOWN', flush=True)
                return
            def chosen(vs):
                return next(i for i, v in enumerate(vs) if lib.sat_val(solver, v) > 0)
            gates = [(chosen(typ[i]), chosen(left[i]), chosen(right[i])) for i in range(args.gates)]
            bad = [r for r in range(1024) if EVALUATE(gates, r)[-1] != TARGET(r)]
            assert not rows.intersection(bad)
            (out / ('round-' + str(iteration) + '.json')).write_text(json.dumps({'gates': gates, 'bad': bad}))
            print('bad truth rows', len(bad), flush=True)
            if not bad:
                a, b = gates[-1][1:]
                first_witness = [r for r in range(1024) if EVALUATE(gates, r)[a] and not EVALUATE(gates, r)[b]]
                second_witness = [r for r in range(1024) if EVALUATE(gates, r)[b] and not EVALUATE(gates, r)[a]]
                result = {'gates': gates, 'exclusive_witnesses': [first_witness, second_witness]}
                (out / 'full-witness.json').write_text(json.dumps(result))
                print('FULL_FUNCTION', gates, 'exclusive counts', len(first_witness), len(second_witness), flush=True)
                return
            # Add a spread of counterexamples, retaining the solver's learned clauses.
            selected = sorted(bad, key=lambda r: (r.bit_count(), r))
            chosen_rows = selected[:8] + selected[-8:]
            for row in sorted(set(chosen_rows)):
                rows.add(row)
                add_row(cnf, row, typ, left, right)
            print('rows', len(rows), 'new clauses', install(), flush=True)
            iteration += 1
    finally:
        lib.sat_release(solver)


if __name__ == '__main__':
    main()
