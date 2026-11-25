import argparse
import hashlib
import itertools
import json
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


EDGES = [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(3,8),(4,6),(6,8),(8,5),(5,7),(7,4)]
NEGATIVE = [25,52,58,69,100,104,138,201,274,277,385,386]
POSITIVE = [(1 << a) | (1 << b) for a,b in EDGES]
ROWS = sorted(POSITIVE + NEGATIVE)
FULL_EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]


def target(x):
    return any(x >> a & 1 and x >> b & 1 for a,b in EDGES)


def initial(x, free):
    return [bool(x >> j & 1) for j in range(9)] + [any(x >> j & 1 for j in free)]


def evaluate(gates, values):
    values = list(values)
    for i,(op,a,b) in enumerate(gates):
        assert op in (0,1) and 0 <= a < len(values) and 0 <= b < len(values), (i,op,a,b)
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    return values


def full_lift(gates, free):
    # Output indices in this returned ordinary circuit start at ten.
    f = sorted(free)
    assert set(f) <= {0,3,4} and len(f) in (2,3)
    lifted = [(1,f[0]+1,f[1]+1)]
    if len(f) == 3:
        lifted.append((1,10,f[2]+1))
    helper = 10 + len(lifted) - 1
    start = 10 + len(lifted)
    def wire(i):
        if i < 9:
            return i+1
        if i == 9:
            return helper
        return start+i-10
    lifted.extend((op,wire(a),wire(b)) for op,a,b in gates)
    cofactor_output = 10 + len(lifted) - 1
    if len(f) == 2:
        third = next(j for j in (0,3,4) if j not in f)
        lifted.append((1,helper,third+1))
        helper = 10 + len(lifted) - 1
    lifted.append((0,0,helper))
    star = 10 + len(lifted) - 1
    lifted.append((1,cofactor_output,star))
    return lifted


def validate(gates, free):
    wrong = [x for x in range(512) if evaluate(gates,initial(x,free))[-1] != target(x)]
    lifted = full_lift(gates,free)
    wrong_lift = [x for x in range(1024) if
        evaluate(lifted,[bool(x >> i & 1) for i in range(10)])[-1] !=
        any(x >> a & 1 and x >> b & 1 for a,b in FULL_EDGES)]
    # The posted input list has an extra free negation at index ten.
    def shift(i):
        return i if i < 10 else i+1
    posted = [(op,shift(a),shift(b)) for op,a,b in lifted]
    wrong_posted = [x for x in range(1024) if
        evaluate(posted,[bool(x >> i & 1) for i in range(10)]+[not bool(x&1)])[-1] !=
        any(x >> a & 1 and x >> b & 1 for a,b in FULL_EDGES)]
    return dict(cofactor_rows_checked=512, wrong_cofactor=wrong,
                ordinary_lift_gates=lifted, ordinary_lift_size=len(lifted),
                lift_rows_checked=1024, wrong_lift=wrong_lift,
                posted_lift_gates=posted, posted_rows_checked=1024,
                wrong_posted=wrong_posted)


class CNF:
    def __init__(self):
        self.nv, self.cs = 0, []
    def var(self):
        self.nv += 1
        return self.nv
    def clause(self,*xs):
        self.cs.append(tuple(xs))
    def one(self,xs):
        self.clause(*xs)
        for a,b in itertools.combinations(xs,2):
            self.clause(-a,-b)
    def write(self,path):
        with path.open('w') as stream:
            stream.write(f'p cnf {self.nv} {len(self.cs)}\n')
            for clause in self.cs:
                stream.write(' '.join(map(str,clause))+' 0\n')


def main():
    parser = argparse.ArgumentParser(description='Exact Petersen vertex-deletion monotone synthesis with one free neighbor OR.')
    parser.add_argument('--free', required=True, help='Comma-separated natural9 coordinates, e.g. 0,3 or 0,3,4')
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--pin')
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--require-helper', action='store_true')
    parser.add_argument('--productive', action='store_true')
    parser.add_argument('--primary-minimal', action='store_true')
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--sat-preset', action='store_true')
    parser.add_argument('--outdir', default=str(Path(__file__).resolve().parent))
    parser.add_argument('--scratch', default='/tmp/oec/pequalnp-pilot-103/orch1884-free-neighbor-or')
    args = parser.parse_args()
    free = tuple(map(int,args.free.split(',')))
    assert len(set(free)) == len(free) and len(free) in (2,3) and set(free) <= {0,3,4}
    assert 1 <= args.gates <= 32 and args.seconds >= 1
    out = Path(args.outdir)
    scratch = Path(args.scratch)
    out.mkdir(parents=True,exist_ok=True)
    scratch.mkdir(parents=True,exist_ok=True)
    n,N = 10,args.gates
    started = datetime.now(timezone.utc).isoformat()
    clock = time.monotonic()
    # Verify that every raw source is semantically essential even in the
    # presence of the free OR. This licenses requiring a direct use of it.
    essential = {}
    for j in range(9):
        for x in range(512):
            y = x ^ (1 << j)
            if target(x) == target(y):
                continue
            vx,vy = initial(x,free),initial(y,free)
            if all(vx[k] == vy[k] for k in range(n) if k != j):
                essential[j] = [x,y]
                break
        assert j in essential, ('source essentiality not established',j)
    c = CNF()
    A,B,O = [],[],[]
    for i in range(N):
        A.append([c.var() for _ in range(n+i)])
        B.append([c.var() for _ in range(n+i)])
        O.append(c.var())
        c.one(A[i]);c.one(B[i])
        for a in range(n+i):
            for b in range(a):
                c.clause(-A[i][a],-B[i][b])
    for i in range(N-1):
        c.clause(*(v for j in range(i+1,N) for v in (A[j][n+i],B[j][n+i])))
    for source in list(range(9)) + ([9] if args.require_helper else []):
        c.clause(*(v for j in range(N) for v in (A[j][source],B[j][source])))
    if args.pin:
        pin = json.loads(Path(args.pin).read_text())
        if isinstance(pin,dict):
            pin = pin['gates']
        assert len(pin) == N
        for i,(op,a,b) in enumerate(pin):
            a,b = sorted((a,b))
            assert op in (0,1) and 0 <= a <= b < n+i
            c.clause(O[i] if op else -O[i]);c.clause(A[i][a]);c.clause(B[i][b])
    V = {}
    for x in ROWS:
        fixed = initial(x,free)
        values = []
        for i in range(N):
            u,v,w = c.var(),c.var(),c.var()
            for source in range(n+i):
                for selectors,dest in ((A[i],u),(B[i],v)):
                    if source < n:
                        c.clause(-selectors[source],dest if fixed[source] else -dest)
                    else:
                        z = values[source-n]
                        c.clause(-selectors[source],-dest,z)
                        c.clause(-selectors[source],dest,-z)
            op = O[i]
            c.clause(op,-u,-v,w);c.clause(op,u,-w);c.clause(op,v,-w)
            c.clause(-op,u,v,-w);c.clause(-op,-u,w);c.clause(-op,-v,w)
            values.append(w)
        c.clause(values[-1] if target(x) else -values[-1])
        V[x] = values
    if args.productive:
        for i in range(N):
            c.clause(*(V[x][i] for x in POSITIVE))
    if args.primary_minimal:
        for i in range(N):
            for source in range(n):
                differences = [V[x][i] if not initial(x,free)[source] else -V[x][i] for x in POSITIVE]
                increases = [-V[x][i] for x in NEGATIVE if initial(x,free)[source]]
                c.clause(*(differences+increases))
    if args.fresh:
        for i in range(N):
            vals = [V[x][i] for x in ROWS]
            c.clause(*vals);c.clause(*(-v for v in vals))
            for source in range(n):
                c.clause(*(v if not initial(x,free)[source] else -v for x,v in zip(ROWS,vals)))
            for j in range(i):
                diffs = []
                for x in ROWS:
                    u,v,d = V[x][j],V[x][i],c.var()
                    diffs.append(d)
                    c.clause(-d,u,v);c.clause(-d,-u,-v)
                    c.clause(d,u,-v);c.clause(d,-u,v)
                c.clause(*diffs)
    cnf = scratch/(args.tag+'.cnf')
    c.write(cnf)
    result = dict(started_at=started, arguments=vars(args), source_functions=[{'raw':j} for j in range(9)]+[{'or':list(free)}],
                  rows=ROWS, positive=POSITIVE, negative=NEGATIVE, raw_source_witnesses=essential,
                  variables=c.nv,clauses=len(c.cs),cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(),
                  strict_earlier_wires=True, paid_gate_count=N,
                  scope='Exact monotone nine-input cofactor with the specified free OR; not directly the posted gap.')
    print('PREPARED',json.dumps(result),flush=True)
    if args.prepare_only:
        result.update(status='PREPARED_NOT_RUN',elapsed_seconds=time.monotonic()-clock)
    else:
        solver = '/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical'
        command = [solver,'-t',str(args.seconds),'--seed='+str(args.seed)]
        if args.sat_preset:
            command.append('--sat')
        command.append(str(cnf))
        stdout,stderr = out/(args.tag+'.stdout'),out/(args.tag+'.stderr')
        with stdout.open('w') as sout,stderr.open('w') as serr:
            try:
                run = subprocess.run(command,stdout=sout,stderr=serr,timeout=args.seconds+10)
                code = run.returncode
            except subprocess.TimeoutExpired:
                code = 'external timeout'
        text = stdout.read_text()
        status = 'SAT' if 's SATISFIABLE' in text else 'UNSAT' if 's UNSATISFIABLE' in text else 'UNKNOWN'
        result.update(status=status,exit=code,solver_arguments=command[1:],elapsed_seconds=time.monotonic()-clock)
        if status == 'SAT':
            positive_model = {int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
            gates = [(int(O[i] in positive_model),next(j for j,v in enumerate(A[i]) if v in positive_model),
                      next(j for j,v in enumerate(B[i]) if v in positive_model)) for i in range(N)]
            result.update(gates=gates,validation=validate(gates,free))
            assert not result['validation']['wrong_cofactor'],result
            assert not result['validation']['wrong_lift'],result
            assert not result['validation']['wrong_posted'],result
            (out/(args.tag+'-witness.json')).write_text(json.dumps(result,indent=2)+'\n')
            print('VALIDATED_WITNESS',json.dumps(result),flush=True)
    result['finished_at'] = datetime.now(timezone.utc).isoformat()
    (out/(args.tag+'-result.json')).write_text(json.dumps(result,indent=2)+'\n')
    print('RESULT',json.dumps(result),flush=True)


if __name__ == '__main__':
    main()
