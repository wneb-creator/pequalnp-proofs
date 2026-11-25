from pathlib import Path
import argparse, json, subprocess, time

SCRATCH = Path('/tmp/oec/pequalnp-pilot-64')
SOLVER = SCRATCH / 'toolchain/lean-4.36.0-linux/bin/cadical'

class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def new(self):
        self.n += 1
        return self.n

    def add(self, *clause):
        self.clauses.append(list(clause))

    def conjunction(self, a, b):
        c = self.new()
        self.add(-c, a)
        self.add(-c, b)
        self.add(c, -a, -b)
        return c

    def disjunction(self, xs):
        c = self.new()
        self.add(-c, *xs)
        for x in xs:
            self.add(c, -x)
        return c

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for c in self.clauses:
                f.write(' '.join(map(str,c)) + ' 0\n')

def graph_case(name):
    if name == 'matching3':
        m, differences = 3, [0]
    elif name == 'cycle6':
        m, differences = 3, [0,1]
    elif name == 'cycle8':
        m, differences = 4, [0,1]
    elif name == 'fano':
        m, differences = 7, [0,1,3]
    elif name == 'plane3':
        m, differences = 13, [0,1,3,9]
    else:
        raise ValueError(name)
    row = [sum(1 << j for j in range(m) if (i-j)%m in differences) for i in range(m)]
    positives = [(1 << i) | (1 << (m+j)) for i in range(m) for j in range(m) if row[i] >> j & 1]
    negatives = []
    full = (1 << m)-1
    for a in range(1 << m):
        hood = 0
        for i in range(m):
            if a >> i & 1:
                hood |= row[i]
        b = full ^ hood
        closure = sum(1 << i for i in range(m) if row[i] & b == 0)
        if closure == a:
            negatives.append(a | (b << m))
    return 2*m, positives, negatives

def encode(n, k, positives, negatives, sym_first=False, reduced=False):
    cnf = CNF()
    sides = [[[cnf.new() for _ in range(n+g)] for _ in range(2)] for g in range(k)]
    outputs = [cnf.new() for _ in range(k)]
    cnf.add(*outputs)
    for g in range(k):
        for s in range(2):
            cnf.add(*sides[g][s])
        for i in range(n+g if reduced else n):
            cnf.add(-sides[g][0][i], -sides[g][1][i])
        if reduced:
            cnf.add(outputs[g], *(sides[h][s][n+g] for h in range(g+1,k) for s in range(2)))
    if sym_first:
        cnf.add(sides[0][0][0])
        cnf.add(sides[0][1][n//2])
    positive_vals = []
    for mask, positive in [(a,True) for a in positives] + [(a,False) for a in negatives]:
        vals = []
        for g in range(k):
            sv = []
            for s in range(2):
                terms = [sides[g][s][i] for i in range(n) if mask >> i & 1]
                terms += [cnf.conjunction(sides[g][s][n+j],vals[j]) for j in range(g)]
                sv.append(cnf.disjunction(terms))
            vals.append(cnf.conjunction(*sv))
        if positive:
            positive_vals.append(vals)
            cnf.add(*(cnf.conjunction(o,v) for o,v in zip(outputs,vals)))
        else:
            for o,v in zip(outputs, vals):
                cnf.add(-o,-v)
    if reduced:
        for g in range(k):
            cnf.add(*(vs[g] for vs in positive_vals))
    return cnf, sides, outputs

def eval_candidate(candidate, mask):
    vals = [bool(mask >> i & 1) for i in range(candidate['n'])]
    for l,r in candidate['gates']:
        vals.append(any(vals[i] for i in l) and any(vals[i] for i in r))
    return any(vals[candidate['n']+g] for g in candidate['outputs'])

def main():
    p = argparse.ArgumentParser()
    p.add_argument('case',choices=['matching3','cycle6','cycle8','fano','plane3'])
    p.add_argument('k',type=int)
    p.add_argument('--seconds',type=int,default=60)
    p.add_argument('--full',action='store_true')
    p.add_argument('--rounds',type=int,default=20)
    p.add_argument('--proof',action='store_true')
    p.add_argument('--sym-first',action='store_true')
    p.add_argument('--reduced',action='store_true')
    p.add_argument('--dual',action='store_true')
    a = p.parse_args()
    n, positives, all_negatives = graph_case(a.case)
    if a.dual:
        full = (1 << n)-1
        positives, all_negatives = [full^t for t in all_negatives], [full^t for t in positives]
    negatives = list(all_negatives if a.full else [all_negatives[0],all_negatives[-1]])
    directory = SCRATCH / ('and-' + a.case + '-' + str(a.k) + ('-sym' if a.sym_first else '') + ('-reduced' if a.reduced else '') + ('-dual' if a.dual else ''))
    directory.mkdir(exist_ok=True)
    print(json.dumps({'case':a.case,'n':n,'ands':a.k,'positives':len(positives),'all_negatives':len(all_negatives)}),flush=True)
    for round_id in range(a.rounds):
        start = time.time()
        cnf,sides,outputs = encode(n,a.k,positives,negatives,a.sym_first,a.reduced)
        stem = directory / ('round-' + str(round_id))
        cnf.write(stem.with_suffix('.cnf'))
        cmd = [str(SOLVER),'-t',str(a.seconds),str(stem.with_suffix('.cnf'))]
        if a.proof:
            cmd.append(str(stem.with_suffix('.drat')))
        with stem.with_suffix('.stdout').open('w') as out, stem.with_suffix('.stderr').open('w') as err:
            proc = subprocess.run(cmd,stdout=out,stderr=err)
        result = {'round':round_id,'negatives':len(negatives),'variables':cnf.n,'clauses':len(cnf.clauses),'code':proc.returncode,'seconds':round(time.time()-start,2)}
        if proc.returncode == 10:
            truth = set()
            for line in stem.with_suffix('.stdout').read_text().splitlines():
                if line.startswith('v '):
                    truth.update(int(t) for t in line[2:].split() if int(t)>0)
            candidate = {'n':n,'gates':[[[i for i,v in enumerate(side) if v in truth] for side in gate] for gate in sides],
                         'outputs':[g for g,v in enumerate(outputs) if v in truth]}
            assert all(eval_candidate(candidate,t) for t in positives)
            assert not any(eval_candidate(candidate,t) for t in negatives)
            violated = [t for t in all_negatives if eval_candidate(candidate,t)]
            result['violated_negatives'] = len(violated)
            stem.with_suffix('.candidate.json').write_text(json.dumps(candidate,indent=2)+'\n')
            print(json.dumps(result),flush=True)
            if not violated:
                print('SAT exact on all minimal positives and maximal negatives',flush=True)
                return
            # Add all violated negatives: each is a genuine graph-zero input.
            negatives.extend(violated)
        else:
            print(json.dumps(result),flush=True)
            return

if __name__ == '__main__':
    main()
