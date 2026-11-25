import argparse
import itertools
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_array

OUT = Path('/tmp/oec/pequalnp-pilot-66')


def graph(name):
    if name.startswith('cycle'):
        n = int(name[5:])
        return n, sorted({tuple(sorted((i, (i + 1) % n))) for i in range(n)})
    if name == 'petersen':
        return 10, sorted({*[(i, (i + 1) % 5) for i in range(5)],
                           *[(i, i + 5) for i in range(5)],
                           *[(i + 5, (i + 2) % 5 + 5) for i in range(5)]})
    raise ValueError(name)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--graph', required=True)
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--seconds', type=float, default=120)
    args = parser.parse_args()
    n, raw_edges = graph(args.graph)
    edges = sorted({tuple(sorted(e)) for e in raw_edges})
    independent = [x for x in range(1 << n) if all(not(x >> a & 1 and x >> b & 1) for a, b in edges)]
    maximal = [x for x in independent if all(x >> v & 1 or x | (1 << v) not in independent for v in range(n))]
    alpha = max(x.bit_count() for x in independent)
    tests = [(1 << a | 1 << b, 1) for a, b in edges] + [(x, 0) for x in maximal]
    k = args.gates
    print('graph',args.graph,'n',n,'edges',edges,'alpha',alpha,'star_bound',len(edges)+n-alpha-1,flush=True)
    print('tests',len(tests),'gates',k,flush=True)
    count = 0
    def fresh():
        nonlocal count
        count += 1
        return count - 1
    op = [fresh() for _ in range(k)]
    ports = [[[fresh() for _ in range(n + j)] for _ in range(2)] for j in range(k)]
    values = [[fresh() for _ in tests] for _ in range(k)]
    operands = [[[fresh() for _ in tests] for _ in range(2)] for _ in range(k)]
    rows, cols, coefficients, lows, ups = [], [], [], [], []
    def constraint(terms, lo=-np.inf, hi=np.inf):
        r = len(lows)
        for var, coeff in terms:
            rows.append(r); cols.append(var); coefficients.append(coeff)
        lows.append(lo); ups.append(hi)
    for j in range(k):
        for port in ports[j]: constraint([(v,1) for v in port],1,1)
        constraint([(v,a) for a,v in enumerate(ports[j][0])] +
                   [(v,-a) for a,v in enumerate(ports[j][1])], hi=-1)
        for ti, (assignment, expected) in enumerate(tests):
            for pi in range(2):
                dest = operands[j][pi][ti]
                for w, selector in enumerate(ports[j][pi]):
                    if w < n:
                        if assignment >> w & 1:
                            constraint([(dest,1),(selector,-1)],lo=0)
                        else:
                            constraint([(dest,1),(selector,1)],hi=1)
                    else:
                        src = values[w-n][ti]
                        constraint([(dest,1),(src,-1),(selector,1)],hi=1)
                        constraint([(dest,-1),(src,1),(selector,1)],hi=1)
            z,u,v,a = values[j][ti],operands[j][0][ti],operands[j][1][ti],op[j]
            constraint([(z,1),(u,-1),(a,1)],hi=1)
            constraint([(z,1),(v,-1),(a,1)],hi=1)
            constraint([(z,1),(u,-1),(v,-1)],lo=-1,hi=0)
            constraint([(z,1),(u,-1),(a,1)],lo=0)
            constraint([(z,1),(v,-1),(a,1)],lo=0)
    # Minimum witnesses have no unused gates; every earlier gate is read later.
    for j in range(k-1):
        constraint([(ports[l][p][n+j],1) for l in range(j+1,k) for p in range(2)],lo=1)
    # These preset graphs are vertex transitive, so the first operand may be vertex zero.
    constraint([(ports[0][0][0],1)],1,1)
    low = np.zeros(count); high = np.ones(count)
    for ti,(_,expected) in enumerate(tests):
        low[values[-1][ti]] = high[values[-1][ti]] = expected
    matrix = coo_array((np.asarray(coefficients,dtype=float),(np.asarray(rows,dtype=np.int32),np.asarray(cols,dtype=np.int32))),shape=(len(lows),count)).tocsc()
    print('variables',count,'constraints',len(lows),'nonzeros',len(coefficients),flush=True)
    start=time.time()
    result=milp(np.zeros(count),integrality=np.ones(count),bounds=Bounds(low,high),
                constraints=LinearConstraint(matrix,np.asarray(lows),np.asarray(ups)),
                options={'time_limit':args.seconds,'node_limit':100000,'presolve':True,'disp':True})
    print('result',result,flush=True)
    summary={'graph':args.graph,'n':n,'edges':edges,'gate_count':k,'status':result.status,
             'message':result.message,'elapsed':time.time()-start,'star_bound':len(edges)+n-alpha-1}
    if result.x is not None:
        gates=[]
        for j in range(k):
            gates.append(('and' if result.x[op[j]]>.5 else 'or',
                          int(np.argmax(result.x[ports[j][0]])),int(np.argmax(result.x[ports[j][1]]))))
        valid=True
        for x in range(1<<n):
            wires=[bool(x>>i&1) for i in range(n)]
            for operation,a,b in gates:wires.append(wires[a] and wires[b] if operation=='and' else wires[a] or wires[b])
            if wires[-1] != any(x>>a&1 and x>>b&1 for a,b in edges):valid=False;break
        summary.update({'gates':gates,'all_inputs_validated':valid})
        print('WITNESS',json.dumps(summary),flush=True)
    (OUT/f'milp-{args.graph}-{k}.json').write_text(json.dumps(summary,indent=2))


if __name__=='__main__':main()
