"""Bounded exact search for a constant plane with tridiagonal variation.

The off-diagonal entries 01, 12, 23 are independent x,y,z; all other
off-diagonal variations vanish. Diagonal33 enforces the tangent equation.
This is one restricted support family, not the full RREF chart.
"""

import argparse
import itertools
import json
import multiprocessing
from pathlib import Path
import time

import sympy as sp


def worker(output, queue):
    start = time.monotonic()
    x, y, z = sp.symbols("x y z")
    variables = (x, y, z)
    unknowns = sp.symbols("d0:9")
    diagonal = [sum(unknowns[3*i+j] * variables[j] for j in range(3)) for i in range(3)]
    diagonal.append(-sum(diagonal) - 2*(x+y+z))
    T = sp.diag(*diagonal)
    for (i,j), value in zip([(0,1),(1,2),(2,3)], variables):
        T[i,j] = T[j,i] = value
    permanent = sp.Poly(sp.expand(sum(sp.prod(1+T[i,p[i]] for i in range(4))
                        for p in itertools.permutations(range(4))) - 24), *variables)
    equations = permanent.coeffs()
    assert all(sum(power) in (2,3,4) for power in permanent.monoms())
    preliminary = {"support": [[0,1],[1,2],[2,3]], "matrix": str(T),
        "unknowns": [str(v) for v in unknowns], "monomials": permanent.monoms(),
        "equations": [str(p) for p in equations], "equation_count": len(equations)}
    Path(output).write_text(json.dumps(preliminary, indent=2) + "\n")
    print(json.dumps({"stage": "generated", "unknowns": len(unknowns),
                     "equations": len(equations), "seconds": time.monotonic()-start}), flush=True)
    basis = sp.groebner(equations, *unknowns, order="grevlex", domain=sp.QQ)
    result = {"stage": "completed", "seconds": time.monotonic()-start,
              "basis": [str(p.as_expr()) for p in basis.polys],
              "unit_ideal": len(basis.polys)==1 and basis.polys[0].as_expr()==1}
    queue.put(result)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=int, default=120)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    queue = multiprocessing.Queue()
    process = multiprocessing.Process(target=worker, args=(args.output, queue))
    process.start()
    process.join(args.seconds)
    if process.is_alive():
        process.terminate()
        process.join()
        result = {"stage": "UNKNOWN", "wall_limit_seconds": args.seconds}
    elif process.exitcode:
        result = {"stage": "ERROR", "exit": process.exitcode}
    else:
        result = queue.get()
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
