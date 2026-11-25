"""Explore three-planes in the row-sum-zero ansatz; no Lean claim.

Each worker receives a wall-time cap. Full output goes to the caller log.
The eight charts choose one coordinate from each hyperbolic pair.
"""

import argparse
import itertools
import json
import multiprocessing
import time

import sympy as sp


def rowzero_coefficients():
    a, b, c, d, e, f, z = sp.symbols("a b c d e f z")
    A = sp.Matrix([[a, d, e], [d, b, f], [e, f, c]])
    V = sp.Matrix([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]])
    T = V * A * V.T
    permanent = sum(sp.prod(1 + z * T[i, p[i]] for i in range(4))
                    for p in itertools.permutations(range(4)))
    poly = sp.Poly(sp.expand(permanent), z)
    coefficients = {degree: sp.factor(poly.nth(degree)) for degree in range(5)}
    print("ROWZERO_COEFFICIENTS", json.dumps({str(k): str(v) for k, v in coefficients.items()}), flush=True)
    return coefficients


def chart_worker(chart, queue):
    started = time.monotonic()
    x, y, z, s, t, u = sp.symbols("x y z s t u")
    r = sp.sqrt(-2)
    X = sp.Matrix([x, y, z])
    S = sp.Matrix([[0, s, t], [-s, 0, u], [-t, -u, 0]])
    Y = S * X
    hyperbolic = [(X[i], Y[i]) if not (chart >> i & 1) else (Y[i], X[i])
                  for i in range(3)]
    diag = [r * (left + right) for left, right in hyperbolic]
    off = [left - right for left, right in hyperbolic]
    a, b, c = diag
    d, e, f = off
    q = sp.expand(a * a + b * b + c * c + 2 * (d * d + e * e + f * f))
    assert q == 0
    cubic = sp.expand(a * b * c + 2 * d * e * f + a * f * f + b * e * e + c * d * d)
    equations = sp.Poly(cubic, x, y, z).coeffs()
    basis = sp.groebner(equations, s, t, u, order="grevlex", extension=r)
    queue.put({"chart": chart, "seconds": time.monotonic() - started,
               "equations": [str(eq) for eq in equations],
               "groebner": [str(p.as_expr()) for p in basis.polys],
               "unit_ideal": len(basis.polys) == 1 and basis.polys[0].as_expr() == 1})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--chart", type=int, action="append")
    parser.add_argument("--seconds", type=int, default=60)
    args = parser.parse_args()
    rowzero_coefficients()
    for chart in args.chart if args.chart is not None else range(8):
        queue = multiprocessing.Queue()
        process = multiprocessing.Process(target=chart_worker, args=(chart, queue))
        process.start()
        process.join(args.seconds)
        if process.is_alive():
            process.terminate()
            process.join()
            result = {"chart": chart, "status": "UNKNOWN", "wall_limit_seconds": args.seconds}
        elif process.exitcode:
            result = {"chart": chart, "status": "ERROR", "exit": process.exitcode}
        else:
            result = queue.get()
        print("CHART", json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
