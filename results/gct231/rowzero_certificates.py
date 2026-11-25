"""Exact linear-algebra certificates for the eight cubic chart ideals.

Reads the complete saved chart logs; does not invoke another solver.
All arithmetic is in Q(sqrt(-2)). Each worker has an explicit wall cap.
"""

import argparse
import itertools
import json
import multiprocessing
from pathlib import Path
import time

import sympy as sp
from sympy.polys.matrices import DomainMatrix


def monomials(degree):
    return [(a, b, c) for a in range(degree + 1)
            for b in range(degree + 1 - a)
            for c in range(degree + 1 - a - b)]


def worker(record, degree, queue):
    started = time.monotonic()
    variables = sp.symbols("s t u")
    r = sp.sqrt(-2)
    field = sp.QQ.algebraic_field(r)
    equations = [sp.Poly(sp.sympify(eq), *variables, extension=r)
                 for eq in record["equations"]]
    powers = monomials(degree)
    output_powers = monomials(degree + max(poly.total_degree() for poly in equations))
    coefficients = []
    for poly in equations:
        for power in powers:
            shifted = poly * sp.Poly(sp.prod(v ** e for v, e in zip(variables, power)),
                                    *variables, extension=r)
            coefficients.append([shifted.coeff_monomial(power_out)
                                 for power_out in output_powers])
    matrix = sp.Matrix(coefficients).T
    rhs = sp.Matrix([int(power == (0, 0, 0)) for power in output_powers])
    reduced, pivots = DomainMatrix.from_Matrix(matrix.row_join(rhs)).convert_to(field).rref()
    if matrix.cols in pivots:
        queue.put({"chart": record["chart"], "degree": degree, "status": "NO_CERTIFICATE",
                   "seconds": time.monotonic() - started})
        return
    reduced = reduced.to_Matrix()
    solution = [sp.S.Zero] * matrix.cols
    for row, pivot in enumerate(pivots):
        solution[pivot] = reduced[row, matrix.cols]
    multipliers = []
    for index in range(len(equations)):
        multipliers.append(sp.expand(sum(solution[index * len(powers) + j] *
            sp.prod(v ** e for v, e in zip(variables, power))
            for j, power in enumerate(powers))))
    identity = sp.Poly(sp.expand(sum(multiplier * poly.as_expr()
                                    for multiplier, poly in zip(multipliers, equations))),
                       *variables, extension=r)
    assert identity.as_expr() == 1
    queue.put({"chart": record["chart"], "degree": degree, "status": "CERTIFIED",
               "seconds": time.monotonic() - started,
               "equations": record["equations"],
               "multipliers": [str(poly) for poly in multipliers],
               "verified_sum": "1"})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("logs", nargs="+")
    parser.add_argument("--output", required=True)
    parser.add_argument("--seconds", type=int, default=60)
    args = parser.parse_args()
    records = []
    for filename in args.logs:
        for line in Path(filename).read_text().splitlines():
            if line.startswith("CHART "):
                records.append(json.loads(line[6:]))
    certificates = []
    for record in records:
        for degree in range(4):
            queue = multiprocessing.Queue()
            process = multiprocessing.Process(target=worker, args=(record, degree, queue))
            process.start()
            process.join(args.seconds)
            if process.is_alive():
                process.terminate()
                process.join()
                result = {"chart": record["chart"], "degree": degree, "status": "UNKNOWN"}
            elif process.exitcode:
                result = {"chart": record["chart"], "degree": degree, "status": "ERROR"}
            else:
                result = queue.get()
            print(json.dumps({key: value for key, value in result.items()
                              if key not in ("equations", "multipliers")}), flush=True)
            if result["status"] == "CERTIFIED":
                certificates.append(result)
                break
            if result["status"] in ("UNKNOWN", "ERROR"):
                break
    Path(args.output).write_text(json.dumps(certificates, indent=2) + "\n")


if __name__ == "__main__":
    main()
