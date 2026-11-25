"""Recreate the seven-gate shared-P4 positive calibration exactly.

The generated metadata describes the base CNF. Pinning appends three unit
clauses per gate and updates the DIMACS header, hence the 21-clause delta.
"""
import argparse
import json
from pathlib import Path

from fano_multi_sat import generate


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--stem", required=True)
    a = p.parse_args()
    gates = [(1, 0, 1), (0, 1, 8), (1, 8, 9), (1, 2, 15),
             (1, 7, 15), (0, 16, 17), (0, 14, 18)]
    generate(7, 5, True, [0, 1, 2, 7, 8, 9], a.stem,
             violation=False, ordered=True, projected=True,
             fanout_budget=True, roots=2)
    data = json.loads(Path(a.stem + ".json").read_text())
    pins = []
    for g, (op, u, v) in enumerate(gates):
        pins.extend([data["ops"][g] if op else -data["ops"][g],
                     data["selectors"][g][0][u],
                     data["selectors"][g][1][v]])
    path = Path(a.stem + ".cnf")
    text = path.read_text().splitlines()
    text[0] = "p cnf %d %d" % (data["variables"], data["clauses"] + len(pins))
    text.extend("%d 0" % x for x in pins)
    path.write_text("\n".join(text) + "\n")
    print(json.dumps({"pins": len(pins), "gates": gates}))


if __name__ == "__main__":
    main()
