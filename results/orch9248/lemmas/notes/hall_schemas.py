"""Constructive Hall RUP schemas; exact finite checks, not a lower bound."""
import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "search"))
from rup import check_run, literals, mask_of, php, propagation


def pos(p, h):
    return 2 * (4 * p + h)


def neg(p, h):
    return pos(p, h) + 1


def escape(pigeons, holes):
    return mask_of(pos(p, h) for p in pigeons for h in range(4) if h not in holes)


def hall2(pigeons, holes):
    return [escape(pigeons, holes)]


def hall3(pigeons, holes):
    a, b, c = pigeons
    h0, h1 = holes
    e = escape(pigeons, holes)
    return [e | mask_of([neg(a, h0)]), e]


def hall4(pigeons, holes):
    a, b, c, d = pigeons
    h0, h1, h2 = holes
    e = escape(pigeons, holes)
    return [e | mask_of([neg(a, h0), pos(c, h1)]),
            e | mask_of([neg(d, h1)]),
            e | mask_of([neg(b, h0)]),
            e | mask_of([pos(b, h1)]), e]


def main():
    counts = {}
    reports = {}
    for k, constructor in [(2, hall2), (3, hall3), (4, hall4)]:
        count = 0
        for pigeons in itertools.permutations(range(5), k):
            for holes in itertools.permutations(range(4), k - 1):
                run = constructor(pigeons, holes)
                check_run(run)
                count += 1
        counts[str(k)] = count
        reports[str(k)] = check_run(constructor(tuple(range(k)), tuple(range(k - 1))))
    result = {"status": "exact finite RUP validation; no Lean claim",
              "all_ordered_instantiations": counts, "examples": reports}
    target = Path(__file__).with_name("hall_schemas.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"verified": counts, "path": str(target)}))


if __name__ == "__main__":
    main()
