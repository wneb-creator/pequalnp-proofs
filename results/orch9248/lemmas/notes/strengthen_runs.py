"""Greedy clause strengthening and redundant-step deletion of saved runs."""
import argparse
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "search"))
from rup import check_run, literals, mask_of, php, propagation


def strengthen(run, rng):
    database = php()
    result = []
    for clause in run:
        order = literals(clause)
        rng.shuffle(order)
        for literal in order:
            smaller = clause & ~(1 << literal)
            if propagation(database, smaller)[0]:
                clause = smaller
        result.append(clause)
        database.append(clause)
        if clause == 0:
            break
    return result


def valid(run):
    database = php()
    for clause in run:
        if not propagation(database, clause)[0]:
            return False
        database.append(clause)
    return True


def prune(run, rng):
    order = list(range(len(run)-1))
    rng.shuffle(order)
    marked = set()
    for index in order:
        candidate = [c for j,c in enumerate(run) if j not in marked and j != index]
        if valid(candidate):
            marked.add(index)
    return [c for j,c in enumerate(run) if j not in marked]


def load(path):
    data = json.loads(Path(path).read_text())
    if "oldest_first_clauses" in data:
        return [mask_of(c) for c in data["oldest_first_clauses"]]
    return [mask_of(2*(abs(v)-1) + (v < 0) for v in c) for c in data["run"]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+")
    parser.add_argument("--seconds", type=float, default=30)
    args = parser.parse_args()
    rng = random.Random(9248)
    seeds = [load(p) for p in args.inputs]
    best = min(seeds, key=len)
    iterations = 0
    started = time.time()
    while time.time() - started < args.seconds:
        current = list(rng.choice(seeds))
        for _ in range(3):
            current = prune(strengthen(current, rng), rng)
        if len(current) < len(best):
            best = current
            print(json.dumps({"best":len(best),"iteration":iterations}), flush=True)
            seeds.append(best)
        iterations += 1
    report = check_run(best)
    report.update(iterations=iterations, elapsed=time.time()-started,
                  method="random greedy strengthening and redundant-step deletion")
    target = Path(__file__).with_name("strengthened_run.json")
    target.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"best":len(best),"iterations":iterations,"path":str(target)}))


if __name__ == "__main__":
    main()
