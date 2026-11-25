"""Check a SAT model with the literal capped-at-three joint recurrence.

The search encoder discards large counts; this independent recurrence keeps
them capped at three, exactly as READ-2's Lean definition does. It compares
the retained small vectors at every wire, not only the circuit output.
"""

import argparse
import ast
import json
from pathlib import Path

from ReadTwoSearch import get_graph, validate


def capped_validate(p, l, edges, gates):
    output = {}
    for u, v in sorted(edges):
        capped = [{(1, 0)} if a == u else {(0, 1)} if a == v else set()
                  for a in range(p + l)]
        small = [set(row) for row in capped]
        for a, b, op in gates:
            if op:
                capped.append(capped[a] | capped[b])
                small.append(small[a] | small[b])
            else:
                capped.append({(min(x + xx, 3), min(y + yy, 3))
                               for x, y in capped[a] for xx, yy in capped[b]})
                small.append({(x + xx, y + yy)
                              for x, y in small[a] for xx, yy in small[b]
                              if x + xx <= 2 and y + yy <= 2})
            assert {pair for pair in capped[-1] if max(pair) <= 2} == small[-1]
        output[str((u, v))] = sorted(capped[-1])
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    lines = args.log.read_text().splitlines()
    metadata = next(json.loads(line) for line in lines if line.startswith('{"graph":'))
    assert any(line.startswith("result sat ") for line in lines), "log has no SAT result"
    gates = ast.literal_eval(next(line[6:] for line in lines if line.startswith("gates ")))
    p, l, edges = get_graph(metadata["graph"])
    checked = validate(p, l, edges, gates, metadata["non_read2"])
    checked["literal_capped3_output_vectors"] = capped_validate(p, l, edges, gates)
    checked["every_wire_small_vectors_agree_with_capped3"] = True
    print(json.dumps(checked, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
