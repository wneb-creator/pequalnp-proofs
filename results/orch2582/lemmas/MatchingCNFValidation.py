"""Finite validation of the 19-gate matching CNF local-rewrite obstruction."""

import argparse
import json

from ReadTwoSearch import validate
from ReadTwoValidate import capped_validate
from ReadTwoBypassSearch import bypass_witnesses


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    edges = {(0, 3), (1, 4), (2, 5)}
    gates = [(0, 1, 1), (0, 4, 1), (1, 3, 1), (3, 4, 1)]
    for pair in range(6, 10):
        for endpoint in (2, 5):
            gates.append((endpoint, pair, 1))
    gates.append((10, 11, 0))
    current = 18
    for clause in range(12, 18):
        gates.append((clause, current, 0))
        current = 6 + len(gates) - 1
    assert len(gates) == 19 and current == 24
    result = validate(3, 3, edges, gates, True)
    result["gates"] = gates
    result["gate_encoding"] = "0=AND, 1=OR"
    result["edges"] = sorted(edges)
    result["literal_cap3"] = capped_validate(3, 3, edges, gates)
    result["operand_bypass_witnesses"] = bypass_witnesses(3, 3, edges, gates)
    signatures = [0] * 25
    for mask in range(64):
        values = [mask >> i & 1 for i in range(6)]
        for a, b, op in gates:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        for i, value in enumerate(values):
            signatures[i] |= value << mask
    assert len(set(signatures)) == 25
    result["all25_wire_functions_distinct"] = True
    result["wire_signatures"] = signatures
    witnesses = {}
    for omitted in range(19):
        for earlier in range(6 + omitted):
            found = None
            for mask in range(64):
                values = [mask >> i & 1 for i in range(6)]
                for g, (a, b, op) in enumerate(gates):
                    if g == omitted:
                        values.append(values[earlier])
                    else:
                        values.append(values[a] | values[b] if op else values[a] & values[b])
                if bool(values[-1]) != any(mask >> a & 1 and mask >> b & 1
                                          for a, b in edges):
                    found = mask
                    break
            assert found is not None, (omitted, earlier)
            witnesses[str((omitted, earlier))] = found
    assert len(witnesses) == 285
    result["any_earlier_wire_bypass_witnesses"] = witnesses
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
