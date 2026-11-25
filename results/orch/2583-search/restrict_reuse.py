#!/usr/bin/env python3
"""Restore restricted stars, reusing every suitable live nonlinear wire."""
import itertools
import json
import pathlib
import runpy
import sys

directory = pathlib.Path(sys.argv[1])
context = runpy.run_path(str(directory / 'restrict_repair.py'))
problem, candidate, extras = (context[name] for name in ('problem', 'candidate', 'extras'))
restrict = context['restrict']
vertices = context['vertices']


def values(gates, x):
    result = [bool(x >> i & 1) for i in range(26)]
    for gate in gates:
        a, b = result[gate['a']], result[gate['b']]
        result.append(a and b if gate['op'] == 'and' else a or b)
    return result


results = []
for size in range(1, len(vertices)+1):
    for choice in itertools.combinations(vertices, size):
        zeros = set(choice)
        if any(a not in zeros and b not in zeros for a, b in extras):
            continue
        restricted, base_output = restrict(zeros)
        internal = [(a, b) for a, b in problem['edges'] if a in zeros and b in zeros]
        for orientation in range(1 << len(internal)):
            assigned = {v: [] for v in choice}
            for a, b in problem['edges']:
                if a in zeros and b in zeros:
                    j = internal.index((a, b))
                    center, other = (a, b) if orientation >> j & 1 else (b, a)
                    assigned[center].append(other)
                elif a in zeros:
                    assigned[a].append(b)
                elif b in zeros:
                    assigned[b].append(a)
            gates, output, details = list(restricted), base_output, []
            for center, neighbors in assigned.items():
                if not neighbors:
                    continue
                # These are global monotonicity bounds for restricted wires.
                # Inputs that were set to zero do not occur in restricted gates.
                outside = ((1 << 26)-1) ^ sum(1 << v for v in neighbors)
                bound = values(restricted, outside)
                singleton = [values(restricted, 1 << v) for v in neighbors]
                sources = {}
                for wire in range(26 + len(restricted)):
                    if bound[wire]:
                        continue
                    cover = sum(1 << j for j in range(len(neighbors)) if singleton[j][wire])
                    if cover:
                        sources.setdefault(cover, wire)
                for j, v in enumerate(neighbors):
                    sources[1 << j] = v
                full = (1 << len(neighbors))-1
                dp = {0: []}
                for mask in range(full+1):
                    if mask not in dp:
                        continue
                    for cover, wire in sources.items():
                        merged = mask | cover
                        route = dp[mask] + [wire]
                        if merged not in dp or len(route) < len(dp[merged]):
                            dp[merged] = route
                selected = dp[full]
                details.append(dict(center=center, neighbors=neighbors, sources=selected,
                                    saved=len(neighbors)-len(selected)))
                wire = selected[0]
                for source in selected[1:]:
                    gates.append(dict(op='or', a=wire, b=source))
                    wire = 25 + len(gates)
                gates.append(dict(op='and', a=center, b=wire))
                wire = 25 + len(gates)
                gates.append(dict(op='or', a=output, b=wire))
                output = 25 + len(gates)
            record = dict(zeros=list(choice), orientation=orientation,
                          restricted_gates=len(restricted), restored_gates=len(gates),
                          reused_savings=sum(d['saved'] for d in details), stars=details)
            results.append(record)
            if len(gates) <= 63:
                out = dict(inputs=26, gates=gates, output=output, repair=record)
                (directory / 'reused-repair63.json').write_text(json.dumps(out, indent=2)+'\n')
                print('POTENTIAL EXACT REPAIR', record)
results.sort(key=lambda x: (x['restored_gates'], -x['reused_savings']))
(directory / 'reuse-repairs.json').write_text(json.dumps(results, indent=2)+'\n')
print('reuse-best', results[:3])
