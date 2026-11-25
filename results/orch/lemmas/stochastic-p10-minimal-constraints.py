import itertools
import json
import sys
import time

start = time.monotonic()
line_points = [{0, 1, 3}, {0, 2, 6}, {1, 5, 6}, {0, 4, 5},
               {3, 4, 6}, {2, 3, 5}, {1, 2, 4}]
Q = set(range(4))
E = {4, 5, 6}
nb = [{t for t in range(7) if i in line_points[t]} for i in range(4)]
survivors = []
count = 0
for codes in itertools.product(range(4), repeat=7):
    count += 1
    r = [{j for j in range(2) if (code >> j) & 1} for code in codes]
    assigned = [nb[i] | {t for x in nb[i] for t in range(7)
                        if r[x] and r[x] <= r[t]} for i in range(4)]
    if all(sum(t in assigned[i] for i in Q) + int(bool(line_points[t] & E))
           <= 2 + len(r[t]) for t in range(7)):
        survivors.append(list(codes))
result = {"scope": "Independent set-based enumeration of direct nonempty residual-inclusion forcing and assigned-consumption bounds. No protected-mask, cofactor, or missing-mask assumptions. Circuit transfer is separate.",
          "enumerated": count, "survivors": survivors,
          "neighbor_rows": [sorted(x) for x in nb],
          "extra": [int(bool(s & E)) for s in line_points],
          "seconds": time.monotonic() - start}
with open(sys.argv[1], 'w') as stream:
    json.dump(result, stream, indent=2)
    stream.write('\n')
print(json.dumps({k:v for k,v in result.items() if k != 'scope'}))
