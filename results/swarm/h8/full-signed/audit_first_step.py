"""Independently replay the 720 first signed steps using whole H9 bounds only."""
import argparse
import itertools
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--reference', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
reference = json.loads(args.reference.read_text())
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
         (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
raw = [[bool(row >> i & 1) for row in range(1024)] for i in range(10)]
target = [any(raw[a][row] and raw[b][row] for a,b in edges) for row in range(1024)]
stats = dict(projection=0, collision=0, open=0)
records = []
for a,b in itertools.combinations(range(10), 2):
    for op in range(4):
        out = [(x and y) if op == 0 else (x or y) if op == 1 else
               (x and not y) if op == 2 else (not x and y)
               for x,y in zip(raw[a],raw[b])]
        for ka,kb in itertools.product([False,True], repeat=2):
            child = [w for i,w in enumerate(raw) if (i != a or ka) and (i != b or kb)] + [out]
            reason = None
            for v in range(10):
                rows = [r for r in range(1024) if not raw[v][r]]
                restricted = [tuple(w[r] for r in rows) for w in child]
                bank = {tuple(w[r] for r in rows) for w in raw}
                bank |= {tuple(not x for x in w) for w in list(bank)}
                bank |= {(False,)*512, (True,)*512}
                constants = sum(all(x == w[0] for x in w) for w in restricted)
                # Whole H9 signed lower bound 15; remaining budget is 15.
                if all(w in bank for w in restricted) and 15 < 15 + constants:
                    reason = ['projection', v]
                    break
            if reason is None:
                profiles = {}
                for r in range(1024):
                    profile = tuple(w[r] for w in child)
                    if profile in profiles and target[profiles[profile]] != target[r]:
                        reason = ['collision', [profiles[profile],r]]
                        break
                    profiles[profile] = r
            if reason is None:
                reason = ['open', None]
            saved = reference['records'][len(records)]
            assert saved[:5] == [a,b,op,ka,kb]
            if reason[0] == 'collision':
                # Different valid collisions may be encountered first. Check
                # the exact saved pair independently, rather than require the
                # same incidental iteration order in both implementations.
                assert saved[5] == 'collision'
                r,s = saved[6]
                assert 0 <= r < 1024 and 0 <= s < 1024
                assert target[r] != target[s]
                assert all(w[r] == w[s] for w in child)
                reason = saved[5:]
            stats[reason[0]] += 1
            records.append([a,b,op,ka,kb,*reason])
result = dict(stats=stats, records=records)
assert result == reference, 'independent first-step replay differs from saved records'
assert stats == dict(projection=675,collision=45,open=0)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(stats))
