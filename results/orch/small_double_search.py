import json
import time
from pathlib import Path


def search(n, edges, max_gates, time_limit=40, required_truth=None, required_predicate=None):
    started = time.monotonic()
    count = 1 << n
    target = sum(1 << mask for mask in range(count)
                 if any((mask >> a) & (mask >> b) & 1 for a, b in edges))
    first, second = edges[0]
    base_forward = 1 << first
    base_reverse = 1 << second
    initial = tuple(sorted((sum(1 << mask for mask in range(count) if mask >> i & 1),
                            int(i == second), int(i == first)) for i in range(n)))
    states = {initial: []}
    levels = []
    for k in range(1, max_gates + 1):
        following = {}
        for state, path in states.items():
            for a in range(len(state)):
                x, dx, ex = state[a]
                for b in range(a + 1, len(state)):
                    y, dy, ey = state[b]
                    candidates = (
                        (x | y, dx | dy, ex | ey),
                        (x & y,
                         ((x >> base_forward & 1) & dy) | (dx & (y >> base_forward & 1)),
                         ((x >> base_reverse & 1) & ey) | (ex & (y >> base_reverse & 1))))
                    for op, result in enumerate(candidates):
                        if result == (target, 0, 0) and (required_truth is None or
                                any(wire[0] == required_truth for wire in state)) and (
                                required_predicate is None or any(required_predicate(wire[0]) for wire in state)):
                            return dict(n=n, edges=edges, minimum=k, states=levels, path=path+[(op,a,b,result)],
                                        elapsed=time.monotonic() - started)
                        if state.count(result) >= 2:
                            continue
                        following.setdefault(tuple(sorted((*state, result))), path+[(op,a,b,result)])
            if time.monotonic() - started > time_limit:
                return dict(n=n, edges=edges, exhausted_through=k - 1, aborted_at=k,
                            states=levels, elapsed=time.monotonic() - started)
        states = following
        levels.append(len(states))
    return dict(n=n, edges=edges, exhausted_through=max_gates,
                states=levels, elapsed=time.monotonic() - started)


if __name__ == '__main__':
    results = []
    for case in ((2, [(0, 1)], 3), (3, [(0, 1), (0, 2)], 4),
                 (4, [(0, 2), (1, 3)], 5)):
        result = search(*case)
        results.append(result)
        print(json.dumps(result), flush=True)
    Path('/tmp/oec/pequalnp-pilot-60/small-double-search.json').write_text(json.dumps(results, indent=2))
