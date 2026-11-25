import argparse
import json
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pack', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=10)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for case in json.loads(args.pack.read_text()):
        start = time.monotonic()
        n = case['inputs']
        signatures = [sum(1 << t for t, (mask, _) in enumerate(case['tests']) if mask >> i & 1)
                      for i in range(n)]
        target = sum(1 << t for t, (_, label) in enumerate(case['tests']) if label)
        dp = [set() for _ in range(1 << n)]
        for i, signature in enumerate(signatures):
            dp[1 << i].add(signature)
        operations = 0
        completed = True
        for size in range(2, n + 1):
            for subset in range(1, 1 << n):
                if subset.bit_count() != size:
                    continue
                anchor = subset & -subset
                part = (subset - 1) & subset
                while part:
                    if part & anchor:
                        other = subset ^ part
                        for a in dp[part]:
                            for b in dp[other]:
                                dp[subset].add(a & b)
                                dp[subset].add(a | b)
                                operations += 1
                            if time.monotonic() - start > args.seconds:
                                completed = False
                                break
                        if not completed:
                            break
                    part = (part - 1) & subset
                if not completed:
                    break
            if not completed:
                break
        report = dict(case=case['name'], sources=n, completed=completed,
                      seconds=time.monotonic() - start, pair_operations=operations,
                      reachable_signature_count=len(dp[-1]),
                      target_read_once=(target in dp[-1]) if completed else None,
                      scope='Every raw input and the single correlated OR feature occurs exactly once.')
        if completed:
            (args.output / (case['name'] + '-tables.json')).write_text(
                json.dumps(dict(signatures=signatures, target=target,
                                reachable=[sorted(values) for values in dp])))
        (args.output / (case['name'] + '-result.json')).write_text(json.dumps(report))
        print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
