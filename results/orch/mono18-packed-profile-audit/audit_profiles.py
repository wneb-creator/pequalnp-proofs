import argparse
import hashlib
import json
from pathlib import Path
import re
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_maximum(matrix, rows, cols):
    if len(rows) > len(cols):
        matrix = [list(x) for x in zip(*matrix)]
        rows, cols = cols, rows
    best = 0
    sums = [0] * len(cols)
    previous = 0
    for counter in range(1, 1 << len(rows)):
        selected = counter ^ (counter >> 1)
        changed = selected ^ previous
        position = changed.bit_length() - 1
        sign = 1 if selected & changed else -1
        row = matrix[rows[position]]
        for j, col in enumerate(cols):
            sums[j] += sign * row[col]
        best = max(best, sum(x for x in sums if x > 0))
        previous = selected
    return best


def brute_maximum(matrix, rows, cols):
    best = 0
    for rmask in range(1 << len(rows)):
        for cmask in range(1 << len(cols)):
            score = sum(matrix[r][c] for i, r in enumerate(rows)
                        for j, c in enumerate(cols)
                        if (rmask >> i) & 1 and (cmask >> j) & 1)
            best = max(best, score)
    return best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('census', type=Path)
    parser.add_argument('generated', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    args.output.mkdir(parents=True, exist_ok=True)
    weights = json.loads((args.census / 'weights.json').read_text())
    profiles = json.loads((args.census / 'profiles.json').read_text())
    blocks = json.loads((args.generated / 'blocks.json').read_text())
    locator = json.loads((args.generated / 'profile-locator.json').read_text())
    base = (args.generated / 'Mono18RectangleBase.lean').read_text()
    spec_text = base.split('def specs :', 1)[1].split('def spec (', 1)[0]
    specs = [tuple(int(v, 0) for v in match) for match in
             re.findall(r'\((\d+),(\d+),(\d+),(\d+),(0x[0-9a-f]+)\)', spec_text)]
    assert len(specs) == len(weights) == 19
    coefficient_count = 0
    for i, (nr, nc, offset, bits, packed) in enumerate(specs):
        original = weights[i]
        assert (nr, nc) == (original['rows'], original['cols'])
        assert nr > 0 and nc > 0 and bits > 0
        assert len(original['weights']) == nr
        assert all(len(row) == nc for row in original['weights'])
        assert packed >> (nr * nc * bits) == 0
        decoded = [[((packed >> (bits * (r * nc + c))) & ((1 << bits) - 1)) - offset
                    for c in range(nc)] for r in range(nr)]
        assert decoded == original['weights'], ('matrix', i)
        assert sum(map(sum, decoded)) == original['total']
        coefficient_count += nr * nc

    pattern = re.compile(r'def block(\d+) : \{xs : List Nat // xs\.all '
                         r'\(checkRecord (\d+)\) = true\} :=\s*'
                         r'⟨\[([0-9a-fx,\s]*)\], by decide \+kernel⟩')
    sources = sorted(args.generated.glob('Mono18RectangleCost*.lean'))
    parsed = {}
    for source in sources:
        text = source.read_text()
        declarations = re.findall(r'^def block\d+\b', text, re.M)
        found = list(pattern.finditer(text))
        assert len(declarations) == len(found), source.name
        for match in found:
            bid, weight = int(match[1]), int(match[2])
            records = [int(value.strip(), 0) for value in match[3].split(',') if value.strip()]
            assert bid not in parsed, ('duplicate declaration', bid)
            parsed[bid] = (weight, records, source.name)
    assert sorted(parsed) == list(range(108))
    assert len(blocks) == 108 and len(profiles) == len(locator) == 6159
    assert sorted(map(int, locator)) == list(range(len(profiles)))
    aggregate = (args.generated / 'Mono18RectangleCosts.lean').read_text()
    order = [(int(a), int(b)) for a, b in re.findall(r'⟨(\d+), block(\d+)⟩', aggregate)]
    assert order == [(b['weight'], b['id']) for b in blocks]

    seen = []
    records = []
    subset_count = 0
    brute_checks = 0
    slack_count = 0
    for block in blocks:
        bid = block['id']
        weight, encoded, filename = parsed[bid]
        assert weight == block['weight']
        assert len(encoded) == len(block['profiles'])
        nr, nc, _, _, _ = specs[weight]
        work = 0
        for offset, (pid, code) in enumerate(zip(block['profiles'], encoded)):
            profile = profiles[pid]
            p = code & ((1 << nr) - 1)
            n = (code >> nr) & ((1 << nc) - 1)
            cap = code >> (nr + nc)
            assert profile['weight'] == weight
            assert p == profile['positive_mask']
            assert n == profile['negative_false_mask']
            assert cap == profile['cost']
            loc = locator[str(pid)]
            assert loc == dict(block=bid, offset=offset, weight=weight, record=hex(code))
            rows = [r for r in range(nr) if (p >> r) & 1]
            cols = [c for c in range(nc) if (n >> c) & 1]
            matrix = weights[weight]['weights']
            optimum = exact_maximum(matrix, rows, cols)
            assert optimum <= cap, (pid, optimum, cap)
            if len(rows) + len(cols) <= 9:
                assert brute_maximum(matrix, rows, cols) == optimum, pid
                brute_checks += 1
            slack_count += optimum < cap
            work += 1 << min(len(rows), len(cols))
            seen.append(pid)
            records.append(dict(profile=pid, block=bid, offset=offset, source=filename,
                                weight=weight, positive_count=len(rows),
                                negative_false_count=len(cols), exact_maximum=optimum,
                                recorded_cap=cap, source_obligations=profile['source_obligations']))
        assert work == block['subsets']
        subset_count += work
    assert sorted(seen) == list(range(len(profiles)))
    assert subset_count == 177807
    inputs = [args.census / 'weights.json', args.census / 'profiles.json',
              args.generated / 'blocks.json', args.generated / 'profile-locator.json',
              args.generated / 'Mono18RectangleBase.lean',
              args.generated / 'generate_profiles.py', args.generated / 'compile-plan.json'] + sources
    manifest = {str(path): dict(sha256=digest(path), bytes=path.stat().st_size) for path in inputs}
    result = dict(verdict='PASS', matrices=len(weights), coefficients=coefficient_count,
                  profiles=len(records), blocks=len(blocks), subsets=subset_count,
                  brute_checks=brute_checks, profiles_with_slack=slack_count,
                  source_obligations=sum(r['source_obligations'] for r in records),
                  elapsed_seconds=time.monotonic()-started,
                  scope='Finite packed profile data only; no whole-search or kernel completion claim.')
    (args.output / 'report.json').write_text(json.dumps(result, indent=2)+'\n')
    (args.output / 'profiles-audited.json').write_text(json.dumps(records, indent=2)+'\n')
    (args.output / 'input-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
