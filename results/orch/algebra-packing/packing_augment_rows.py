from pathlib import Path
import json
import random
import time
import numpy as np

base = Path('/tmp/oec/pequalnp-pilot-62')
data = json.loads((base / 'geometry-data.json').read_text())
original = json.loads((base / 'geometry-cover.json').read_text())
rows = [row['S'] | (row['D'] << 13) for row in data['generic']]
original_masks = {row['S'] | (row['D'] << 13) for row in original}
families = [list(map(int, line.split()[1:]))
            for line in (base / 'singleton-packing-bad.log').read_text().splitlines()
            if line.startswith('BAD ')]
width = max(map(len, families))
array = np.asarray([family + [0] * (width - len(family)) for family in families], dtype=np.uint32)
started = time.monotonic()
covers = []
for row in rows:
    bad = np.count_nonzero(array & row, axis=1) >= 3
    covers.append(int.from_bytes(np.packbits(bad, bitorder='little').tobytes(), 'little'))
full = (1 << len(families)) - 1
assert not any(covers[i] for i, row in enumerate(rows) if row in original_masks)
assert np.bitwise_or.reduce(np.asarray([0], dtype=np.uint8)) == 0
union = 0
for cover in covers:
    union |= cover
assert union == full
rng = random.Random(62)
best = None
for trial in range(40):
    uncovered = full
    selected = []
    while uncovered:
        scores = [(cover & uncovered).bit_count() for cover in covers]
        maximum = max(scores)
        assert maximum
        threshold = maximum if trial == 0 else maximum * (0.90 + 0.10 * rng.random())
        candidates = [i for i, score in enumerate(scores) if score >= threshold]
        choice = candidates[0] if trial == 0 else rng.choice(candidates)
        selected.append(choice)
        uncovered &= ~covers[choice]
    for item in list(reversed(selected)):
        union = 0
        for other in selected:
            if other != item:
                union |= covers[other]
        if union == full:
            selected.remove(item)
    if best is None or len(selected) < len(best):
        best = selected
        print('BEST', trial, len(best), best, flush=True)
extra = [data['generic'][i] for i in best]
augmented = original + extra
augmented_masks = [row['S'] | (row['D'] << 13) for row in augmented]
edges = [(1 << p) | (1 << (13 + line)) for line, mask in enumerate(data['lines'])
         for p in range(13) if mask >> p & 1]
(base / 'packing-augmented-rows.json').write_text(json.dumps(augmented, indent=2) + '\n')
(base / 'packing-augmented-input.txt').write_text(f'{len(augmented_masks)} 52\n' +
    '\n'.join(map(str, augmented_masks + edges)) + '\n')
print(json.dumps({'original_rows': len(original), 'extra_rows': len(extra),
                  'total_rows': len(augmented), 'bad_prefixes': len(families),
                  'extra_S': [row['S'] for row in extra], 'extra_D': [row['D'] for row in extra],
                  'seconds': time.monotonic() - started}), flush=True)
