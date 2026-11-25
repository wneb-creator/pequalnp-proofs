import json
import pathlib
import sys
import time

packet, case_index, seed_path, output_path = sys.argv[1:]
case = json.loads(pathlib.Path(packet).read_text())[int(case_index)]
gates = json.loads(pathlib.Path(seed_path).read_text())
n, raw, points = case['inputs'], case['raw_inputs'], len(case['group'])
tests = case['tests'].copy()
for x in (1 << i for i in range(raw)):
    value = x
    for i, f in enumerate(case['features']):
        if any(x >> v & 1 for v in f['raw_indices']):
            value |= 1 << (raw+i)
    tests.append([value, 0])
mask = (1 << len(tests))-1
target = sum(y << i for i, (_, y) in enumerate(tests))
guard = sum(1 << i for i, (x, _) in enumerate(tests)
            if (x & ((1 << raw)-1)).bit_count() == 1 or
            (x & ((1 << raw)-1)) in ((1 << points)-1, ((1 << raw)-1)^((1 << points)-1)))
values = [sum(((x >> i) & 1) << j for j, (x, _) in enumerate(tests)) for i in range(n)]
for op, a, b in gates:
    values.append(values[a] | values[b] if op else values[a] & values[b])
best = (values[-1] & ~target).bit_count()
solutions = []
checked = 0
start = time.monotonic()
for consumer, (old_op, old_a, old_b) in enumerate(gates):
    context = []
    for bit in (0, mask):
        working = values.copy()
        working[n+consumer] = bit
        for i in range(consumer+1, len(gates)):
            op, a, b = gates[i]
            working[n+i] = working[a] | working[b] if op else working[a] & working[b]
        context.append(working[-1])
    for side in (1, 2):
        other = values[old_b if side == 1 else old_a]
        for op in (0, 1):
            for a in range(n+consumer):
                for b in range(a+1, n+consumer):
                    inserted = values[a] | values[b] if op else values[a] & values[b]
                    modified = other | inserted if old_op else other & inserted
                    output = context[0] | (context[1] & modified)
                    checked += 1
                    if output & target != target or output & guard:
                        continue
                    bad = (output & ~target).bit_count()
                    if bad > best:
                        continue
                    candidate = []
                    for i, gate in enumerate(gates):
                        if i == consumer:
                            candidate.append([op, a, b])
                        original_op, left, right = gate
                        left += left >= n+consumer
                        right += right >= n+consumer
                        if i == consumer:
                            if side == 1:
                                left = n+consumer
                            else:
                                right = n+consumer
                        candidate.append([original_op, left, right])
                    used = {n+len(candidate)-1}
                    for i in range(len(candidate)-1, -1, -1):
                        if n+i in used:
                            used.update(candidate[i][1:])
                    if any(i not in used for i in range(raw)):
                        continue
                    if bad < best:
                        best = bad
                        solutions = []
                        print('BEST', best, 'consumer', consumer, 'side', side,
                              'inserted', [op, a, b], 'seconds', time.monotonic()-start, flush=True)
                        pathlib.Path(output_path).write_text(json.dumps(candidate)+'\n')
                    if len(solutions) < 30:
                        solutions.append(dict(gates=candidate, false=bad, consumer=consumer,
                                              side=side, inserted=[op, a, b]))
pathlib.Path(output_path).with_suffix('.pool.json').write_text(json.dumps(solutions))
print('DONE', checked, 'best', best, 'ties_retained', len(solutions),
      'seconds', time.monotonic()-start, flush=True)
