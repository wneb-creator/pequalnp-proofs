import itertools
import json
import pathlib
import random

HERE = pathlib.Path(__file__).resolve().parent
geometry = json.loads((HERE / 'geometry.json').read_text())
case = json.loads((HERE / 'full-case.json').read_text())
edges = {tuple(e) for e in geometry['edges']}
tests = case['tests'] + [[1 << i, 0] for i in range(26)]
tests += [[(1 << p) | (1 << l), 0]
          for p in range(13) for l in range(13, 26) if (p, l) not in edges]
assert len(tests) == 899
signatures = [sum(((x >> i) & 1) << j for j, (x, _) in enumerate(tests))
              for i in range(26)]
target = sum(y << j for j, (_, y) in enumerate(tests))
guardmask = sum(1 << j for j, (x, _) in enumerate(tests)
                if x.bit_count() == 1 or x in ((1 << 13)-1, ((1 << 13)-1) << 13))
maxnegmask = sum(1 << j for j in range(52, 756))
pairmask = sum(1 << j for j in range(782, 899))


class Builder:
    def __init__(self, inputs=26):
        self.inputs = inputs
        self.gates = []
        self.cache = {}
        self.unions = {1 << i: i for i in range(inputs)}

    def gate(self, op, a, b):
        if a == b:
            return a
        a, b = sorted((a, b))
        key = (op, a, b)
        if key not in self.cache:
            self.cache[key] = self.inputs + len(self.gates)
            self.gates.append([op, a, b])
        return self.cache[key]

    def union(self, vertices):
        mask = sum(1 << x for x in vertices)
        assert mask
        if mask in self.unions:
            return self.unions[mask]
        # Reuse the largest existing pure OR chunk, then cover the remaining bits.
        chunks = []
        remaining = mask
        while remaining:
            part = max((m for m in self.unions if m & remaining == m),
                       key=lambda m: (m.bit_count(), -self.unions[m]))
            chunks.append((part, self.unions[part]))
            remaining ^= part
        accumulated, output = chunks[0]
        for part, wire in chunks[1:]:
            output = self.gate(1, output, wire)
            accumulated |= part
            self.unions.setdefault(accumulated, output)
        self.unions[mask] = output
        return output

    def compact(self, output):
        used = {output}
        for i in range(len(self.gates)-1, -1, -1):
            if self.inputs+i in used:
                used.update(self.gates[i][1:])
        renumber = {i: i for i in range(self.inputs)}
        result = []
        for i, (op, a, b) in enumerate(self.gates):
            if self.inputs+i in used:
                renumber[self.inputs+i] = self.inputs + len(result)
                result.append([op, renumber[a], renumber[b]])
        assert renumber[output] == self.inputs - 1 + len(result)
        return result


def build(side, group, split, order):
    owners = list(range(13)) if side == 0 else list(range(13, 26))
    neighbors = {p: {b if a == p else a for a, b in edges if p in (a, b)}
                 for p in owners}
    group = tuple(owners[p] for p in group)
    split = tuple(group[i] for i in split)
    other = set(group) - set(split)
    builder = Builder()
    guard = None
    if split:
        # Merged rectangle M filtered by A OR N(B).  Every original edge survives.
        # Build both guard terms first so they also serve as prefixes of M's sides.
        a = builder.union(split)
        nb = builder.union(set().union(*(neighbors[p] for p in other)))
        guard = builder.gate(1, a, nb)
    owners_wire = builder.union(group)
    neighbors_wire = builder.union(set().union(*(neighbors[p] for p in group)))
    merged = builder.gate(0, owners_wire, neighbors_wire)
    if guard is not None:
        merged = builder.gate(0, merged, guard)
    terms = [merged]
    remaining = [p for p in owners if p not in group]
    if order:
        remaining.reverse()
    for p in remaining:
        terms.append(builder.gate(0, p, builder.union(neighbors[p])))
    output = terms[0]
    for term in terms[1:]:
        output = builder.gate(1, output, term)
    return builder.compact(output)


if __name__ == "__main__":
    seeds = []
    seen = set()
    for side in range(2):
        for size in (3, 4):
            for group in itertools.combinations(range(13), size):
                # Include the unfiltered rectangle and singleton-versus-rest cover guards.
                splits = [()] + [(i,) for i in range(size)]
                if size == 4:
                    splits += [(0, 1), (0, 2), (0, 3)]
                for split in splits:
                    gates = build(side, group, split, sum(group) % 2)
                    if len(gates) > 63:
                        continue
                    key = tuple(map(tuple, gates))
                    if key in seen:
                        continue
                    seen.add(key)
                    values = signatures.copy()
                    for op, a, b in gates:
                        values.append(values[a] | values[b] if op else values[a] & values[b])
                    result = values[-1]
                    assert result & target == target
                    assert result & guardmask == 0
                    seeds.append(dict(side=side, group=group, guard_split=split,
                                      gates=gates, output=25+len(gates), size=len(gates),
                                      maximal_negative_errors=(result & maxnegmask).bit_count(),
                                      nonedge_errors=(result & pairmask).bit_count()))
    random.Random(650).shuffle(seeds)
    path = HERE / 'full-guard-seeds.json'
    path.write_text(json.dumps(seeds))
    with (HERE / 'full-guard-seeds.txt').open('w') as f:
        f.write(f'{len(seeds)}\n')
        for seed in seeds:
            gates = seed['gates'].copy()
            while len(gates) < 63:
                output = 25 + len(gates)
                gates.append([0, output, output])
            f.write(f'{len(gates)}\n')
            for gate in gates:
                f.write(' '.join(map(str, gate)) + '\n')
    with (HERE / 'full-pair-tests.txt').open('w') as f:
        f.write(f'{len(tests)}\n')
        for x, y in tests:
            f.write(f'{x} {y}\n')
    summary = {'seeds': len(seeds), 'minimum_size': min(s['size'] for s in seeds),
               'minimum_nonedge_errors': min(s['nonedge_errors'] for s in seeds),
               'minimum_maximal_negative_errors': min(s['maximal_negative_errors'] for s in seeds)}
    (HERE / 'full-guard-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(summary)
