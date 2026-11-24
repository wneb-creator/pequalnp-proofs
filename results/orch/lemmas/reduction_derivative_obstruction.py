from itertools import combinations

points = range(1, 8)
line = {p for p in points if p.bit_count() % 2 == 0}

def exact(X):
    return bool(set(X) & line)

def coordinate_masks(X):
    return {(bit, (p >> bit) & 1) for p in X for bit in range(3)}

def compressed(X):
    masks = coordinate_masks(X)
    return any(all((bit, (p >> bit) & 1) in masks for bit in range(3)) for p in line)

assert all(compressed({p}) == exact({p}) for p in points)
assert not exact({1, 2})
assert compressed({1, 2})
print('PASS: all 7 singleton points agree')
print('Line points:', sorted(line))
print('Witness X:', [1, 2], 'exact:', exact({1, 2}), 'compressed:', compressed({1, 2}))
print('Synthesized incident point:', 3)
