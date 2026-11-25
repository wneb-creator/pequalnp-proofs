import collections
import json

N = 1024
ALL = (1 << N) - 1
PIN = [sum(1 << x for x in range(N) if (x >> i) & 1) for i in range(10)]
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
         (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9),
         (9, 6), (6, 8), (8, 5)]
TARGET = 0
for a, b in EDGES:
    TARGET |= PIN[a] & PIN[b]
ZERO = [ALL ^ p for p in PIN]
CRITICAL = [(TARGET ^ (TARGET >> (1 << i))) & ZERO[i] for i in range(10)]


def gate(d, a, b):
    return [a & b, a | b, a & ~b, ~a & b][d] & ALL


def is_linear_zero(sig, v):
    masked = sig & ZERO[v]
    return masked == 0 or any(masked == p & ZERO[v] for p in PIN)


def witness(g1, g2, v):
    if not is_linear_zero(g1, v) or not is_linear_zero(g2, v):
        return None
    bits = CRITICAL[v] & ~(g1 ^ (g1 >> (1 << v))) & ~(g2 ^ (g2 >> (1 << v)))
    if not bits:
        return None
    return (bits & -bits).bit_length() - 1


def paid_witness(g1, g2, v):
    if (g2 & ZERO[v]) != 0:
        return None
    bits = CRITICAL[v] & ~(g1 ^ (g1 >> (1 << v))) & ~(g2 ^ (g2 >> (1 << v)))
    if not bits:
        return None
    return (bits & -bits).bit_length() - 1


summary = collections.Counter()
bad = []
for j in (1, 2):
    for d1 in range(4):
        g1 = gate(d1, PIN[0], PIN[j])
        bank = PIN + [g1]
        for a in range(11):
            for b in range(a + 1, 11):
                for d2 in range(4):
                    g2 = gate(d2, bank[a], bank[b])
                    if g2 == 0 or g2 in bank:
                        continue
                    summary['valid'] += 1
                    found = [(v, witness(g1, g2, v)) for v in range(10)]
                    found = [(v, row) for v, row in found if row is not None]
                    if found:
                        summary['restriction_proves_binary18'] += 1
                    else:
                        summary['unresolved'] += 1
                        summary['unresolved_dependent' if b == 10 else 'unresolved_independent'] += 1
                        bad.append(dict(j=j, d1=d1, a=a, b=b, d2=d2))
                    paid = [(v, paid_witness(g1, g2, v)) for v in range(10)]
                    paid = [(v, row) for v, row in paid if row is not None]
                    if paid:
                        summary['paid_restriction_proves_binary18'] += 1
                    if not found and not paid:
                        summary['neither_restriction_works'] += 1
                        if d1 == 1:
                            summary['or_first_unresolved_second_'+str(d2)] += 1
print(json.dumps(dict(summary=summary, unresolved=bad), indent=2))
