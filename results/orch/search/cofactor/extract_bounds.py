import ast
import json
import re
from pathlib import Path

SOURCE = Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_670.lean')
DEST = Path('/tmp/oec/pequalnp-pilot-87/status_review/subgraph_bounds.json')
text = SOURCE.read_text()
signed, mono = {}, {}
in_signed = True
for line in text.splitlines():
    match = re.fullmatch(r'def known(\d+) := extendKnown (?:\[\]|known\d+) (\d+) (\[.*\])', line)
    if not match:
        continue
    for mask, carry in ast.literal_eval(match.group(3)):
        if mask < 512:
            mono[mask] = max(mono.get(mask, 0), int(match.group(2)))
            if in_signed:
                signed[mask] = max(signed.get(mask, 0), int(match.group(2)))
    if match.group(1) == '383':
        in_signed = False
for name, table in [('transported', mono), ('signedTransports', signed)]:
    line = next(line for line in text.splitlines() if line.startswith('def ' + name + ' :'))
    for mask, lower, base, perm in ast.literal_eval(line.split(':=', 1)[1].strip()):
        if mask < 512:
            table[mask] = max(table.get(mask, 0), lower)
# The final monoRoot/signedRoot certificates strengthen the full nine-input bound.
mono[511] = 16
signed[511] = 15

EDGES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
         (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5))
EDGESET = {frozenset((a, b)) for a, b in EDGES}

def active(mask):
    out = 0
    for a, b in EDGES:
        if mask >> a & 1 and mask >> b & 1:
            out |= (1 << a) | (1 << b)
    return out

def complete9(table):
    result = []
    for mask in range(512):
        required = active(mask)
        value = max(0, required.bit_count() - 1)
        for sub, low in table.items():
            if sub & ~mask == 0 and active(sub):
                value = max(value, low + (required & ~sub).bit_count())
        result.append(value)
    return result

autos = []
def extend(p):
    a = len(p)
    if a == 10:
        autos.append(p)
        return
    for b in range(10):
        if b not in p and all((frozenset((a, i)) in EDGESET) ==
                              (frozenset((b, p[i])) in EDGESET)
                              for i in range(a)):
            extend(p + [b])
extend([])
assert len(autos) == 120

def complete10(table):
    result, evidence = [], []
    for mask in range(1024):
        best = max(0, active(mask).bit_count() - 1)
        cert = None
        for index, perm in enumerate(autos):
            if mask >> perm[9] & 1:
                continue
            sub = sum(1 << i for i in range(9) if mask >> perm[i] & 1)
            if table[sub] > best:
                best, cert = table[sub], (index, sub)
        result.append(best)
        evidence.append(cert)
    return result, evidence

mono10, mono_cert = complete10(complete9(mono))
signed10, signed_cert = complete10(complete9(signed))
DEST.write_text(json.dumps(dict(mono=mono10, signed=signed10, automorphisms=autos,
                               mono_transport=mono_cert, signed_transport=signed_cert)))
print('Saved', DEST)
print('Direct bounds:', len(mono), 'monotone;', len(signed), 'signed')
print('Vertex-zero bounds:', mono10[511], signed10[511])
print('Vertex-one bounds:', mono10[303] + 3, signed10[303] + 3)
