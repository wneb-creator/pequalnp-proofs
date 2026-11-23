from pathlib import Path
import json

root = Path(__file__).parent
m = json.loads((root / 'Cut12CodecManifest.json').read_text())
base = json.loads((root / 'Data414.json').read_text())
P = 2147483647
mask = (1 << 414) - 1
autos = base['autos']
raw = [tuple(int(x, 16) for x in a) for a in base['raw']]

def run(recipe, g):
    stack = []
    for x in recipe:
        if x <= 9:
            stack.append(raw[autos[g][x - 1]])
        elif x == 10:
            a = stack.pop()
            stack.append((a[0] ^ mask, a[1] ^ mask))
        else:
            b, a = stack.pop(), stack.pop()
            stack.append(tuple((u & v) if x == 11 else (u | v) for u, v in zip(a, b)))
    assert len(stack) == 1
    return stack[0]

def hs(a):
    return pow((a[0] % P * 65537 + a[1] % P + 317) % P, 3, P)

actions = [[run(w['recipe'], g) for g in range(12)] for w in m['signals']]
hashes = [[hs(a) for a in row] for row in actions]
inverse = [autos.index([a.index(i) for i in range(9)]) for a in autos]
items, canon, seen, allseen = [], [], {}, {}
for i, row in enumerate(m['rows']):
    hh = [sum(hashes[x][g] for x in row['v']) % P for g in range(12)]
    h = min(hh)
    g = hh.index(h)
    for j, hj in enumerate(hh):
        vals = tuple(sorted(actions[x][j] for x in row['v']))
        allseen.setdefault(hj, set()).add(vals)
    seen.setdefault(h, []).append(i)
    items.append((h, 12 * i + inverse[g] + 1))
    canon.append({'hash': h, 'auto': g})
print('canonical hashes distinct', len(items), 'orbit hashes', len(allseen), flush=True)
assert all(len(allseen[h])==1 for h in seen), 'canonical hash collision'
print('orbit classes', len(seen), 'sizes', dict(__import__('collections').Counter(map(len,seen.values()))), flush=True)
(root / 'Cut12OrbitClasses.json').write_text(json.dumps({'classes':list(seen.values()),'canonical':canon},separators=(',',':')))
assert max(map(len,seen.values())) <= 2
aliases = []
for group in seen.values():
    if len(group) == 2:
        aliases.append((group[0], items[group[1]][1]))
aliases.sort()
items = [items[group[0]] for group in seen.values()]

B = (len(items) + 3) // 4
result = None
for M in [4739, 4877, 5003, 5209]:
    for mult in [65537, 104729, 524287, 999983, 8191, 131071] + [2*j+17011 for j in range(100)]:
        lanes = [[] for _ in range(B)]
        for h, v in items:
            lanes[h % B].append((h * mult % P % M, v))
        table, used, ds, ok = [0] * M, set(), [0] * B, True
        for lane in sorted(range(B), key=lambda j: -len(lanes[j])):
            group = lanes[lane]
            if not group:
                continue
            if len({h for h, v in group}) != len(group):
                ok = False
                break
            if len(group) == 1:
                available = next(i for i in range(M) if i not in used)
                shift = (available - group[0][0]) % M
            else:
                shift = None
                for d in range(M):
                    if all((h + d) % M not in used for h, v in group):
                        shift = d
                        break
                if shift is None:
                    ok = False
                    break
            ds[lane] = shift
            for h, v in group:
                slot = (h + shift) % M
                assert table[slot] == 0
                table[slot] = v
                used.add(slot)
        if ok:
            result = {'size': M, 'buckets': B, 'multiplier': mult,
                      'displacements': ds, 'table': table}
            break
    if result:
        break
assert result is not None
for h, v in items:
    slot = (h * result['multiplier'] % P + result['displacements'][h % B]) % result['size']
    assert result['table'][slot] == v

membership = [0] * len(m['rows'])
for level in m['levels']:
    for i in level['rows']:
        membership[i] |= 1 << ((level['k'] - 12) * 8 + level['t'])
patterns = sorted(set(membership))
pi = [patterns.index(x) for x in membership]
pattern_blocks = [tuple(pi[i:i+4] + [0] * max(0,i+4-len(pi))) for i in range(0,len(pi),4)]
block_dictionary = sorted(set(pattern_blocks))
block_ids = [block_dictionary.index(x) for x in pattern_blocks]
assert len(block_dictionary) <= 128

def pack(xs, w):
    return sum(x << (w*j) for j, x in enumerate(xs))

data = {**result, 'canonical': canon, 'membership': membership, 'patterns': patterns,
        'aliases': aliases,
        'patternindices': pi, 'patternblocks': block_dictionary, 'blockids': block_ids,
        'inverse': inverse}
(root / 'Cut12LookupData.json').write_text(json.dumps(data, separators=(',', ':')))
packed = {'table': hex(pack(result['table'], 16)),
          'displacements': hex(pack(result['displacements'], 13)),
          'patterns': hex(pack(patterns, 32)), 'patternindices': hex(pack(block_ids, 7)),
          'patternblocks': hex(pack([pack(x,5) for x in block_dictionary],20)),
          'aliases': hex(pack([a | (b << 16) for a,b in aliases], 32))}
(root / 'Cut12LookupPacked.json').write_text(json.dumps(
    {**packed, 'size': result['size'], 'buckets': B, 'multiplier': result['multiplier']},
    separators=(',', ':')))
body = f'''namespace PEqualNP.Outside.L_meta_670_aux.Cut12Data

def tableSize : Nat := {result['size']}
def tableBuckets : Nat := {B}
def tableMultiplier : Nat := {result['multiplier']}
def tableBits : Nat := {packed['table']}
def displacementBits : Nat := {packed['displacements']}
def activePatterns : Nat := {packed['patterns']}
def activeIndices : Nat := {packed['patternindices']}
def activeBlocks : Nat := {packed['patternblocks']}

def primaryStamp (h : Nat) : Nat :=
  let d := (displacementBits >>> (13*(h % tableBuckets))) % 8192
  let slot := ((h*tableMultiplier % 2147483647)+d) % tableSize
  (tableBits >>> (16*slot)) % 65536

def enabled (k t j : Nat) : Bool :=
  if 12 ≤ k && k ≤ 15 && t < 8 && j < 4734 then
    let block := (activeIndices >>> (7*(j/4))) % 128
    let pattern := (activeBlocks >>> (20*block+5*(j%4))) % 32
    ((activePatterns >>> (32*pattern+8*(k-12)+t)) % 2) == 1
  else false

def aliasBits : Nat := {packed['aliases']}

def aliasEntry (i : Nat) : Nat := (aliasBits >>> (32*i)) % 4294967296

def findAlias : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel+1, j, lo, hi =>
    if hi ≤ lo+1 then lo else
      let mid := (lo+hi)/2
      if aliasEntry mid % 65536 ≤ j then findAlias fuel j mid hi
      else findAlias fuel j lo mid

def lookupStamp (k t h : Nat) : Nat :=
  let stamp := primaryStamp h
  let j := (stamp-1)/12
  if enabled k t j then stamp else
    let entry := aliasEntry (findAlias 6 j 0 39)
    if entry % 65536 = j then entry >>> 16 else stamp

end PEqualNP.Outside.L_meta_670_aux.Cut12Data
'''
(root / 'Cut12LookupBody.lean').write_text(body)
print('CHD', result['size'], B, result['multiplier'], 'Leanbytes', len(body.encode()),
      'maxdisplacement', max(ds), 'patterns', len(patterns), flush=True)
