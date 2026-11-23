from pathlib import Path
import json, hashlib

root = Path(__file__).parent
m = json.loads((root / 'Cut12CodecManifest.json').read_text())
p = json.loads((root / 'Cut12LookupPacked.json').read_text())
base = json.loads((root / 'Data414.json').read_text())
P = 2147483647
table = int(p['table'], 16)
displacements = int(p['displacements'], 16)
patterns = int(p['patterns'], 16)
indices = int(p['patternindices'], 16)
blocks = int(p['patternblocks'], 16)
aliases = int(p['aliases'], 16)

def enabled(k, t, j):
    if not (12 <= k <= 15 and t < 8 and j < 4734):
        return False
    block = (indices >> (7*(j//4))) & 127
    pattern = (blocks >> (20*block+5*(j%4))) & 31
    return (patterns >> (32*pattern + 8*(k-12) + t)) & 1 == 1

def alias_entry(i):
    return (aliases >> (32*i)) & ((1 << 32)-1)

def stamp(k, t, h):
    d = (displacements >> (13*(h % p['buckets']))) & 8191
    slot = (h*p['multiplier'] % P + d) % p['size']
    s = (table >> (16*slot)) & 65535
    j = max(0, s-1)//12
    if enabled(k, t, j):
        return s
    lo, hi = 0, 39
    for _ in range(6):
        if hi <= lo+1:
            break
        mid = (lo+hi)//2
        if alias_entry(mid) & 65535 <= j:
            lo = mid
        else:
            hi = mid
    e = alias_entry(lo)
    return e >> 16 if e & 65535 == j else s

def reindex(x, perm):
    return sum(((x >> j) & 1) << i for i, j in enumerate(perm))

signals = [tuple(int(w[x], 16) for x in ['p', 'n']) for w in m['signals']]
autos = base['autos']
actions = [[tuple(reindex(x, base['auto_indices'][g]) for x in sig)
            for g in range(12)] for sig in signals]
for i in range(9):
    for g in range(12):
        assert actions[i][g] == signals[autos[g][i]]
composition = [[autos.index([h[g[i]] for i in range(9)]) for h in autos] for g in autos]
hashes = [[pow((a[0] % P*65537+a[1] % P+317) % P, 3, P) for a in aa] for aa in actions]
levelsets = {(l['k'], l['t']): set(l['rows']) for l in m['levels']}
membership_checks = 0
for k in range(11, 17):
    for t in range(9):
        for j in range(4735):
            assert enabled(k, t, j) == (j in levelsets.get((k,t), set()))
            membership_checks += 1

transport_checks = 0
for level in m['levels']:
    k, t = level['k'], level['t']
    for i in level['rows']:
        source = m['rows'][i]['v']
        for g0 in range(12):
            hh = [sum(hashes[x][composition[g0][g]] for x in source) % P for g in range(12)]
            h = min(hh)
            c = hh.index(h)
            s = stamp(k, t, h)
            j, inverse = divmod(s-1, 12)
            assert enabled(k, t, j)
            transport = composition[c][inverse]
            actual = sorted(actions[x][composition[g0][transport]] for x in source)
            wanted = sorted(signals[x] for x in m['rows'][j]['v'])
            assert actual == wanted, (k,t,i,g0,j,c,inverse)
            transport_checks += 1
print('PASS memberships', membership_checks, 'all12automorphism transports', transport_checks)
for filename in ['Cut12LookupBody.lean', 'Cut12LookupPacked.json', 'Cut12LookupData.json']:
    content = (root / filename).read_bytes()
    print(filename, len(content), hashlib.sha256(content).hexdigest())
