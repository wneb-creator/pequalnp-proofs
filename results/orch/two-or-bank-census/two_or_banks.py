from pathlib import Path
import json, itertools, time, hashlib

base = Path('/tmp/oec/pequalnp-pilot-87/status_review/two-or-banks')
base.mkdir(exist_ok=True)
source = Path('/workspace/pequalnp-proofs/results/orch/weak20369-generation/complete-fixture-20369.json')
fixture = json.loads(source.read_text())
autos = fixture['header']['automorphisms']
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
edge_set = {tuple(sorted(e)) for e in edges}
def graph(r):
    return any((r >> a) & (r >> b) & 1 for a,b in edges)
assert len(autos) == len(set(map(tuple, autos))) == 120
for a in autos:
    assert sorted(a) == list(range(10))
    assert {tuple(sorted((a[u], a[v]))) for u,v in edges} == edge_set
pairs = list(itertools.combinations(range(10), 2))
all_cases = set(itertools.combinations(pairs, 2))
cases = []
while all_cases:
    rep = min(all_cases)
    orbit = {tuple(sorted(tuple(sorted((g[a],g[b]))) for a,b in rep)) for g in autos}
    assert orbit <= all_cases
    all_cases -= orbit
    cases.append((rep, len(orbit)))
positive = [r for r in range(1024) if graph(r)]
negative = [r for r in range(1024) if not graph(r)]
assert len(negative) == 76
report = []
started = time.monotonic()
for number, (rep, size) in enumerate(cases):
    pmasks = [sum(1 << j for j in p) for p in rep]
    signals = []
    for r in range(1024):
        hs = [bool(r & m) for m in pmasks]
        signals.append(r | (int(hs[0]) << 10) | (int(hs[1]) << 11)
                       | (int(not hs[0]) << 12) | (int(not hs[1]) << 13))
    clauses = [dict() for _ in range(4)]
    for p in positive:
        for n in negative:
            diff = signals[p] & ~signals[n]
            for used_neg in range(4):
                if diff & (used_neg << 12):
                    continue
                mask = diff & 4095
                assert mask
                clauses[used_neg].setdefault(mask, (p,n))
    patterns = []
    for used_neg in range(4):
        minimal_clauses = []
        for mask in sorted(clauses[used_neg], key=lambda m: (m.bit_count(),m)):
            if not any((old & mask) == old for old in minimal_clauses):
                minimal_clauses.append(mask)
        valid = [all(mask & c for c in minimal_clauses) for mask in range(4096)]
        minima = [mask for mask in range(4096) if valid[mask]
                  and all(not valid[mask ^ (1 << j)] for j in range(12) if mask >> j & 1)]
        assert minima
        forced = 4095
        for mask in minima:
            forced &= mask
        patterns.append(dict(negatives_retained=[j for j in range(2) if used_neg >> j & 1],
                             minimal_clauses=[dict(mask=c,positive=clauses[used_neg][c][0],
                                                   negative=clauses[used_neg][c][1])
                                              for c in minimal_clauses],
                             minimal_banks=[dict(optional_mask=m, root_count=m.bit_count()+used_neg.bit_count(),
                                                 inputs=[j for j in range(10) if m >> j & 1],
                                                 positive_sources=[j for j in range(2) if m >> (10+j) & 1])
                                            for m in minima],
                             forced_inputs=[j for j in range(10) if forced >> j & 1],
                             valid_optional_banks=sum(valid)))
    report.append(dict(index=number,pairs=rep,orbit_size=size,
                       pair_edges=[tuple(p) in edge_set for p in rep],
                       overlap=len(set(rep[0]) & set(rep[1])), patterns=patterns))
    print(number, rep, size, 'bothneg', len(patterns[3]['minimal_banks']),
          'forced', patterns[3]['forced_inputs'],
          'sizes', sorted({m['root_count'] for m in patterns[3]['minimal_banks']}), flush=True)
result = dict(scope='Exhaustive full-row positive-tail order-separation bank census, not a gate-bound proof or circuit search. Distinct original-input OR pairs only. Every valid bank contains a listed inclusion-minimal bank; presence of both complements is pattern3. Equal OR pairs collapse semantically to the one-NOT family and are not enumerated.',
              fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              root_positions='0..9 inputs;10,11 positive OR sources;12,13 their complements',
              positive_rows=len(positive), negative_rows=len(negative), case_count=len(cases),
              pair_pair_total=sum(s for _,s in cases), cases=report, seconds=time.monotonic()-started)
(base/'census.json').write_text(json.dumps(result, indent=2)+'\n')
print('DONE',len(cases),'orbits',sum(s for _,s in cases),'cases',result['seconds'], flush=True)
