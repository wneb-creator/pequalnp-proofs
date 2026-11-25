import json
from pathlib import Path

p = Path('/tmp/oec/pequalnp-pilot-62')
repo = Path('/workspace/pequalnp-proofs')
data = json.loads((p / 'packing3-blocks.json').read_text())
actions = json.loads((p / 'packing3-finite-actions.json').read_text())

def read_labels(kind, masks, perms):
    lines = (p / ('packing-capacity3-' + kind + '-certificate.txt')).read_text().splitlines()
    records = [list(map(int, line.split())) for line in lines[1:]]
    assert len(records) == int(lines[0]) == len(masks)
    index = {mask: i for i, mask in enumerate(masks)}
    labels = [None] * len(masks)
    depths = []
    roots = []
    for k, (mask, parent, generator) in enumerate(records):
        if parent == -1:
            assert generator == -1
            depth = 0
            label = 0
            roots.append(index[mask])
        else:
            assert 0 <= parent < k and 0 <= generator < 4
            depth = depths[parent] + 1
            label = 4 * depth + generator
            assert perms[generator][index[mask]] == index[records[parent][0]]
        assert depth < 16
        depths.append(depth)
        labels[index[mask]] = label
    assert all(label is not None for label in labels)
    packed = sum(label << (6*i) for i, label in enumerate(labels))
    for i, label in enumerate(labels):
        assert (packed >> (6*i)) & 63 == label
        if label // 4:
            assert labels[perms[label % 4][i]] // 4 < label // 4
        else:
            assert i in roots
    print(kind, 'count', len(labels), 'maxdepth', max(depths), 'roots', roots)
    return packed, roots

pair_word, pair_roots = read_labels('pairs', [b[0] for b in data['blocks'][26:]], actions['pair_permutations'])
vertex_word, vertex_roots = read_labels('singletons', [1 << v for v in range(26)], actions['vertex_permutations'])
assert vertex_roots == [0]
s = f'''def pairLabel (i : Fin 325) : Nat :=
  ({hex(pair_word)} >>> (6 * i.val)) &&& 63

def pairDepth (i : Fin 325) : Nat := pairLabel i / 4

def pairSelector (i : Fin 325) : Fin 4 := ⟨pairLabel i % 4, Nat.mod_lt _ (by decide)⟩

def pairParent (i : Fin 325) : Fin 325 := pairPerm (pairSelector i) i

def pairRoots : List (Fin 325) := {pair_roots}

def pairLocalCheck (i : Fin 325) : Bool :=
  if pairDepth i = 0 then decide (i ∈ pairRoots)
  else decide (pairDepth (pairParent i) < pairDepth i)

def vertexLabel (v : Fin 26) : Nat :=
  ({hex(vertex_word)} >>> (6 * v.val)) &&& 63

def vertexDepth (v : Fin 26) : Nat := vertexLabel v / 4

def vertexSelector (v : Fin 26) : Fin 4 := ⟨vertexLabel v % 4, Nat.mod_lt _ (by decide)⟩

def vertexParent (v : Fin 26) : Fin 26 := vertexPerm (vertexSelector v) v

def vertexLocalCheck (v : Fin 26) : Bool :=
  if vertexDepth v = 0 then decide (v = 0)
  else decide (vertexDepth (vertexParent v) < vertexDepth v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairLocalCheck_all : ∀ i : Fin 325, pairLocalCheck i = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma vertexLocalCheck_all : ∀ v : Fin 26, vertexLocalCheck v = true := by
  decide +kernel

'''
(p / 'packing3-small-orbits.txt').write_text(s)
base = (repo / 'results/orch/lemmas/PackingThreeOrbits.lean').read_text()
base = base[:base.index('set_option maxRecDepth 100000 in')]
checks = ''
for i in range(65):
    checks += f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_group_{i} : ∀ k : Fin 5, ∀ j : Fin 325,
    localCheck ⟨5 * {i} + k.val, by omega⟩ j = true := by
  decide +kernel

'''
cases = '(fun i => Fin.elim0 i)'
for i in reversed(range(65)):
    cases = f'(Fin.cases localCheck_group_{i} {cases})'
checks += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma localCheck_all : ∀ i j : Fin 325, localCheck i j = true := by
  have h : ∀ g : Fin 65, ∀ k : Fin 5, ∀ j : Fin 325,
      localCheck ⟨5 * g.val + k.val, by omega⟩ j = true := by
    exact ''' + cases + '''
  intro i j
  have hi := h ⟨i.val / 5, by omega⟩ ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ j
  have heq : (⟨5 * (i.val / 5) + i.val % 5, by omega⟩ : Fin 325) = i := by
    apply Fin.ext
    omega
  simpa only [heq] using hi

'''
(repo / 'results/orch/lemmas/PackingThreeAllOrbits.lean').write_text(base + s + checks + 'end PEqualNP.Outside.L_meta_1896_aux.PackingOrbits\n')
print('FULL_SOURCE_BYTES', len((base + s + checks).encode()))
