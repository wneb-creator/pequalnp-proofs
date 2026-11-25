import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--out', required=True)
ap.add_argument('--negative', action='store_true')
args = ap.parse_args()
N = 13
offsets = (0, 1, 3, 9)
neighbors = [sorted((l+d) % N for d in offsets) for l in range(N)]
incidence_masks = [sum(1 << p for p in ps) for ps in neighbors]
gates = []

def gate(op, a, b):
    assert a < 26 + len(gates) and b < 26 + len(gates)
    gates.append((op, a, b))
    return 25 + len(gates)

tops = []
for l, ps in enumerate(neighbors):
    w = ps[0]
    for p in ps[1:]:
        w = gate('or', w, p)
    tops.append(gate('and', w, N+l))
output = tops[0]
for w in tops[1:]:
    output = gate('or', output, w)
assert len(gates) == 64

negative_words = [0] * 26
for mask in range(1 << N):
    for p in range(N):
        if mask >> p & 1:
            negative_words[p] |= 1 << mask
    for l in range(N):
        if not mask & incidence_masks[l]:
            negative_words[N+l] |= 1 << mask
positive_rows = [(p,l) for p in range(N) for l in range(N) if p in neighbors[l]]
assert len(positive_rows) == 52
positive_words = [0] * 26
for row, (p,l) in enumerate(positive_rows):
    positive_words[p] |= 1 << row
    positive_words[N+l] |= 1 << row

def evaluate(words):
    ws = list(words)
    for op, a, b in gates:
        ws.append(ws[a] & ws[b] if op == 'and' else ws[a] | ws[b])
    return ws[output]

assert evaluate(negative_words) == 0
assert evaluate(positive_words) == (1 << 52) - 1
base = Path('/workspace/pequalnp-proofs/results/orch/lemmas')
s = (base/'word_certificate_bridge.lean').read_text()
s += '''
namespace PEqualNP.Outside.L_meta_2583.Q3WordControl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_2583.WordCertificate

def circuit : Circuit :=
  ⟨['''
s += ',\n    '.join('⟨.'+op+', ['+str(a)+', '+str(b)+']⟩' for op,a,b in gates)
s += '], '+str(output)+'⟩\n\n'
checked = (base/'decomposition_pair_lookup_geometry.lean').read_text()
helpers = checked[checked.index('def backwardCheck'):checked.index('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 1000000 in\nlemma circuit_ao')]
s += helpers
s += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma circuit_ao : IsAO2 26 circuit := by
  refine ⟨?_, backwardCheck_sound 26 circuit.gates circuit.output (by decide +kernel), ?_⟩
  · decide +kernel
  · decide +kernel

lemma circuit_size : circuit.size = 64 := rfl

def positiveWords : List (BitVec 52) :=
  ['''
s += ',\n    '.join(hex(w) for w in positive_words)+']\n\n'
s += '''def negativeWords : List (BitVec 8192) :=
  ['''
s += ',\n    '.join(hex(w) for w in negative_words)+']\n\n'
s += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma positive_word_certificate : wordEval circuit positiveWords = (0xfffffffffffff : BitVec 52) := by
  decide +kernel

'''
if args.negative:
    s += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma negative_word_certificate : wordEval circuit negativeWords = 0 := by
  decide +kernel

'''
s += 'end PEqualNP.Outside.L_meta_2583.Q3WordControl\n'
out = Path(args.out)
out.write_text(s)
out.with_suffix('.json').write_text(json.dumps(dict(gates=gates, output=output,
    positive_rows=positive_rows, positive_words=[hex(w) for w in positive_words],
    negative_words=[hex(w) for w in negative_words],
    positive_count=52, negative_count=8192)))
print(json.dumps(dict(gates=64, positive_count=52, negative_count=8192,
    positive_output=hex(evaluate(positive_words)), negative_output=0,
    lean_bytes=len(s.encode()), negative_lemma=args.negative)))
