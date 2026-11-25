from pathlib import Path

root = Path(__file__).resolve().parents[2]
src = root / 'results/orch/lemmas'
target = root / 'lean/PEqualNP/Outside/L_meta_4675.lean'
marker = 'namespace PEqualNP.Outside.L_meta_4675.SemanticStarForest\n\nlemma star_forest_bound'
old = target.read_text()
tail = marker + old.split(marker, 1)[1]
tail = tail.split('\nnamespace PEqualNP.Outside.L_meta_4675.Normalized', 1)[0]
names = [
    'structural-combinatorics', 'structural-linear', 'library-colour',
    'semantic-support', 'algebraic-mask', 'algebraic-certificate',
    'library-onecolour', 'semantic-linear', 'semantic-starforest',
    'semantic-minterms', 'algebraic-private', 'structural-partners',
    'algebraic-bridge', 'semantic-masked-witness', 'library-or-essential',
    'structural-classification',
]
chunks = []
for name in names:
    lines = (src / (name + '.lean')).read_text().splitlines()
    while lines and (lines[0].startswith('import ') or not lines[0].strip()):
        lines.pop(0)
    if name == 'structural-classification':
        start = lines.index('namespace PEqualNP.Outside.L_meta_4675.Redirect')
        stop = lines.index('end PEqualNP.Outside.L_meta_4675.Redirect', start)
        lines = lines[:start] + lines[stop + 1:]
    chunks.append('\n'.join(lines).rstrip())
content = 'import Mathlib\nimport PEqualNP.Defs\n\n' + '\n\n'.join(chunks) + '\n\n' + tail
content += '''
namespace PEqualNP.Outside.L_meta_4675.Normalized

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.TwoColour

lemma exists_top_form_pair_active {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hne : ∃ u v, G.Adj u v)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (ht : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧ PEqualNP.TopForm.TopForm G D ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = graphFun G ∅ → tCount n D' s = 0 →
        D.size ≤ D'.size) ∧
      (∀ j < D.gates.length, ∃ u v, G.Adj u v ∧ gateVal n D j (pairInput u v) = true) := by
  classical
  have hG : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hne
    exact ⟨s(u, v), by simpa using huv⟩
  obtain ⟨D, hD, hDf, hDt, hsize, htop, hmin⟩ :=
    PEqualNP.Outside.L_meta_4675.Lift.exists_top_form_zero n G C s hG hAO hfun ht
  refine ⟨D, hD, hDf, hDt, hsize, htop, hmin, ?_⟩
  exact PEqualNP.Outside.L_meta_4675.SemanticFold.least_pair_active G D s hD hDt hDf hne
    (fun D' hD' hDt' hDf' => hmin D' hD' hDf' hDt')

end PEqualNP.Outside.L_meta_4675.Normalized
'''
sections = [
    ('algebraic-tree', 'namespace PEqualNP.Outside.L_meta_4675.TreeCount', False),
    ('algebraic-residual-complete', 'namespace PEqualNP.Outside.L_meta_4675.Residual', False),
    ('algebraic-residual-closed', 'namespace PEqualNP.Outside.L_meta_4675.Residual', True),
    ('algebraic-bipartite-reduction', 'namespace PEqualNP.Outside.L_meta_4675.Residual', True),
    ('algebraic-residual-large', 'namespace PEqualNP.Outside.L_meta_4675.Residual', True),
    ('algebraic-bipartite-large', 'namespace PEqualNP.Outside.L_meta_4675.Residual', True),
    ('library-mask-smaller', 'namespace PEqualNP.Outside.L_meta_4675.MaskMerge', False),
    ('algebraic-centres-trace', 'namespace PEqualNP.Outside.L_meta_4675.Centres', False),
    ('algebraic-and-trace', 'namespace PEqualNP.Outside.L_meta_4675.AndTrace', False),
]
for name, marker, last in sections:
    source = (src / (name + '.lean')).read_text()
    pos = source.rindex(marker) if last else source.index(marker)
    content += '\n' + source[pos:].rstrip() + '\n'
paid = (src / 'structural-semantic-mixed-paid.lean').read_text().splitlines()
assert paid[280].startswith('lemma clean_and_unit_adj ')
assert paid[800].startswith('lemma mixed_left_forces_empty_right_orIn ')
assert paid[938] == 'end PEqualNP.Outside.L_meta_4675.StructuralPrefix'
content += '\nnamespace PEqualNP.Outside.L_meta_4675.StructuralPrefix\n\n'
content += '\n'.join(paid[797:799]) + '\n\n'
content += '\n'.join(paid[280:335]) + '\n\n'
content += '\n'.join(paid[800:938]) + '\n\n'
content += 'end PEqualNP.Outside.L_meta_4675.StructuralPrefix\n'
# Research snapshots allow helper theorems; the submission uses helper lemmas.
content = content.replace('\ntheorem ', '\nlemma ')
target.write_text(content)
print('Assembled lines', len(content.splitlines()), 'bytes', len(content.encode()))
