import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

lemma path4_support_centres {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b c d : Fin n} (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : a ≠ c) (bd : b ≠ d) :
    (∀ v, G.Adj v a → G.Adj v c → v = b) ∧
    (∀ v, G.Adj v b → G.Adj v d → v = c) ∧
    (∀ v, ¬ (G.Adj v b ∧ G.Adj v c)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v va vc
    exact (square v a b c va ab bc vc.symm).resolve_right ac
  · intro v vb vd
    exact (square v b c d vb bc cd vd.symm).resolve_right bd
  · rintro v ⟨vb, vc⟩
    exact triangle v b c vb bc vc.symm

end PEqualNP.Outside.L_meta_1904
