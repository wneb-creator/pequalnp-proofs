
namespace PEqualNP.Outside.L_meta_2448.cross

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma gateAt_prefix (pre post : List Gate) (output j : ℕ) (hj : j < pre.length) :
    gateAt ⟨pre ++ post, output⟩ j = gateAt ⟨pre, 0⟩ j := by
  exact List.getD_append pre post _ j hj

lemma gateVal_prefix (n : ℕ) (pre post : List Gate) (output j : ℕ)
    (hj : j < pre.length) (x : Fin n → Bool) :
    gateVal n ⟨pre ++ post, output⟩ j x = gateVal n ⟨pre, 0⟩ j x := by
  exact wf_prefix pre post (List.ofFn x) (n+j) (by simp; omega)

lemma inCone_prefix (n : ℕ) (pre post : List Gate) (output i j : ℕ)
    (hj : j < pre.length) :
    InCone n ⟨pre ++ post, output⟩ i j ↔ InCone n ⟨pre, 0⟩ i j := by
  change i ∈ (cf n (pre ++ post) []).getD j [] ↔ i ∈ (cf n pre []).getD j []
  rw [cf_append, cf_keep n post (cf n pre []) j (by simpa [cf_len] using hj)]

lemma owns_prefix (n : ℕ) (pre post : List Gate) (output j : ℕ)
    (hj : j < pre.length) (u v : Fin n) :
    Owns n ⟨pre ++ post, output⟩ j u v ↔ Owns n ⟨pre, 0⟩ j u v := by
  constructor
  · rintro ⟨_, hop, hv, hh⟩
    refine ⟨hj, ?_, ?_, ?_⟩
    · rw [← gateAt_prefix pre post output j hj]
      exact hop
    · rw [← gateVal_prefix n pre post output j hj]
      exact hv
    · intro i hi hc hop
      have hip : i < pre.length := hi.trans hj
      rw [← gateVal_prefix n pre post output i hip]
      exact hh i hi ((inCone_prefix n pre post output i j hj).mpr hc)
        (by simpa only [gateAt_prefix pre post output i hip] using hop)
  · rintro ⟨_, hop, hv, hh⟩
    refine ⟨by change j < (pre ++ post).length; simp; omega, ?_, ?_, ?_⟩
    · rw [gateAt_prefix pre post output j hj]
      exact hop
    · rw [gateVal_prefix n pre post output j hj]
      exact hv
    · intro i hi hc hop
      have hip : i < pre.length := hi.trans hj
      rw [gateVal_prefix n pre post output i hip]
      exact hh i hi ((inCone_prefix n pre post output i j hj).mp hc)
        (by simpa only [gateAt_prefix pre post output i hip] using hop)

end PEqualNP.Outside.L_meta_2448.cross
