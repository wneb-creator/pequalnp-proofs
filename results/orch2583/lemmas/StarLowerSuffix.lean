namespace PEqualNP.Outside.L_meta_2583.PlaneCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2583_aux.Geometry

lemma read_one_lower (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hao : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hf : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hr : IsReadK (N + N) C 1) : N * (q + 2) ≤ C.size + 1 := by
  let E := edges I
  have hmem (p l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E,edges]
  have hrect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ ((p,l) ∈ E ∧ (p,l') ∈ E ∧ (p',l) ∈ E ∧ (p',l') ∈ E) := by
    intro p p' l l' hp hl hh
    apply hl
    exact (hu p p' hp).unique ⟨(hmem _ _).mp hh.1,(hmem _ _).mp hh.2.2.1⟩
      ⟨(hmem _ _).mp hh.2.1,(hmem _ _).mp hh.2.2.2⟩
  have hf' : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, (p,l) ∈ E ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    intro z
    simpa only [hmem] using hf z
  obtain ⟨A,B,hcover,hbound⟩ := ReadLower.cover_bound N N E C hrect hao hf' hr
  have hcvr : N ≤ A.card + B.card :=
    cover_lower I hc (lines_through q I (by omega) hN hc hu) A B
      (fun p l h => hcover (p,l) ((hmem p l).mpr h))
  have he : E.card = N * (q + 1) := edge_count I hc
  have heq : N * (q + 2) = N * (q + 1) + N := by ring
  rw [he] at hbound
  omega

end PEqualNP.Outside.L_meta_2583.PlaneCount
