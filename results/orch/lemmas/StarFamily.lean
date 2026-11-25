import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def familyFun (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun s => x.getD s.1 false && s.2.any (fun b => x.getD b false))

lemma family_exists (n : ℕ) : ∀ own : List (ℕ × List ℕ),
    (∀ s ∈ own, s.2 ≠ [] ∧ s.1 < n ∧ ∀ b ∈ s.2, b < n ∧ s.1 ≠ b) →
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      (∀ x : List Bool, x.length = n → D.eval x = familyFun x own) ∧
      D.size = (own.map (fun s => s.2.length)).sum + own.length - 1 ∧
      IsReadK n D 1 ∧ (own ≠ [] → D.output < n + D.size) := by
  intro own
  induction own with
  | nil =>
    intro _
    let D : Circuit := ⟨[], n⟩
    have hfalse (x : List Bool) (hx : x.length = n) : D.eval x = false := by
      simp [D, Circuit.eval, Circuit.wires, ← hx]
    refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
    · simp [D, PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
        PEqualNP.MetaComplexity.NestedCover.ReadsBack]
    · intro x hx
      simpa [familyFun] using hfalse x hx
    · simp [D, Circuit.size]
    · intro S hS
      have ht := hS.1
      change D.eval (List.ofFn (setInput S)) = true at ht
      rw [hfalse _ (by simp)] at ht
      exact (Bool.false_ne_true ht).elim
    · simp
  | cons s own ih =>
    intro hgood
    have hs := hgood s (by simp)
    rcases s with ⟨p, leaves⟩
    cases leaves with
    | nil => exact (hs.1 rfl).elim
    | cons a bs =>
      have hp : p < n := hs.2.1
      have ha : a < n := (hs.2.2 a (by simp)).1
      have hbs : ∀ b ∈ bs, b < n := fun b hb => (hs.2.2 b (by simp [hb])).1
      let S := Star.starCircuit n p a bs
      have hSv : PEqualNP.TopForm.IsAO2 n S := Star.starCircuit_valid n p a bs hp ha hbs
      have hSr : IsReadK n S 1 := Star.starCircuit_read_one n p a bs hp ha hbs
        (fun b hb => (hs.2.2 b hb).2)
      have hSo : S.output < n + S.size := by
        simp [S, Star.starCircuit, Star.addGate, Circuit.size]
      have hSf (x : List Bool) (hx : x.length = n) :
          S.eval x = (x.getD p false && (a :: bs).any (fun b => x.getD b false)) := by
        simpa using Star.starCircuit_eval n p a bs hp ha hbs x hx
      by_cases hown : own = []
      · subst own
        refine ⟨S, hSv, ?_, ?_, hSr, fun _ => hSo⟩
        · intro x hx
          simpa [familyFun] using hSf x hx
        · simp [S, Star.starCircuit_size]
      · obtain ⟨D, hDv, hDf, hDs, hDr, hDo⟩ := ih (fun s hs => hgood s (by simp [hs]))
        refine ⟨unionCircuit n S D, union_valid n S D hSv hDv hSo (hDo hown), ?_, ?_,
          union_read_one n S D hSo hSr hDr, fun _ => union_output n S D⟩
        · intro x hx
          rw [union_eval n S D hSo x hx, hSf x hx, hDf x hx]
          rfl
        · rw [union_size, show S.size = bs.length + 1 from Star.starCircuit_size n p a bs, hDs]
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have hpos : 0 < own.length := List.length_pos_iff.mpr hown
          omega

end PEqualNP.Outside.L_meta_2585.Merge
