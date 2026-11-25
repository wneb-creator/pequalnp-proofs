import DirectFilterCore
import SharedFilterSafety

namespace PEqualNP.Outside.L_meta_1884.NoPositiveRail

open PEqualNP.CircuitLowerBounds
open DirectFilter SoleOrPartner

def above0 (w z : List Bool) : Prop :=
  w.length = z.length ∧ 1 ≤ w.length ∧ ∀ i, i ≠ 0 → w.getD i false ≤ z.getD i false

lemma append_above0 {w z : List Bool} {a b : Bool} (h : above0 w z) (hab : a ≤ b) :
    above0 (w ++ [a]) (z ++ [b]) := by
  have hw : 1 ≤ w.length := h.2.1
  refine ⟨by simp [h.1], by simp, ?_⟩
  intro i hi0
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2.2 i hi0
  · by_cases he : i = w.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, h.1] using hab
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [← h.1]; omega)]

lemma run_above0 (gs : List Gate) (w z : List Bool) (h : above0 w z)
    (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (away : ∀ g ∈ gs, 0 ∉ g.inputs) :
    above0 (SafeNot.run gs w) (SafeNot.run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (SafeNot.step w g) (SafeNot.step z g)
    · apply append_above0 h
      apply SafeNot.eval_mono g (allowed g (by simp)) w z
      intro i hi
      exact h.2.2 i (fun he => away g (by simp) (he ▸ hi))
    · intro g' hg'; exact allowed g' (by simp [hg'])
    · intro g' hg'; exact away g' (by simp [hg'])

lemma critical_above : ∀ v : Fin 10, v ≠ 0 →
    above0 (seed (pair 0 v)) (seed (SoleOrPartner.singleton v)) := by
  intro v hv
  refine ⟨by simp [seed], by simp [seed], ?_⟩
  intro i hi0
  by_cases hi : i < 11
  · have finite : ∀ v : Fin 10, v ≠ 0 → ∀ i : Fin 11, i.val ≠ 0 →
        (seed (pair 0 v)).getD i.val false ≤ (seed (SoleOrPartner.singleton v)).getD i.val false := by decide
    exact finite v hv ⟨i, hi⟩ hi0
  · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
        List.getD_eq_default _ _ (by simp [seed]; omega)]

lemma out_not_zero (C : Circuit)
    (correct : ∀ x, C.eval (seed x) = target x) : C.output ≠ 0 := by
  intro ho
  have hc := correct (SoleOrPartner.singleton 0)
  have he : C.eval (seed (SoleOrPartner.singleton 0)) = true := by
    change (SoleReader.run C.gates (seed (SoleOrPartner.singleton 0))).getD C.output false = true
    rw [ho, SoleReader.run_input _ _ 0 (by simp [seed])]
    simp [seed, SoleOrPartner.singleton, List.getD_eq_getElem?_getD]
  rw [he] at hc
  simp [target, SoleOrPartner.singleton] at hc

lemma impossible (pre post : List Gate) (ins : List Nat) (out : Nat) (v : Fin 10)
    (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (hp : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (hs : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (ap : ∀ g ∈ pre, 0 ∉ g.inputs) (as : ∀ g ∈ post, 0 ∉ g.inputs)
    (correct : ∀ x, (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval (seed x) = target x)
    (independent : ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) →
      operand pre ins x = operand pre ins y)
    (factor : ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) →
      (x v || operand pre ins x) = (y v || operand pre ins y) → target x = target y) : False := by
  have hv0 : v ≠ 0 := by rcases hv with rfl | rfl | rfl <;> decide
  have hm := operand_fiber_mono pre ins hp
  have hsingle := rejects_singleton v hv0 (operand pre ins) hm independent factor v
  have hzero := rejects_other_singleton v hv0 (operand pre ins) hm factor 0 (Ne.symm hv0)
  have hpair : operand pre ins (pair 0 v) = false := by
    rw [independent (pair 0 v) (SoleOrPartner.singleton 0) (by
      intro i hi; simp [pair, SoleOrPartner.singleton, hi])]
    exact hzero
  have hlo := SafeNot.replace_not_false pre post ins out (seed (pair 0 v)) hpair
  have hhi := SafeNot.replace_not_false pre post ins out (seed (SoleOrPartner.singleton v)) hsingle
  have hmono : (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval (seed (pair 0 v)) ≤
      (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval (seed (SoleOrPartner.singleton v)) := by
    apply (run_above0 (pre ++ Gate.mk .and [] :: post) _ _ (critical_above v hv0) ?_ ?_).2.2 out
      (out_not_zero _ correct)
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hp g hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact Or.inl rfl
        · exact hs g hg
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ap g hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · simp
        · exact as g hg
  rw [hlo, hhi, correct, correct] at hmono
  rcases hv with rfl | rfl | rfl <;> simp [target, pair, SoleOrPartner.singleton] at hmono
  all_goals cases Bool.le_iff_imp.mp hmono rfl

end PEqualNP.Outside.L_meta_1884.NoPositiveRail
