import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.OneNot

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

lemma getD_snoc (w : List Bool) (b : Bool) (j : ℕ) :
    (w ++ [b]).getD j false = if j = w.length then b else w.getD j false := by
  by_cases h : j < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (Nat.ne_of_lt h)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases he : j = w.length
    · subst j
      simp
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by omega)]
      cases hd : j - w.length with
      | zero => omega
      | succ k => simp

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega

lemma fold_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

lemma fold_agree_except (gs : List Gate) (i : ℕ)
    (avoid : ∀ g ∈ gs, i ∉ g.inputs)
    (w v : List Bool) (hlen : w.length = v.length)
    (hi : i < w.length)
    (agree : ∀ j, j ≠ i → w.getD j false = v.getD j false) :
    ∀ j, j ≠ i → (gs.foldl step w).getD j false = (gs.foldl step v).getD j false := by
  induction gs generalizing w v with
  | nil => exact agree
  | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun h hh => avoid h (by simp [hh]))
      · simp [step, hlen]
      · simp [step]; omega
      · intro j hji
        have hg : g.op.eval (g.inputs.map fun k => w.getD k false) =
            g.op.eval (g.inputs.map fun k => v.getD k false) := by
          congr 1
          apply List.map_congr_left
          intro k hk
          apply agree k
          intro hki
          exact avoid g (by simp) (hki ▸ hk)
        simp only [step, getD_snoc, hlen, hg, agree j hji]

def AboveExcept (i : ℕ) (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ j, j ≠ i → w.getD j false = true → v.getD j false = true

lemma above_snoc (i : ℕ) (w v : List Bool) (a b : Bool)
    (h : AboveExcept i w v) (hab : a = true → b = true) :
    AboveExcept i (w ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hji hj
  simp only [getD_snoc, ← h.1] at hj ⊢
  by_cases he : j = w.length
  · simp only [he, if_true] at hj ⊢
    exact hab hj
  · simp only [he, if_false] at hj ⊢
    exact h.2 j hji hj

lemma fold_above_except (gs : List Gate) (i : ℕ)
    (avoid : ∀ g ∈ gs, i ∉ g.inputs)
    (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (h : AboveExcept i w v) :
    AboveExcept i (gs.foldl step w) (gs.foldl step v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g hg => avoid g (by simp [hg]))
        (fun g hg => mono g (by simp [hg]))
      apply above_snoc i w v
      · exact h
      · rcases mono g (by simp) with hg | hg
        · rw [hg]
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
          intro hall b hb
          obtain ⟨j, hj, rfl⟩ := hb
          apply h.2 j
          · intro hji
            exact avoid g (by simp) (hji ▸ hj)
          · exact hall _ ⟨j, hj, rfl⟩
        · rw [hg]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
          refine ⟨_, ⟨j, hj, rfl⟩, h.2 j ?_ hb⟩
          intro hji
          exact avoid g (by simp) (hji ▸ hj)

lemma sole_not_antitone (pre post : List Gate) (i out : ℕ)
    (preAvoid : ∀ g ∈ pre, i ∉ g.inputs)
    (postAvoid : ∀ g ∈ post, i ∉ g.inputs)
    (postMono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w0 w1 : List Bool) (hlen : w0.length = w1.length)
    (hi : i < w0.length) (hz : w0.getD i false = false) (ho : w1.getD i false = true)
    (agree : ∀ j, j ≠ i → w0.getD j false = w1.getD j false)
    (outne : out ≠ i) :
    (Circuit.mk (pre ++ ⟨GateOp.not, [i]⟩ :: post) out).eval w1 = true →
      (Circuit.mk (pre ++ ⟨GateOp.not, [i]⟩ :: post) out).eval w0 = true := by
  have hp := fold_agree_except pre i preAvoid w0 w1 hlen hi agree
  have hpre : AboveExcept i (pre.foldl step w1) (pre.foldl step w0) := by
    refine ⟨by simp [fold_length, hlen], ?_⟩
    intro j hji hj
    rw [hp j hji]
    exact hj
  have hn : AboveExcept i
      (step (pre.foldl step w1) ⟨GateOp.not, [i]⟩)
      (step (pre.foldl step w0) ⟨GateOp.not, [i]⟩) := by
    apply above_snoc i _ _ _ _ hpre
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
      fold_input pre w0 i hi, fold_input pre w1 i (by omega), hz, ho,
      Bool.not_false, Bool.not_true]
    simp
  have hpost := fold_above_except post i postAvoid postMono _ _ hn
  change ((pre ++ ⟨GateOp.not, [i]⟩ :: post).foldl step w1).getD out false = true →
    ((pre ++ ⟨GateOp.not, [i]⟩ :: post).foldl step w0).getD out false = true
  simpa only [List.foldl_append, List.foldl_cons] using hpost.2 out outne

end PEqualNP.Outside.L_meta_2592_aux.OneNot
