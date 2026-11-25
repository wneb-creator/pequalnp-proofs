import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4923
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def SS (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => (wf C.gates (List.ofFn fun z : Fin n => decide (z = v))).getD w false = true

theorem ss_small (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) : (SS n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ v ∈ SS n C w, v = ⟨w, hw⟩ := by
    intro v hv
    have h := (Finset.mem_filter.1 hv).2
    rw [wf_keep _ _ w (by rw [List.length_ofFn]; exact hw)] at h
    have e := getD_ofFn (fun z : Fin n => decide (z = v)) ⟨w, hw⟩
    rw [e] at h
    exact (of_decide_eq_true h).symm
  intro a ha b hb
  rw [key a ha, key b hb]

theorem ss_big (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) : SS n C w = ∅ := by
  apply Finset.filter_eq_empty_iff.2
  intro v _
  rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_ofFn]; exact hw)]
  decide

theorem mem_ss (n : ℕ) (C : Circuit) (hOR : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < C.gates.length) (v : Fin n) :
    v ∈ SS n C (n + j) ↔ ∃ i ∈ C.gates[j].inputs, i < n + j ∧ v ∈ SS n C i := by
  have hval := gate_val C.gates (List.ofFn fun z : Fin n => decide (z = v)) j hj
  rw [List.length_ofFn, (hOR _ (List.getElem_mem hj)).1] at hval
  unfold SS
  rw [Finset.mem_filter, hval]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id, Finset.mem_univ,
    true_and, Finset.mem_filter]
  constructor
  · rintro ⟨i, hi, hv⟩
    have hlt : i < n + j := by
      by_contra hge
      rw [List.getD_eq_default _ _ (by
        rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hj)]; omega)] at hv
      exact absurd hv (by decide)
    refine ⟨i, hi, hlt, ?_⟩
    rw [wire_take C.gates _ j i (by rw [List.length_ofFn]; exact hlt) (le_of_lt hj)]
    exact hv
  · rintro ⟨i, hi, hlt, hv⟩
    refine ⟨i, hi, ?_⟩
    rw [← wire_take C.gates _ j i (by rw [List.length_ofFn]; exact hlt) (le_of_lt hj)]
    exact hv

end PEqualNP.Outside.L_meta_4923

open PEqualNP.Outside.L_meta_4923 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4923 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x3 ∈ x2.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs.length ≤ (2 : ℕ)) →     ∃ (x4 : List (Finset (Fin x1))),       x4.length ≤ x2.size ∧         (∀ (x5 : ℕ),             have x6 : Finset (Fin x1) := {x6 : Fin x1 | (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 = x6))).getD x5 Bool.false = Bool.true};             x6.card ≤ (1 : ℕ) ∨ x6 ∈ x4) ∧           ∀ (x5 : ℕ) (x6 : Finset (Fin x1)), x4[x5]? = Option.some x6 → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1)), x6 = x8 ∪ x9 ∧ (x8.card ≤ (1 : ℕ) ∨ x8 ∈ List.take x5 x4) ∧ (x9.card ≤ (1 : ℕ) ∨ x9 ∈ List.take x5 x4) := by
  intro n C hOR
  refine ⟨(List.range C.gates.length).map (fun j => SS n C (n + j)), ?_, ?_, ?_⟩
  · show ((List.range C.gates.length).map (fun j => SS n C (n + j))).length ≤ C.gates.length
    simp
  · intro w
    show (SS n C w).card ≤ 1 ∨ SS n C w ∈ (List.range C.gates.length).map (fun j => SS n C (n + j))
    by_cases h1 : w < n
    · exact Or.inl (ss_small n C w h1)
    · by_cases h2 : w < n + C.gates.length
      · right
        exact List.mem_map.2 ⟨w - n, List.mem_range.2 (by omega), by
          show SS n C (n + (w - n)) = SS n C w
          congr 1
          omega⟩
      · left
        rw [ss_big n C w (by omega)]
        simp
  · intro j T hT
    obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.1 hT
    have hj' : j < C.gates.length := by simpa using hj
    have eT : T = SS n C (n + j) := by
      rw [← e]
      simp
    have okp : ∀ i, (if i < n + j then SS n C i else ∅).card ≤ 1 ∨
        (if i < n + j then SS n C i else ∅) ∈
          List.take j ((List.range C.gates.length).map (fun j => SS n C (n + j))) := by
      intro i
      by_cases h1 : i < n + j
      · rw [if_pos h1]
        by_cases h2 : i < n
        · exact Or.inl (ss_small n C i h2)
        · right
          rw [← List.map_take, List.take_range]
          exact List.mem_map.2 ⟨i - n, List.mem_range.2 (by rw [Nat.lt_min]; omega), by
            show SS n C (n + (i - n)) = SS n C i
            congr 1
            omega⟩
      · rw [if_neg h1]
        left
        simp
    have mp : ∀ (i : ℕ) (v : Fin n), v ∈ (if i < n + j then SS n C i else ∅) ↔
        (i < n + j ∧ v ∈ SS n C i) := by
      intro i v
      by_cases h1 : i < n + j
      · rw [if_pos h1]; exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
      · rw [if_neg h1]; exact ⟨fun h => absurd h (Finset.notMem_empty v), fun h => absurd h.1 h1⟩
    have hlen := (hOR _ (List.getElem_mem hj')).2
    rw [eT]
    match hin : C.gates[j].inputs, hlen with
    | [], _ =>
      refine ⟨∅, ∅, ?_, Or.inl (by simp), Or.inl (by simp)⟩
      ext v
      rw [mem_ss n C hOR j hj' v, hin]
      simp
    | [a], _ =>
      refine ⟨if a < n + j then SS n C a else ∅, ∅, ?_, okp a, Or.inl (by simp)⟩
      ext v
      rw [mem_ss n C hOR j hj' v, hin, Finset.union_empty, mp]
      constructor
      · rintro ⟨i, hi, h⟩
        rw [List.mem_singleton] at hi
        rw [hi] at h
        exact h
      · intro h
        exact ⟨a, List.mem_singleton.2 rfl, h⟩
    | [a, b], _ =>
      refine ⟨if a < n + j then SS n C a else ∅, if b < n + j then SS n C b else ∅, ?_, okp a, okp b⟩
      ext v
      rw [mem_ss n C hOR j hj' v, hin, Finset.mem_union, mp, mp]
      constructor
      · rintro ⟨i, hi, h⟩
        rcases List.mem_pair.1 hi with e1 | e1
        · rw [e1] at h; exact Or.inl h
        · rw [e1] at h; exact Or.inr h
      · rintro (h | h)
        · exact ⟨a, by simp, h⟩
        · exact ⟨b, by simp, h⟩
    | _ :: _ :: _ :: _, h => exact absurd h (by simp)
