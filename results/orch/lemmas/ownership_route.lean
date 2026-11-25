import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i h
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C i k hk).1 h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i j, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i j hij hjk
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C j k hk).mp hjk
    · apply (inCone_iff n C i k hk).mpr
      exact ⟨w, hw, hn, hlt, Or.inr (h ▸ hij)⟩
    · apply (inCone_iff n C i k hk).mpr
      exact ⟨w, hw, hn, hlt, Or.inr (ih (w - n) (by omega) (by omega) i j hij h)⟩

lemma owned_ancestor (n : ℕ) (C : Circuit) (u v : Fin n) :
    ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      gateVal n C j (pairInput u v) = true →
      ∃ i, (i = j ∨ InCone n C i j) ∧ Owns n C i u v := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hand hval
    by_cases hown : Owns n C j u v
    · exact ⟨j, Or.inl rfl, hown⟩
    · have hex : ∃ i, i < j ∧ InCone n C i j ∧
          (gateAt C i).op = GateOp.and ∧ gateVal n C i (pairInput u v) = true := by
        by_contra hn
        apply hown
        refine ⟨hj, hand, hval, ?_⟩
        intro i hi hc ha
        cases hv : gateVal n C i (pairInput u v)
        · rfl
        · exact False.elim (hn ⟨i, hi, hc, ha, hv⟩)
      obtain ⟨i, hi, hc, ha, hv⟩ := hex
      obtain ⟨k, hk, hko⟩ := ih i hi (by omega) ha hv
      refine ⟨k, Or.inr ?_, hko⟩
      rcases hk with rfl | hki
      · exact hc
      · exact inCone_trans n C j hj k i hki hc

lemma nonowning_true_has_owning_ancestor (n : ℕ) (C : Circuit) (j : ℕ)
    (u v : Fin n) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hval : gateVal n C j (pairInput u v) = true) (hno : ¬ Owns n C j u v) :
    ∃ i, i < j ∧ InCone n C i j ∧ Owns n C i u v := by
  obtain ⟨i, hi, ho⟩ := owned_ancestor n C u v j hj hand hval
  rcases hi with rfl | hi
  · exact (hno ho).elim
  · exact ⟨i, inCone_lt n C j hj i hi, hi, ho⟩

end PEqualNP.Outside.L_meta_1772_aux
