import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.CompareNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk


lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma suffix_bit_monotone (Q : Circuit)
    (mono : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : List Bool) :
    Q.eval (w ++ [false]) = true → Q.eval (w ++ [true]) = true := by
  apply monotone_foldl_wiresStep Q.gates mono _ _ (by simp)
  intro i hi
  by_cases last : i = w.length
  · simp [last] at hi
  · rw [getD_snoc_ne w false i last] at hi
    rw [getD_snoc_ne w true i last]
    exact hi

lemma replace_last_not_true {n : ℕ} (P Q : Circuit)
    (mono : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (covered : ∀ x : Fin n → Bool, P.eval (List.ofFn x) = true →
      Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) = true) :
    ∀ x : Fin n → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [true]) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  intro x
  cases h : P.eval (List.ofFn x) with
  | false => simp only [Bool.not_false]
  | true =>
    have old : Q.eval (P.wires (List.ofFn x) ++ [false]) = true := by
      simpa only [h, Bool.not_true] using covered x h
    have changed := suffix_bit_monotone Q mono (P.wires (List.ofFn x)) old
    simpa only [h, Bool.not_true, old] using changed

lemma replace_last_not_false {n : ℕ} (P Q : Circuit)
    (mono : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (covering : ∀ x : Fin n → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) = true →
        P.eval (List.ofFn x) = true) :
    ∀ x : Fin n → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [false]) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  intro x
  cases h : P.eval (List.ofFn x) with
  | true => simp only [Bool.not_true]
  | false =>
    have old : Q.eval (P.wires (List.ofFn x) ++ [true]) = false := by
      apply Bool.eq_false_iff.mpr
      intro bad
      have impossible := covering x (by simpa only [h, Bool.not_false] using bad)
      rw [h] at impossible
      cases impossible
    have changed : Q.eval (P.wires (List.ofFn x) ++ [false]) = false := by
      apply Bool.eq_false_iff.mpr
      intro bad
      have impossible := suffix_bit_monotone Q mono (P.wires (List.ofFn x)) bad
      rw [old] at impossible
      cases impossible
    simpa only [h, Bool.not_false, old] using changed

end PEqualNP.Outside.L_meta_2592_aux.CompareNot
