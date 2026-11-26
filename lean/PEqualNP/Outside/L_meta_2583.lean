import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.SingleUse

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hC : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (hC j hj i hi)]

lemma wv_missing (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (hw : n + C.gates.length ≤ w) : wv n C x w = false := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_eq, foldl_len, List.length_ofFn]
  unfold wv
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wv_mono (n : ℕ) (C : Circuit) (hAO : AndOrOnly C) (hC : ReadsBack n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w : ℕ, wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn, wv_input n C y w hwn]
      exact hxy ⟨w, hwn⟩
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n C x w hwg]
      intro h
      cases h
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; omega
      have hnw : n + k = w := by dsimp [k]; omega
      have hmem : gateAt C k ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        exact List.getElem_mem hk
      rw [← hnw, wv_rec n C x hC k hk, wv_rec n C y hC k hk]
      apply gateOp_mono _ (hAO _ hmem)
      intro u hu hux
      exact ih u (by have := hC k hk u hu; omega) hux

end PEqualNP.Outside.L_meta_2583.SingleUse
namespace PEqualNP.Outside.L_meta_2583.Minterm

lemma support_family_bound {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s) :
    ∀ t : Finset ℕ, t ⊆ Finset.range (n + m) →
      (t.biUnion s).card ≤ (Finset.range m).sum cost + t.card := by
  induction m with
  | zero =>
    intro t ht
    have h1 := Finset.card_biUnion_le (s := t) (t := s)
    have h2 : ∑ i ∈ t, (s i).card ≤ t.card := by
      calc
        ∑ i ∈ t, (s i).card ≤ ∑ i ∈ t, 1 := Finset.sum_le_sum fun i hi =>
          hinput i (by have := ht hi; simpa using this)
        _ = t.card := by simp
    simpa using h1.trans h2
  | succ m ih =>
    intro t ht
    have hb : ∀ k < m, a k ⊆ Finset.range (n + k) := fun k hk => hback k (by omega)
    have hc : ∀ k < m, (a k).card ≤ cost k + 1 := fun k hk => hcost k (by omega)
    have hv : ∀ k < m, s (n + k) ⊆ (a k).biUnion s := fun k hk => hcover k (by omega)
    by_cases hm : n + m ∈ t
    · let u := t.erase (n + m) ∪ a m
      have hu : u ⊆ Finset.range (n + m) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hit⟩ := Finset.mem_erase.mp hi
          have hi' := Finset.mem_range.mp (ht hit)
          exact Finset.mem_range.mpr (by omega)
        · exact hback m (by omega) hi
      have hsub : t.biUnion s ⊆ u.biUnion s := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := Finset.mem_biUnion.mp hx
        by_cases him : i = n + m
        · subst i
          obtain ⟨j, hja, hxj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hxi)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hja, hxj⟩
        · exact Finset.mem_biUnion.mpr ⟨i,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨him, hit⟩), hxi⟩
      have huc : u.card ≤ t.card + cost m := by
        have h1 := Finset.card_union_le (t.erase (n + m)) (a m)
        have h2 := Finset.card_erase_add_one hm
        have h3 := hcost m (by omega)
        dsimp only [u]
        omega
      have hbound := ih hb hc hv u hu
      have hsmall := Finset.card_le_card hsub
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega
    · have ht' : t ⊆ Finset.range (n + m) := by
        intro i hi
        have hi' := Finset.mem_range.mp (ht hi)
        have hne : i ≠ n + m := by intro h; subst i; exact hm hi
        exact Finset.mem_range.mpr (by omega)
      have hbound := ih hb hc hv t ht'
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega

def pickedSupport (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (w : ℕ) : Finset (Fin n) :=
  if hw : w < n then {⟨w, hw⟩}
  else if _hg : w < n + m then
    if both (w - n) then
      pickedSupport n m a b both left ha hb (a (w - n)) ∪
      pickedSupport n m a b both left ha hb (b (w - n))
    else if left (w - n) then
      pickedSupport n m a b both left ha hb (a (w - n))
    else pickedSupport n m a b both left ha hb (b (w - n))
  else ∅
termination_by w
decreasing_by
  all_goals have hk : w - n < m := by omega
  · have := ha (w - n) hk; omega
  · have := hb (w - n) hk; omega
  · have := ha (w - n) hk; omega
  · have := hb (w - n) hk; omega

lemma pickedSupport_input (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (w : ℕ) (hw : w < n) :
    pickedSupport n m a b both left ha hb w = {⟨w, hw⟩} := by
  rw [pickedSupport, dite_eq_left hw]

lemma pickedSupport_gate (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (k : ℕ) (hk : k < m) :
    pickedSupport n m a b both left ha hb (n + k) =
      if both k then
        pickedSupport n m a b both left ha hb (a k) ∪
        pickedSupport n m a b both left ha hb (b k)
      else if left k then pickedSupport n m a b both left ha hb (a k)
      else pickedSupport n m a b both left ha hb (b k) := by
  rw [pickedSupport, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp only [Nat.add_sub_cancel_left]

lemma pickedSupport_bound (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (w : ℕ) (hw : w < n + m) :
    (pickedSupport n m a b both left ha hb w).card ≤
      ((Finset.range m).filter fun k => both k = true).card + 1 := by
  let s := pickedSupport n m a b both left ha hb
  let parents : ℕ → Finset ℕ := fun k =>
    if both k then {a k, b k} else if left k then {a k} else {b k}
  let cost : ℕ → ℕ := fun k => if both k then 1 else 0
  have hinput : ∀ i < n, (s i).card ≤ 1 := by
    intro i hi
    simp [s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k hk)
      · exact Finset.mem_range.mpr (hb k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k hk)
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k _
    simp only [parents, cost]
    split_ifs <;> first | exact Finset.card_le_two | simp
  have hv : ∀ k < m, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    dsimp only [s, parents]
    rw [pickedSupport_gate n m a b both left ha hb k hk]
    split_ifs <;> simp
  have hmain := support_family_bound n m s parents cost hinput hp hc hv {w}
    (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact Finset.mem_range.mpr hw)
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  simpa [s, hsum] using hmain

lemma pickedSupport_bound_closed (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (R : Finset ℕ)
    (hRa : ∀ k ∈ R, k < m → a k < n ∨ a k - n ∈ R)
    (hRb : ∀ k ∈ R, k < m → b k < n ∨ b k - n ∈ R)
    (w : ℕ) (hw : w < n + m) (hwR : w < n ∨ w - n ∈ R) :
    (pickedSupport n m a b both left ha hb w).card ≤
      ((Finset.range m).filter fun k => k ∈ R ∧ both k = true).card + 1 := by
  let s := pickedSupport n m a b both left ha hb
  let ss : ℕ → Finset (Fin n) := fun v => if v < n ∨ v - n ∈ R then s v else ∅
  let parents : ℕ → Finset ℕ := fun k => if k ∈ R then
    if both k then {a k, b k} else if left k then {a k} else {b k}
    else ∅
  let cost : ℕ → ℕ := fun k => if k ∈ R ∧ both k = true then 1 else 0
  have hinput : ∀ i < n, (ss i).card ≤ 1 := by
    intro i hi
    simp [ss, hi, s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with hR h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k hk)
      · exact Finset.mem_range.mpr (hb k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k hk)
    · exact False.elim (Finset.notMem_empty _ hi)
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k _
    dsimp only [parents, cost]
    split_ifs <;> simp_all
    exact Finset.card_le_two
  have hv : ∀ k < m, ss (n + k) ⊆ (parents k).biUnion ss := by
    intro k hk
    by_cases hkR : k ∈ R
    · have hs0 : ss (n + k) = s (n + k) := by simp [ss, hkR]
      have hsa : ss (a k) = s (a k) := by rw [show ss (a k) = if a k < n ∨ a k - n ∈ R then s (a k) else ∅ from rfl, ite_eq_left (hRa k hkR hk)]
      have hsb : ss (b k) = s (b k) := by rw [show ss (b k) = if b k < n ∨ b k - n ∈ R then s (b k) else ∅ from rfl, ite_eq_left (hRb k hkR hk)]
      rw [hs0]
      change pickedSupport n m a b both left ha hb (n + k) ⊆ _
      rw [pickedSupport_gate n m a b both left ha hb k hk]
      simp only [parents, hkR, ↓reduceIte]
      split_ifs <;> simp [hsa, hsb, s]
    · have hs0 : ss (n + k) = ∅ := by simp [ss, hkR]
      rw [hs0]
      exact Finset.empty_subset _
  have hmain := support_family_bound n m ss parents cost hinput hp hc hv {w}
    (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact Finset.mem_range.mpr hw)
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => k ∈ R ∧ both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  simpa [ss, hwR, s, hsum] using hmain

end PEqualNP.Outside.L_meta_2583.Minterm
namespace PEqualNP.Outside.L_meta_2583.MintermCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm

lemma gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

lemma inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gate_mem C k hk))
  simp [opnd, hin]

lemma opnd_back (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) : opnd C k b < n + k := by
  apply hAO.2.1 k hk
  rw [inputs_two n C hAO k hk]
  fin_cases b <;> simp

def pickedBoth (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => wv n C x (n + k)
  | _ => false

def circuitSupport (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) : Finset (Fin n) :=
  pickedSupport n C.gates.length (fun k => opnd C k 0) (fun k => opnd C k 1)
    (pickedBoth n C x) (fun k => wv n C x (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w

lemma circuitSupport_input (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    circuitSupport n C hAO x w = {⟨w, hw⟩} := by
  exact pickedSupport_input _ _ _ _ _ _ _ _ _ hw

lemma circuitSupport_gate (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    circuitSupport n C hAO x (n + k) =
      if pickedBoth n C x k then
        circuitSupport n C hAO x (opnd C k 0) ∪ circuitSupport n C hAO x (opnd C k 1)
      else if wv n C x (opnd C k 0) then circuitSupport n C hAO x (opnd C k 0)
      else circuitSupport n C hAO x (opnd C k 1) := by
  exact pickedSupport_gate _ _ _ _ _ _ _ _ _ hk

lemma support_sound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (S : Finset (Fin n)) :
    ∀ w : ℕ, wv n C (setInput S) w = true →
      circuitSupport n C hAO (setInput S) w ⊆ S ∧
      wv n C (setInput (circuitSupport n C hAO (setInput S) w)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwtrue
    by_cases hwn : w < n
    · rw [circuitSupport_input n C hAO (setInput S) w hwn]
      rw [wv_input n C (setInput S) w hwn] at hwtrue
      constructor
      · simp only [Finset.singleton_subset_iff]
        exact of_decide_eq_true hwtrue
      · rw [wv_input n C _ w hwn]
        simp [setInput]
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n C (setInput S) w hwg] at hwtrue
      cases hwtrue
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have ha : opnd C k 0 < n + k := opnd_back n C hAO k hk 0
      have hb : opnd C k 1 < n + k := opnd_back n C hAO k hk 1
      have hgate := wv_rec n C (setInput S) hAO.2.1 k hk
      rw [inputs_two n C hAO k hk] at hgate
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hbits : wv n C (setInput S) (opnd C k 0) = true ∧
            wv n C (setInput S) (opnd C k 1) = true := by
          simpa [hop, GateOp.eval] using hgate.symm.trans hwtrue
        have hsa := ih _ ha hbits.1
        have hsb := ih _ hb hbits.2
        rw [circuitSupport_gate n C hAO (setInput S) k hk]
        simp only [pickedBoth, hop, hwtrue, ↓reduceIte]
        change circuitSupport n C hAO (setInput S) (opnd C k 0) ∪
            circuitSupport n C hAO (setInput S) (opnd C k 1) ⊆ S ∧ _
        constructor
        · exact Finset.union_subset hsa.1 hsb.1
        · have hma := wv_mono n C hAO.1 hAO.2.1 _
              (setInput (circuitSupport n C hAO (setInput S) (opnd C k 0) ∪
                circuitSupport n C hAO (setInput S) (opnd C k 1)))
              (fun i hi => by
                simp only [setInput, decide_eq_true_eq] at hi ⊢
                exact Finset.mem_union_left _ hi) _ hsa.2
          have hmb := wv_mono n C hAO.1 hAO.2.1 _
              (setInput (circuitSupport n C hAO (setInput S) (opnd C k 0) ∪
                circuitSupport n C hAO (setInput S) (opnd C k 1)))
              (fun i hi => by
                simp only [setInput, decide_eq_true_eq] at hi ⊢
                exact Finset.mem_union_right _ hi) _ hsb.2
          rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
          simpa [hop, GateOp.eval] using And.intro hma hmb
      · have hbits : wv n C (setInput S) (opnd C k 0) = true ∨
            wv n C (setInput S) (opnd C k 1) = true := by
          simpa [hop, GateOp.eval] using hgate.symm.trans hwtrue
        rw [circuitSupport_gate n C hAO (setInput S) k hk]
        simp only [pickedBoth, hop, Bool.false_eq_true, ↓reduceIte]
        by_cases hat : wv n C (setInput S) (opnd C k 0) = true
        · rw [ite_eq_left hat]
          have hsa := ih _ ha hat
          refine ⟨hsa.1, ?_⟩
          rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp [hop, GateOp.eval, hsa.2]
        · rw [ite_eq_right hat]
          have hsb := ih _ hb (hbits.resolve_left hat)
          refine ⟨hsb.1, ?_⟩
          rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp [hop, GateOp.eval, hsb.2]

lemma minimal_support_card_le_true_ands (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) (hw : wv n C (setInput S) w = true)
    (hmin : ∀ T ⊆ S, wv n C (setInput T) w = true → S ⊆ T) :
    S.card ≤ ((Finset.range C.gates.length).filter fun k =>
      pickedBoth n C (setInput S) k = true).card + 1 := by
  classical
  have hvalid : w < n + C.gates.length := by
    by_contra h
    rw [wv_missing n C (setInput S) w (by omega)] at hw
    cases hw
  have hsound := support_sound n C hAO S w hw
  have hS : S = circuitSupport n C hAO (setInput S) w :=
    Finset.Subset.antisymm (hmin _ hsound.1 hsound.2) hsound.1
  have hbound := pickedSupport_bound n C.gates.length (fun k => opnd C k 0)
    (fun k => opnd C k 1) (pickedBoth n C (setInput S))
    (fun k => wv n C (setInput S) (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w hvalid
  calc
    S.card = (circuitSupport n C hAO (setInput S) w).card := congrArg Finset.card hS
    _ ≤ _ := hbound

end PEqualNP.Outside.L_meta_2583.MintermCircuit
namespace PEqualNP.Outside.L_meta_2583.TopNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

open Classical in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

end PEqualNP.Outside.L_meta_2583.TopNormal

namespace PEqualNP.Outside.L_meta_2583.SharedSupport

open PEqualNP.Outside.L_meta_2583.Minterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma support_family_bound_anchor {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s) (x : α) :
    ∀ t : Finset ℕ, t ⊆ Finset.range (n + m) →
      (t.biUnion s).card ≤ (Finset.range m).sum cost +
        (t.filter (fun i => x ∉ s i)).card + 1 := by
  induction m with
  | zero =>
    intro t ht
    have hinput' : ∀ i ∈ t, (s i).card ≤ 1 := by
      intro i hi
      exact hinput i (by have := ht hi; simpa using this)
    have hsub : t.biUnion s ⊆ insert x ((t.filter (fun i => x ∉ s i)).biUnion s) := by
      intro y hy
      obtain ⟨i, hit, hyi⟩ := Finset.mem_biUnion.mp hy
      by_cases hyx : y = x
      · exact Finset.mem_insert.mpr (Or.inl hyx)
      · apply Finset.mem_insert.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, hyi⟩
        intro hxi
        exact hyx (Finset.card_le_one.mp (hinput' i hit) y hyi x hxi)
    have h1 := Finset.card_biUnion_le (s := t.filter (fun i => x ∉ s i)) (t := s)
    have h2 : ∑ i ∈ t.filter (fun i => x ∉ s i), (s i).card ≤
        (t.filter (fun i => x ∉ s i)).card := by
      calc
        _ ≤ ∑ i ∈ t.filter (fun i => x ∉ s i), 1 :=
          Finset.sum_le_sum fun i hi => hinput' i (Finset.mem_filter.mp hi).1
        _ = _ := by simp
    have h3 := Finset.card_insert_le x ((t.filter (fun i => x ∉ s i)).biUnion s)
    have h4 := Finset.card_le_card hsub
    simpa using (show (t.biUnion s).card ≤ (t.filter (fun i => x ∉ s i)).card + 1 by omega)
  | succ m ih =>
    intro t ht
    have hb : ∀ k < m, a k ⊆ Finset.range (n + k) := fun k hk => hback k (by omega)
    have hc : ∀ k < m, (a k).card ≤ cost k + 1 := fun k hk => hcost k (by omega)
    have hv : ∀ k < m, s (n + k) ⊆ (a k).biUnion s := fun k hk => hcover k (by omega)
    by_cases hm : n + m ∈ t
    · let u := t.erase (n + m) ∪ a m
      have hu : u ⊆ Finset.range (n + m) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hit⟩ := Finset.mem_erase.mp hi
          have hi' := Finset.mem_range.mp (ht hit)
          exact Finset.mem_range.mpr (by omega)
        · exact hback m (by omega) hi
      have hsub : t.biUnion s ⊆ u.biUnion s := by
        intro y hy
        obtain ⟨i, hit, hyi⟩ := Finset.mem_biUnion.mp hy
        by_cases him : i = n + m
        · subst i
          obtain ⟨j, hja, hyj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hyi)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hja, hyj⟩
        · exact Finset.mem_biUnion.mpr ⟨i,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨him, hit⟩), hyi⟩
      have huc : (u.filter (fun i => x ∉ s i)).card ≤
          (t.filter (fun i => x ∉ s i)).card + cost m := by
        have heq : u.filter (fun i => x ∉ s i) =
            (t.filter (fun i => x ∉ s i)).erase (n + m) ∪
              (a m).filter (fun i => x ∉ s i) := by
          ext i
          simp only [u, Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
          tauto
        rw [heq]
        have h1 := Finset.card_union_le
          ((t.filter (fun i => x ∉ s i)).erase (n + m)) ((a m).filter (fun i => x ∉ s i))
        have h3 := hcost m (by omega)
        by_cases hxm : x ∈ s (n + m)
        · obtain ⟨j, hja, hxj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hxm)
          have hjsub : (a m).filter (fun i => x ∉ s i) ⊆ (a m).erase j := by
            intro i hi
            obtain ⟨hia, hxi⟩ := Finset.mem_filter.mp hi
            refine Finset.mem_erase.mpr ⟨?_, hia⟩
            intro heq
            exact hxi (heq.symm ▸ hxj)
          have h2 := Finset.card_erase_add_one hja
          have h4 := Finset.card_le_card hjsub
          have h5 := Finset.card_le_card (Finset.erase_subset (n + m)
            (t.filter (fun i => x ∉ s i)))
          omega
        · have hmem : n + m ∈ t.filter (fun i => x ∉ s i) := Finset.mem_filter.mpr ⟨hm, hxm⟩
          have h2 := Finset.card_erase_add_one hmem
          have h4 := Finset.card_filter_le (a m) (fun i => x ∉ s i)
          omega
      have hbound := ih hb hc hv u hu
      have hsmall := Finset.card_le_card hsub
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m +
        (t.filter (fun i => x ∉ s i)).card + 1
      omega
    · have ht' : t ⊆ Finset.range (n + m) := by
        intro i hi
        have hi' := Finset.mem_range.mp (ht hi)
        have hne : i ≠ n + m := by intro h; subst i; exact hm hi
        exact Finset.mem_range.mpr (by omega)
      have hbound := ih hb hc hv t ht'
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m +
        (t.filter (fun i => x ∉ s i)).card + 1
      omega



lemma support_family_bound_anchor_closed {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s)
    (R : Finset ℕ)
    (hR : ∀ k ∈ R, k < m → ∀ j ∈ a k, j < n ∨ j - n ∈ R)
    (W : Finset ℕ) (hW : W ⊆ Finset.range (n + m))
    (hWR : ∀ w ∈ W, w < n ∨ w - n ∈ R)
    (x : α) (hshare : ∀ w ∈ W, x ∈ s w) :
    (W.biUnion s).card ≤ ((Finset.range m).filter (fun k => k ∈ R)).sum cost + 1 := by
  let ss : ℕ → Finset α := fun v => if v < n ∨ v - n ∈ R then s v else ∅
  let aa : ℕ → Finset ℕ := fun k => if k ∈ R then a k else ∅
  let cc : ℕ → ℕ := fun k => if k ∈ R then cost k else 0
  have hi : ∀ i < n, (ss i).card ≤ 1 := by
    intro i hi
    simpa only [ss, ite_eq_left (Or.inl hi)] using hinput i hi
  have hb : ∀ k < m, aa k ⊆ Finset.range (n + k) := by
    intro k hk
    by_cases hkR : k ∈ R
    · simpa only [aa, ite_eq_left hkR] using hback k hk
    · simp [aa, hkR]
  have hc : ∀ k < m, (aa k).card ≤ cc k + 1 := by
    intro k hk
    by_cases hkR : k ∈ R
    · simpa only [aa, cc, ite_eq_left hkR] using hcost k hk
    · simp [aa, cc, hkR]
  have hv : ∀ k < m, ss (n + k) ⊆ (aa k).biUnion ss := by
    intro k hk y hy
    by_cases hkR : k ∈ R
    · have hs : ss (n + k) = s (n + k) := by simp [ss, hkR]
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp (hcover k hk (hs ▸ hy))
      have hsj : ss j = s j := by simp only [ss, ite_eq_left (hR k hkR hk j hj)]
      exact Finset.mem_biUnion.mpr ⟨j, by simpa [aa, hkR] using hj, hsj.symm ▸ hyj⟩
    · simp [ss, hkR] at hy
  have heq : W.biUnion ss = W.biUnion s := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hWR w hw)
  have hzero : W.filter (fun w => x ∉ ss w) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw hnot
    apply hnot
    simpa only [ss, ite_eq_left (hWR w hw)] using hshare w hw
  have hbound := support_family_bound_anchor n m ss aa cc hi hb hc hv x W hW
  have hsum : (Finset.range m).sum cc =
      ((Finset.range m).filter (fun k => k ∈ R)).sum cost := by
    simp only [cc, Finset.sum_filter]
  simpa only [heq, hzero, Finset.card_empty, Nat.add_zero, hsum] using hbound


end PEqualNP.Outside.L_meta_2583.SharedSupport

namespace PEqualNP.Outside.L_meta_2583.BiasedSupport

open PEqualNP.Outside.L_meta_2583.Minterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

def andSelector (C : Circuit) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => true
  | _ => false

def selectedSupport (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (left : ℕ → Bool) (w : ℕ) : Finset (Fin n) :=
  pickedSupport n C.gates.length (fun k => opnd C k 0) (fun k => opnd C k 1)
    (andSelector C) left
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w

lemma selectedSupport_sound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (left : ℕ → Bool) :
    ∀ w, w < n + C.gates.length →
      wv n C (setInput (selectedSupport n C hAO left w)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [show selectedSupport n C hAO left w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      rw [wv_input n C _ w hwn]
      simp [setInput]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      have hval (v : ℕ) (hv : v < n + k)
          (hsub : selectedSupport n C hAO left v ⊆ selectedSupport n C hAO left (n + k)) :
          wv n C (setInput (selectedSupport n C hAO left (n + k))) v = true :=
        wv_mono n C hAO.1 hAO.2.1 _ _
          (fun i hi => decide_eq_true (hsub (of_decide_eq_true hi))) v
          (ih v hv (by omega))
      have hrec : selectedSupport n C hAO left (n + k) =
          if andSelector C k then
            selectedSupport n C hAO left (opnd C k 0) ∪ selectedSupport n C hAO left (opnd C k 1)
          else if left k then selectedSupport n C hAO left (opnd C k 0)
          else selectedSupport n C hAO left (opnd C k 1) :=
        pickedSupport_gate _ _ _ _ _ _ _ _ _ hk
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hs : andSelector C k = true := by simp [andSelector, hop]
        rw [hs] at hrec
        simp only [↓reduceIte] at hrec
        have hv0 := hval _ ha (by rw [hrec]; exact Finset.subset_union_left)
        have hv1 := hval _ hb (by rw [hrec]; exact Finset.subset_union_right)
        simp [hop, GateOp.eval, hv0, hv1]
      · have hs : andSelector C k = false := by simp [andSelector, hop]
        rw [hs] at hrec
        simp only [Bool.false_eq_true, ↓reduceIte] at hrec
        by_cases hl : left k = true
        · have hv0 := hval _ ha (by rw [hrec, ite_eq_left hl])
          simp [hop, GateOp.eval, hv0]
        · have hv1 := hval _ hb (by rw [hrec, ite_eq_right hl])
          simp [hop, GateOp.eval, hv1]


def fullSupport (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) : Finset (Fin n) :=
  pickedSupport n C.gates.length (fun k => opnd C k 0) (fun k => opnd C k 1)
    (fun _ => true) (fun _ => true)
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w

end PEqualNP.Outside.L_meta_2583.BiasedSupport

namespace PEqualNP.Outside.L_meta_2583.AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

def isAnd (C : Circuit) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => true
  | _ => false

def andPrefix (C : Circuit) (r : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun k => isAnd C k = true)

end PEqualNP.Outside.L_meta_2583.AndSignature

namespace PEqualNP.Outside.L_meta_2583.AncestorJunk

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.MintermCircuit

/-- The strict ancestor gates together with the selected gate itself. -/
def gateCone (n : ℕ) (C : Circuit) (g : ℕ) : Finset ℕ :=
  insert g ((Finset.range g).filter (fun k => InCone n C k g))

lemma mem_gateCone (n : ℕ) (C : Circuit) (g k : ℕ) :
    k ∈ gateCone n C g ↔ k = g ∨ InCone n C k g := by
  constructor
  · intro hk
    rcases Finset.mem_insert.mp hk with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2
  · intro hk
    rcases hk with hk | hk
    · exact Finset.mem_insert.mpr (Or.inl hk)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (TopNormal.inCone_lt n C k g hk).1, hk⟩))

lemma gateCone_self (n : ℕ) (C : Circuit) (g : ℕ) : g ∈ gateCone n C g :=
  (mem_gateCone n C g g).mpr (Or.inl rfl)

lemma gateCone_prefix (n : ℕ) (C : Circuit) (g : ℕ) :
    gateCone n C g ⊆ Finset.range (g + 1) := by
  intro k hk
  rcases (mem_gateCone n C g k).mp hk with rfl | hk
  · exact Finset.mem_range.mpr (by omega)
  · exact Finset.mem_range.mpr (by have := (TopNormal.inCone_lt n C k g hk).1; omega)

lemma gateCone_real (n : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    gateCone n C g ⊆ Finset.range C.gates.length := by
  intro k hk
  have hkg := Finset.mem_range.mp (gateCone_prefix n C g hk)
  exact Finset.mem_range.mpr (by omega)

lemma gateCone_closed (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) :
    ∀ k ∈ gateCone n C g, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ gateCone n C g := by
  intro k hk b
  have hklen := Finset.mem_range.mp (gateCone_real n C g hg hk)
  by_cases hb : opnd C k b < n
  · exact Or.inl hb
  · right
    have hback := opnd_back n C hAO k hklen b
    have hread : opnd C k b ∈ (gateAt C k).inputs := by
      rw [inputs_two n C hAO k hklen]
      fin_cases b <;> simp
    have hdirect : InCone n C (opnd C k b - n) k := by
      apply (TopNormal.inCone_iff n C _ k).mpr
      refine ⟨hklen, opnd C k b - n, by omega, ?_, Or.inl rfl⟩
      have heq : n + (opnd C k b - n) = opnd C k b := by omega
      exact heq.symm ▸ hread
    apply (mem_gateCone n C g _).mpr
    right
    rcases (mem_gateCone n C g k).mp hk with rfl | hkg
    · exact hdirect
    · exact TopNormal.inCone_trans n C _ k hdirect g hkg

end PEqualNP.Outside.L_meta_2583.AncestorJunk

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma picked_true_ands_subset (n : Nat) (C : Circuit) (x : Fin n → Bool) :
    ((Finset.range C.gates.length).filter (fun k => pickedBoth n C x k = true)) ⊆
      AndSignature.andPrefix C C.gates.length := by
  intro k hk
  obtain ⟨hkr, hb⟩ := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨hkr, ?_⟩
  cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hb ⊢

lemma tight_true_ands_eq_all (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ((Finset.range C.gates.length).filter (fun k => pickedBoth n C (setInput T) k = true)) =
      AndSignature.andPrefix C C.gates.length := by
  have hbound := minimal_support_card_le_true_ands n C hAO T w htrue hmin
  apply Finset.eq_of_subset_of_card_le (picked_true_ands_subset n C (setInput T))
  omega

lemma tight_all_ands_true (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true := by
  intro k hk hop
  have hm : k ∈ AndSignature.andPrefix C C.gates.length := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simp [AndSignature.isAnd, hop]⟩
  rw [← tight_true_ands_eq_all n C hAO T w htrue hmin htight] at hm
  have hb := (Finset.mem_filter.mp hm).2
  simpa [pickedBoth, hop] using hb

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma true_ands_false_wire_is_outside_or
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C) (T : Finset (Fin n))
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true) :
    ∀ w, wv n C (setInput T) w = false →
      ∃ S : Finset (Fin n), (∀ i ∈ S, i ∉ T) ∧
        ∀ x, wv n C x w = true ↔ ∃ i ∈ S, x i = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hnot : (⟨w, hwn⟩ : Fin n) ∉ T := by
        rw [wv_input n C (setInput T) w hwn] at hw
        simpa [setInput] using hw
      refine ⟨{⟨w, hwn⟩}, ?_, ?_⟩
      · intro i hi
        have heq : i = ⟨w, hwn⟩ := Finset.mem_singleton.mp hi
        simpa [heq] using hnot
      · intro x
        rw [wv_input n C x w hwn]
        simp
    by_cases hwg : n + C.gates.length ≤ w
    · refine ⟨∅, by simp, ?_⟩
      intro x
      rw [wv_missing n C x w hwg]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have ht := hactive k hk hop
        rw [hw] at ht
        contradiction
      · have hgate := wv_rec n C (setInput T) hAO.2.1 k hk
        rw [inputs_two n C hAO k hk] at hgate
        have hbits : wv n C (setInput T) (opnd C k 0) = false ∧
            wv n C (setInput T) (opnd C k 1) = false := by
          simpa [hop, GateOp.eval] using hgate.symm.trans hw
        obtain ⟨A, hAT, hA⟩ := ih _ ha hbits.1
        obtain ⟨B, hBT, hB⟩ := ih _ hb hbits.2
        refine ⟨A ∪ B, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact hAT i hi
          · exact hBT i hi
        · intro x
          rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp [hop, GateOp.eval, hA x, hB x, Finset.mem_union, or_and_right, exists_or]

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.SafeProductTopology

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit
  PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma gateCone_mono (n : Nat) (C : Circuit) (k j : Nat) (hk : k ∈ gateCone n C j) :
    gateCone n C k ⊆ gateCone n C j := by
  intro i hi
  rcases (mem_gateCone n C j k).mp hk with rfl | hkj
  · exact hi
  · apply (mem_gateCone n C j i).mpr
    right
    rcases (mem_gateCone n C k i).mp hi with rfl | hik
    · exact hkj
    · exact TopNormal.inCone_trans n C i k hik j hkj

lemma max_and_forces_gate (n : Nat) (C : Circuit) (hAO : IsAO2 n C) (g : Nat) :
    ∀ k, k < C.gates.length → g ∈ gateCone n C k →
      (∀ j ∈ gateCone n C k, (gateAt C j).op = GateOp.and → j ≤ g) →
      ∀ x, gateVal n C g x = true → gateVal n C k x = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hg hmax x hx
    rcases (mem_gateCone n C k g).mp hg with heq | hanc
    · simpa only [heq] using hx
    · have hgk := (TopNormal.inCone_lt n C g k hanc).1
      rcases hAO.1 _ (gate_mem C k hk) with hand | hor
      · have := hmax k (gateCone_self n C k) hand
        omega
      · obtain ⟨_, j, hjk, hjin, hgj⟩ := (TopNormal.inCone_iff n C g k).mp hanc
        have hjcone : j ∈ gateCone n C k := by
          apply (mem_gateCone n C k j).mpr
          right
          exact (TopNormal.inCone_iff n C j k).mpr ⟨hk, j, hjk, hjin, Or.inl rfl⟩
        have hchild : gateVal n C j x = true :=
          ih j hjk (lt_trans hjk hk) ((mem_gateCone n C j g).mpr hgj)
            (fun l hl => hmax l (gateCone_mono n C j k hjcone hl)) x hx
        change wv n C x (n + k) = true
        rw [wv_rec n C x hAO.2.1 k hk, hor]
        change ((gateAt C k).inputs.map (wv n C x)).any id = true
        exact List.any_eq_true.mpr
          ⟨wv n C x (n + j), List.mem_map_of_mem hjin, hchild⟩

def wireCone (n : Nat) (C : Circuit) (w : Nat) : Finset Nat :=
  if w < n then ∅ else gateCone n C (w - n)

lemma wireCone_real (n : Nat) (C : Circuit) (w : Nat) (hw : w < n + C.gates.length) :
    wireCone n C w ⊆ Finset.range C.gates.length := by
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · simpa only [wireCone, ite_eq_right hwn] using
      gateCone_real n C (w - n) (by omega)

lemma wireCone_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (w : Nat) (hw : w < n + C.gates.length) :
    ∀ k ∈ wireCone n C w, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ wireCone n C w := by
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · simpa only [wireCone, ite_eq_right hwn] using
      gateCone_closed n C hAO (w - n) (by omega)

lemma wireCone_root (n : Nat) (C : Circuit) (w : Nat) :
    w < n ∨ w - n ∈ wireCone n C w := by
  by_cases hwn : w < n
  · exact Or.inl hwn
  · exact Or.inr (by simpa only [wireCone, ite_eq_right hwn] using gateCone_self n C (w - n))

lemma max_and_forces_wire (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (g w : Nat) (hw : w < n + C.gates.length) (hg : g ∈ wireCone n C w)
    (hmax : ∀ j ∈ wireCone n C w, (gateAt C j).op = GateOp.and → j ≤ g)
    (x : Fin n → Bool) (hx : gateVal n C g x = true) : wv n C x w = true := by
  by_cases hwn : w < n
  · simp [wireCone, hwn] at hg
  · have heq : n + (w - n) = w := by omega
    have ht := max_and_forces_gate n C hAO g (w - n) (by omega)
      (by simpa only [wireCone, ite_eq_right hwn] using hg)
      (by simpa only [wireCone, ite_eq_right hwn] using hmax) x hx
    change wv n C x (n + (w - n)) = true at ht
    exact heq ▸ ht

end PEqualNP.Outside.L_meta_2583.SafeProductTopology

namespace PEqualNP.Outside.L_meta_2583.TPreservingSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma fullSupport_gate (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (k : Nat) (hk : k < C.gates.length) :
    fullSupport n C hAO (n + k) = fullSupport n C hAO (opnd C k 0) ∪
      fullSupport n C hAO (opnd C k 1) := by
  exact pickedSupport_gate _ _ _ _ _ _ _ _ _ hk

lemma selectedSupport_gate (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (left : Nat → Bool) (k : Nat) (hk : k < C.gates.length) :
    selectedSupport n C hAO left (n + k) =
      if andSelector C k then selectedSupport n C hAO left (opnd C k 0) ∪
        selectedSupport n C hAO left (opnd C k 1)
      else if left k then selectedSupport n C hAO left (opnd C k 0)
      else selectedSupport n C hAO left (opnd C k 1) :=
  pickedSupport_gate _ _ _ _ _ _ _ _ _ hk

def preferredLeft (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (p : Fin n) (k : Nat) : Bool :=
  if p ∈ fullSupport n C hAO (opnd C k 0) then true
  else if p ∈ fullSupport n C hAO (opnd C k 1) then false
  else wv n C (setInput T) (opnd C k 0)

lemma preferredSupport_contains (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (p : Fin n) :
    ∀ w, p ∈ fullSupport n C hAO w →
      p ∈ selectedSupport n C hAO (preferredLeft n C hAO T p) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hpw
    by_cases hwn : w < n
    · simpa only [show fullSupport n C hAO w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn,
        show selectedSupport n C hAO (preferredLeft n C hAO T p) w = {⟨w, hwn⟩} from
          pickedSupport_input _ _ _ _ _ _ _ _ _ hwn] using hpw
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [fullSupport_gate n C hAO k hk] at hpw
      rw [selectedSupport_gate n C hAO _ k hk]
      by_cases hb : andSelector C k = true
      · rw [ite_eq_left hb]
        rcases Finset.mem_union.mp hpw with hl | hr
        · exact Finset.mem_union_left _ (ih _ (opnd_back n C hAO k hk 0) hl)
        · exact Finset.mem_union_right _ (ih _ (opnd_back n C hAO k hk 1) hr)
      · rw [ite_eq_right hb]
        by_cases hl : p ∈ fullSupport n C hAO (opnd C k 0)
        · simp only [preferredLeft, ite_eq_left hl, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 0) hl
        · have hr := (Finset.mem_union.mp hpw).resolve_left hl
          simp only [preferredLeft, ite_eq_right hl, ite_eq_left hr, Bool.false_eq_true, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 1) hr
    · have heq : fullSupport n C hAO w = ∅ := by
        unfold fullSupport
        rw [pickedSupport, dite_eq_right hwn, dite_eq_right hwg]
      exact False.elim (Finset.notMem_empty _ (heq ▸ hpw))

end PEqualNP.Outside.L_meta_2583.TPreservingSupport

namespace PEqualNP.Outside.L_meta_2583.TPreservingSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma fullSupport_true_of_active_ands_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hactive : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (p : Fin n) (hp : p ∈ T) :
    ∀ w, (w < n ∨ w - n ∈ R) → p ∈ fullSupport n C hAO w → wv n C (setInput T) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR hpw
    by_cases hwn : w < n
    · have heq : fullSupport n C hAO w = {⟨w, hwn⟩} :=
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn
      have hpw' := Finset.mem_singleton.mp (heq ▸ hpw)
      rw [wv_input n C (setInput T) w hwn]
      exact decide_eq_true (hpw' ▸ hp)
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hwR.resolve_left hwn
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · exact hactive k hkR hop
      · rw [fullSupport_gate n C hAO k hk] at hpw
        rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk]
        rcases Finset.mem_union.mp hpw with hl | hr
        · have ht := ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0) hl
          simp [hop, GateOp.eval, ht]
        · have ht := ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1) hr
          simp [hop, GateOp.eval, ht]
    · have heq : fullSupport n C hAO w = ∅ := by
        unfold fullSupport
        rw [pickedSupport, dite_eq_right hwn, dite_eq_right hwg]
      exact False.elim (Finset.notMem_empty _ (heq ▸ hpw))

lemma preferredSupport_subset_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hactive : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (p : Fin n) (hp : p ∈ T) :
    ∀ w, (w < n ∨ w - n ∈ R) → wv n C (setInput T) w = true →
      selectedSupport n C hAO (preferredLeft n C hAO T p) w ⊆ T := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR hw
    by_cases hwn : w < n
    · rw [show selectedSupport n C hAO (preferredLeft n C hAO T p) w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      rw [wv_input n C (setInput T) w hwn] at hw
      exact Finset.singleton_subset_iff.mpr (of_decide_eq_true hw)
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hwR.resolve_left hwn
      rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk] at hw
      rw [selectedSupport_gate n C hAO _ k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hb : andSelector C k = true := by simp [andSelector, hop]
        rw [ite_eq_left hb]
        have hbits : wv n C (setInput T) (opnd C k 0) = true ∧
            wv n C (setInput T) (opnd C k 1) = true := by simpa [hop, GateOp.eval] using hw
        exact Finset.union_subset (ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0) hbits.1)
          (ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1) hbits.2)
      · have hb : ¬andSelector C k = true := by simp [andSelector, hop]
        rw [ite_eq_right hb]
        by_cases hl : p ∈ fullSupport n C hAO (opnd C k 0)
        · simp only [preferredLeft, ite_eq_left hl, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0)
            (fullSupport_true_of_active_ands_closed n C hAO T R hRclosed hactive p hp _ (hRclosed k hkR 0) hl)
        · by_cases hr : p ∈ fullSupport n C hAO (opnd C k 1)
          · simp only [preferredLeft, ite_eq_right hl, ite_eq_left hr, Bool.false_eq_true, ↓reduceIte]
            exact ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1)
              (fullSupport_true_of_active_ands_closed n C hAO T R hRclosed hactive p hp _ (hRclosed k hkR 1) hr)
          · simp only [preferredLeft, ite_eq_right hl, ite_eq_right hr]
            by_cases hv0 : wv n C (setInput T) (opnd C k 0) = true
            · rw [ite_eq_left hv0]
              exact ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0) hv0
            · rw [ite_eq_right hv0]
              have hv1 : wv n C (setInput T) (opnd C k 1) = true := by
                simpa [hop, GateOp.eval, hv0] using hw
              exact ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1) hv1
    · rw [wv_missing n C (setInput T) w (by omega)] at hw
      cases hw


lemma shared_roots_support_within_T_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hactive : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (W : Finset Nat) (hW : ∀ w ∈ W, w < n ∨ w - n ∈ R)
    (htrue : ∀ w ∈ W, wv n C (setInput T) w = true)
    (p : Fin n) (hp : p ∈ T) (hfull : ∀ w ∈ W, p ∈ fullSupport n C hAO w) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ (∀ w ∈ W, wv n C (setInput S) w = true) ∧
      S.card ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1 := by
  let left := preferredLeft n C hAO T p
  let s := selectedSupport n C hAO left
  let S := W.biUnion s
  have hvalid : ∀ w ∈ W, w < n + C.gates.length := by
    intro w hw
    rcases hW w hw with hi | hi
    · omega
    · have := Finset.mem_range.mp (hRreal hi)
      omega
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    exact preferredSupport_subset_closed n C hAO T R hRclosed hactive p hp w
      (hW w hw) (htrue w hw) hiw
  · intro w hw
    have hs := selectedSupport_sound n C hAO left w (hvalid w hw)
    exact wv_mono n C hAO.1 hAO.2.1 (setInput (s w)) (setInput S)
      (fun i hi => decide_eq_true (Finset.mem_biUnion.mpr ⟨w, hw, of_decide_eq_true hi⟩)) w hs
  · let parents : Nat → Finset Nat := fun k =>
      if andSelector C k then {opnd C k 0, opnd C k 1}
      else if left k then {opnd C k 0} else {opnd C k 1}
    let cost : Nat → Nat := fun k => if andSelector C k then 1 else 0
    have hi : ∀ i < n, (s i).card ≤ 1 := by
      intro i hi
      have heq : s i = {⟨i, hi⟩} := pickedSupport_input _ _ _ _ _ _ _ _ _ hi
      rw [heq]
      simp
    have hb : ∀ k < C.gates.length, parents k ⊆ Finset.range (n + k) := by
      intro k hk j hj
      simp only [parents] at hj
      split_ifs at hj with h1 h2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact Finset.mem_range.mpr (opnd_back n C hAO k hk 0)
        · exact Finset.mem_range.mpr (opnd_back n C hAO k hk 1)
      · rw [Finset.mem_singleton] at hj
        subst j
        exact Finset.mem_range.mpr (opnd_back n C hAO k hk 0)
      · rw [Finset.mem_singleton] at hj
        subst j
        exact Finset.mem_range.mpr (opnd_back n C hAO k hk 1)
    have hc : ∀ k < C.gates.length, (parents k).card ≤ cost k + 1 := by
      intro k _
      simp only [parents, cost]
      split_ifs <;> first | exact Finset.card_le_two | simp
    have hv : ∀ k < C.gates.length, s (n + k) ⊆ (parents k).biUnion s := by
      intro k hk
      change selectedSupport n C hAO left (n + k) ⊆ _
      rw [selectedSupport_gate n C hAO left k hk]
      simp only [parents]
      split_ifs <;> simp [s]
    have hRc : ∀ k ∈ R, k < C.gates.length → ∀ j ∈ parents k, j < n ∨ j - n ∈ R := by
      intro k hk _ j hj
      simp only [parents] at hj
      split_ifs at hj with h1 h2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hRclosed k hk 0
        · exact hRclosed k hk 1
      · rw [Finset.mem_singleton] at hj
        subst j
        exact hRclosed k hk 0
      · rw [Finset.mem_singleton] at hj
        subst j
        exact hRclosed k hk 1
    have hbound := SharedSupport.support_family_bound_anchor_closed n C.gates.length
      s parents cost hi hb hc hv R hRc W (fun w hw => Finset.mem_range.mpr (hvalid w hw))
      hW p (fun w hw => preferredSupport_contains n C hAO T p w (hfull w hw))
    have heq : (Finset.range C.gates.length).filter (fun k => k ∈ R) = R := by
      ext k
      exact ⟨fun hk => (Finset.mem_filter.mp hk).2,
        fun hk => Finset.mem_filter.mpr ⟨hRreal hk, hk⟩⟩
    rw [heq] at hbound
    have hsum : R.sum cost = (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
      simp only [cost, Finset.sum_boole]
      rfl
    simpa only [hsum] using hbound

end PEqualNP.Outside.L_meta_2583.TPreservingSupport

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma closed_tight_all_ands_true (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∀ k ∈ R, (gateAt C k).op = GateOp.and → wv n C (setInput T) (n + k) = true := by
  classical
  have hvalid : w < n + C.gates.length := by
    rcases hwR with hw | hw
    · omega
    · have hr := Finset.mem_range.mp (hRreal hw)
      omega
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ R ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) R
      (fun k hk _ => hRclosed k hk 0) (fun k hk _ => hRclosed k hk 1) w hvalid hwR
  have hsub : B ⊆ R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    obtain ⟨_, hkR, hboth⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkR, ?_⟩
    cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hboth ⊢
  have hBeq : B = R.filter (fun k => AndSignature.isAnd C k = true) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro k hk hop
  have hmem : k ∈ B := by
    rw [hBeq]
    exact Finset.mem_filter.mpr ⟨hk, by simp [AndSignature.isAnd, hop]⟩
  have hboth := (Finset.mem_filter.mp hmem).2.2
  simpa [pickedBoth, hop] using hboth

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma true_wire_has_support_input (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) :
    ∀ w, wv n C (setInput T) w = true →
      ∃ p ∈ T, p ∈ fullSupport n C hAO w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [wv_input n C (setInput T) w hwn] at hw
        exact of_decide_eq_true hw
      · rw [show fullSupport n C hAO w = {⟨w, hwn⟩} from
          pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
        exact Finset.mem_singleton_self _
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk] at hw
      have hchild : wv n C (setInput T) (opnd C k 0) = true ∨
          wv n C (setInput T) (opnd C k 1) = true := by
        rcases hAO.1 _ (gate_mem C k hk) with hop | hop
        · have hb : wv n C (setInput T) (opnd C k 0) = true ∧
              wv n C (setInput T) (opnd C k 1) = true := by
            simpa [hop, GateOp.eval] using hw
          exact Or.inl hb.1
        · simpa [hop, GateOp.eval] using hw
      rw [TPreservingSupport.fullSupport_gate n C hAO k hk]
      rcases hchild with hl | hr
      · obtain ⟨p, hp, hfull⟩ := ih _ (opnd_back n C hAO k hk 0) hl
        exact ⟨p, hp, Finset.mem_union_left _ hfull⟩
      · obtain ⟨p, hp, hfull⟩ := ih _ (opnd_back n C hAO k hk 1) hr
        exact ⟨p, hp, Finset.mem_union_right _ hfull⟩
    · rw [wv_missing n C (setInput T) w (by omega)] at hw
      cases hw

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma closed_tight_and_operands_T_disjoint
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    Disjoint (T ∩ fullSupport n C hAO (opnd C g 0))
      (T ∩ fullSupport n C hAO (opnd C g 1)) := by
  classical
  have hg := Finset.mem_range.mp (hRreal hgR)
  have hactive := closed_tight_all_ands_true n C hAO R hRreal hRclosed T (n + g)
    (Or.inr (by simpa using hgR)) htrue hmin htight
  let P := R ∩ Finset.range g
  have hPreal : P ⊆ Finset.range C.gates.length := fun _ hk =>
    hRreal (Finset.mem_inter.mp hk).1
  have hPclosed : ∀ k ∈ P, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ P := by
    intro k hk b
    obtain ⟨hkR, hkg⟩ := Finset.mem_inter.mp hk
    rcases hRclosed k hkR b with hb | hb
    · exact Or.inl hb
    · right
      refine Finset.mem_inter.mpr ⟨hb, Finset.mem_range.mpr ?_⟩
      have hkb := opnd_back n C hAO k (Finset.mem_range.mp (hRreal hkR)) b
      have hkg := Finset.mem_range.mp hkg
      omega
  have hPactive : ∀ k ∈ P, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true := fun k hk =>
    hactive k (Finset.mem_inter.mp hk).1
  have hbits : wv n C (setInput T) (opnd C g 0) = true ∧
      wv n C (setInput T) (opnd C g 1) = true := by
    simpa [wv_rec n C (setInput T) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval] using htrue
  apply Finset.disjoint_left.mpr
  intro p hp0 hp1
  obtain ⟨hpT, hp0⟩ := Finset.mem_inter.mp hp0
  have hp1 := (Finset.mem_inter.mp hp1).2
  let W : Finset Nat := {opnd C g 0, opnd C g 1}
  have hopP (b : Fin 2) : opnd C g b < n ∨ opnd C g b - n ∈ P := by
    by_cases hbn : opnd C g b < n
    · exact Or.inl hbn
    rcases hRclosed g hgR b with hb | hb
    · exact False.elim (hbn hb)
    · right
      refine Finset.mem_inter.mpr ⟨hb, Finset.mem_range.mpr ?_⟩
      have hback := opnd_back n C hAO g hg b
      omega
  have hW : ∀ w ∈ W, w < n ∨ w - n ∈ P := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hopP 0
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hopP 1
  have hWtrue : ∀ w ∈ W, wv n C (setInput T) w = true := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hbits.1
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hbits.2
  have hWfull : ∀ w ∈ W, p ∈ fullSupport n C hAO w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hp0
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hp1
  obtain ⟨S, hST, hSW, hScard⟩ := TPreservingSupport.shared_roots_support_within_T_closed
    n C hAO T P hPreal hPclosed hPactive W hW hWtrue p hpT hWfull
  have hStrue : wv n C (setInput S) (n + g) = true := by
    have hs0 := hSW (opnd C g 0) (by simp [W])
    have hs1 := hSW (opnd C g 1) (by simp [W])
    simp [wv_rec n C (setInput S) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval, hs0, hs1]
  have hTcard := Finset.card_le_card (hmin S hST hStrue)
  have hsub : insert g (P.filter (fun k => AndSignature.isAnd C k = true)) ⊆
      R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_filter.mpr ⟨hgR, by simp [AndSignature.isAnd, hga]⟩
    · obtain ⟨hkP, hka⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hkP).1, hka⟩
  have hgnot : g ∉ P.filter (fun k => AndSignature.isAnd C k = true) := by
    intro hm
    have hlt := Finset.mem_range.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hm).1).2
    omega
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hgnot] at hcount
  omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma wv_eq_of_agree_fullSupport (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) :
    ∀ w, (∀ p ∈ fullSupport n C hAO w, x p = y p) → wv n C x w = wv n C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hagree
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn, wv_input n C y w hwn]
      apply hagree
      rw [show fullSupport n C hAO w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      exact Finset.mem_singleton_self _
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have h0 : wv n C x (opnd C k 0) = wv n C y (opnd C k 0) := by
        apply ih _ (opnd_back n C hAO k hk 0)
        intro p hp
        apply hagree
        rw [TPreservingSupport.fullSupport_gate n C hAO k hk]
        exact Finset.mem_union_left _ hp
      have h1 : wv n C x (opnd C k 1) = wv n C y (opnd C k 1) := by
        apply ih _ (opnd_back n C hAO k hk 1)
        intro p hp
        apply hagree
        rw [TPreservingSupport.fullSupport_gate n C hAO k hk]
        exact Finset.mem_union_right _ hp
      rw [wv_rec n C x hAO.2.1 k hk, wv_rec n C y hAO.2.1 k hk,
        inputs_two n C hAO k hk]
      simp only [List.map_cons, List.map_nil, h0, h1]
    · rw [wv_missing n C x w (by omega), wv_missing n C y w (by omega)]

lemma wv_inter_fullSupport (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) :
    wv n C (setInput (T ∩ fullSupport n C hAO w)) w = wv n C (setInput T) w := by
  apply wv_eq_of_agree_fullSupport n C hAO
  intro p hp
  simp [setInput, hp]

lemma minimal_support_subset_fullSupport (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S) :
    T ⊆ fullSupport n C hAO w := by
  have hm := hmin (T ∩ fullSupport n C hAO w) Finset.inter_subset_left
    (by rw [wv_inter_fullSupport n C hAO T w]; exact htrue)
  exact fun _ hp => (Finset.mem_inter.mp (hm hp)).2

lemma and_operand_supports_union (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (g : Nat) (hg : g < C.gates.length)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S) :
    (T ∩ fullSupport n C hAO (opnd C g 0)) ∪
      (T ∩ fullSupport n C hAO (opnd C g 1)) = T := by
  have hsub := minimal_support_subset_fullSupport n C hAO T (n + g) htrue hmin
  rw [TPreservingSupport.fullSupport_gate n C hAO g hg] at hsub
  ext p
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hp
    rcases Finset.mem_union.mp (hsub hp) with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩

lemma and_operand_supports_minimal (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (g : Nat) (hg : g < C.gates.length)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (hdis : Disjoint (T ∩ fullSupport n C hAO (opnd C g 0))
      (T ∩ fullSupport n C hAO (opnd C g 1))) :
    ∀ b : Fin 2, let U := T ∩ fullSupport n C hAO (opnd C g b)
      wv n C (setInput U) (opnd C g b) = true ∧
      ∀ S ⊆ U, wv n C (setInput S) (opnd C g b) = true → U ⊆ S := by
  classical
  have hbits : wv n C (setInput T) (opnd C g 0) = true ∧
      wv n C (setInput T) (opnd C g 1) = true := by
    simpa [wv_rec n C (setInput T) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval] using htrue
  have hminimal (b c : Fin 2) (hbc : b ≠ c)
      (hb : wv n C (setInput T) (opnd C g b) = true)
      (hc : wv n C (setInput T) (opnd C g c) = true)
      (hdisbc : Disjoint (T ∩ fullSupport n C hAO (opnd C g b))
        (T ∩ fullSupport n C hAO (opnd C g c))) :
      ∀ S ⊆ T ∩ fullSupport n C hAO (opnd C g b),
        wv n C (setInput S) (opnd C g b) = true →
        T ∩ fullSupport n C hAO (opnd C g b) ⊆ S := by
    intro S hS hSb
    let V := T ∩ fullSupport n C hAO (opnd C g c)
    have hVT : V ⊆ T := Finset.inter_subset_left
    have hST : S ⊆ T := Finset.Subset.trans hS Finset.inter_subset_left
    have hb' : wv n C (setInput (S ∪ V)) (opnd C g b) = true :=
      wv_mono n C hAO.1 hAO.2.1 _ _
        (fun p hp => decide_eq_true (Finset.mem_union_left V (of_decide_eq_true hp))) _ hSb
    have hc' : wv n C (setInput (S ∪ V)) (opnd C g c) = true := by
      apply wv_mono n C hAO.1 hAO.2.1 (setInput V) _
        (fun p hp => decide_eq_true (Finset.mem_union_right S (of_decide_eq_true hp)))
      rw [wv_inter_fullSupport n C hAO T (opnd C g c)]
      exact hc
    have hroot : wv n C (setInput (S ∪ V)) (n + g) = true := by
      fin_cases b <;> fin_cases c <;> simp_all [wv_rec n C (setInput (S ∪ V)) hAO.2.1 g hg,
        inputs_two n C hAO g hg, GateOp.eval]
    have hTU := hmin (S ∪ V) (Finset.union_subset hST hVT) hroot
    intro p hp
    rcases Finset.mem_union.mp (hTU (Finset.mem_inter.mp hp).1) with hs | hv
    · exact hs
    · exact False.elim (Finset.disjoint_left.mp hdisbc hp hv)
  intro b
  dsimp
  fin_cases b
  · exact ⟨by rw [wv_inter_fullSupport]; exact hbits.1,
      hminimal 0 1 (by decide) hbits.1 hbits.2 hdis⟩
  · exact ⟨by rw [wv_inter_fullSupport]; exact hbits.2,
      hminimal 1 0 (by decide) hbits.2 hbits.1 hdis.symm⟩

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma fullSupport_mono_inCone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (i : Nat) : ∀ j, InCone n C i j →
      fullSupport n C hAO (n + i) ⊆ fullSupport n C hAO (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hij
    obtain ⟨hj, k, hkj, hinput, hik⟩ := (TopNormal.inCone_iff n C i j).mp hij
    have hsub : fullSupport n C hAO (n + k) ⊆ fullSupport n C hAO (n + j) := by
      rw [TPreservingSupport.fullSupport_gate n C hAO j hj]
      rw [inputs_two n C hAO j hj] at hinput
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hinput
      rcases hinput with hinput | hinput
      · rw [hinput]
        exact Finset.subset_union_left
      · rw [hinput]
        exact Finset.subset_union_right
    rcases hik with rfl | hik
    · exact hsub
    · exact Finset.Subset.trans (ih k hkj hik) hsub

lemma wireCone_fullSupport_subset (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (w k : Nat) (hk : k ∈ wireCone n C w) :
    fullSupport n C hAO (n + k) ⊆ fullSupport n C hAO w := by
  by_cases hwn : w < n
  · simp [wireCone, hwn] at hk
  · have hw : n + (w - n) = w := by omega
    rw [wireCone, ite_eq_right hwn, mem_gateCone] at hk
    rcases hk with rfl | hk
    · rw [hw]
    · have hsub := fullSupport_mono_inCone n C hAO k (w - n) hk
      rwa [hw] at hsub

lemma wireCone_subset_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : Nat) (hwR : w < n ∨ w - n ∈ R) : wireCone n C w ⊆ R := by
  have hancestor : ∀ j, j ∈ R → ∀ i, InCone n C i j → i ∈ R := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hjR i hij
      obtain ⟨hj, k, hkj, hinput, hik⟩ := (TopNormal.inCone_iff n C i j).mp hij
      have hkR : k ∈ R := by
        rw [inputs_two n C hAO j hj] at hinput
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hinput
        rcases hinput with hinput | hinput
        · have hc := hRclosed j hjR 0
          rw [← hinput] at hc
          simpa using hc
        · have hc := hRclosed j hjR 1
          rw [← hinput] at hc
          simpa using hc
      rcases hik with rfl | hik
      · exact hkR
      · exact ih k hkj hkR i hik
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · have hwR := hwR.resolve_left hwn
    intro k hk
    rw [wireCone, ite_eq_right hwn, mem_gateCone] at hk
    rcases hk with rfl | hk
    · exact hwR
    · exact hancestor (w - n) hwR k hk

lemma closed_tight_and_cones_disjoint
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    Disjoint ((wireCone n C (opnd C g 0)).filter (fun k => AndSignature.isAnd C k = true))
      ((wireCone n C (opnd C g 1)).filter (fun k => AndSignature.isAnd C k = true)) := by
  have hdis := closed_tight_and_operands_T_disjoint n C hAO R hRreal hRclosed
    T g hgR hga htrue hmin htight
  have hactive := closed_tight_all_ands_true n C hAO R hRreal hRclosed T (n + g)
    (Or.inr (by simpa using hgR)) htrue hmin htight
  have hc0 := wireCone_subset_closed n C hAO R hRclosed (opnd C g 0) (hRclosed g hgR 0)
  apply Finset.disjoint_left.mpr
  intro k hk0 hk1
  obtain ⟨hk0, hka⟩ := Finset.mem_filter.mp hk0
  have hk1 := (Finset.mem_filter.mp hk1).1
  have hkop : (gateAt C k).op = GateOp.and := by
    cases hop : (gateAt C k).op <;> simp [AndSignature.isAnd, hop] at hka ⊢
  obtain ⟨p, hpT, hpk⟩ := true_wire_has_support_input n C hAO T (n + k)
    (hactive k (hc0 hk0) hkop)
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_inter.mpr ⟨hpT, wireCone_fullSupport_subset n C hAO _ k hk0 hpk⟩)
    (Finset.mem_inter.mpr ⟨hpT, wireCone_fullSupport_subset n C hAO _ k hk1 hpk⟩)

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma closed_minimal_support_card_le_ands
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S) :
    T.card ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1 := by
  classical
  have hvalid : w < n + C.gates.length := by
    rcases hwR with hw | hw
    · omega
    · have hr := Finset.mem_range.mp (hRreal hw)
      omega
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ R ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) R
      (fun k hk _ => hRclosed k hk 0) (fun k hk _ => hRclosed k hk 1) w hvalid hwR
  have hsub : B ⊆ R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    obtain ⟨_, hkR, hboth⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkR, ?_⟩
    cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hboth ⊢
  have := Finset.card_le_card hsub
  omega

lemma wireCone_below (n : Nat) (C : Circuit) (w r : Nat) (hw : w < n + r) :
    wireCone n C w ⊆ Finset.range r := by
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · intro k hk
    rw [wireCone, ite_eq_right hwn] at hk
    have hk := Finset.mem_range.mp (gateCone_prefix n C (w - n) hk)
    exact Finset.mem_range.mpr (by omega)

lemma closed_tight_and_operand_counts
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∀ b : Fin 2,
      (T ∩ fullSupport n C hAO (opnd C g b)).card =
        ((wireCone n C (opnd C g b)).filter (fun k => AndSignature.isAnd C k = true)).card + 1 ∧
      ((wireCone n C (opnd C g b)).filter (fun k => AndSignature.isAnd C k = true)).card <
        (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  have hg := Finset.mem_range.mp (hRreal hgR)
  let U := fun b : Fin 2 => T ∩ fullSupport n C hAO (opnd C g b)
  let A := fun b : Fin 2 => (wireCone n C (opnd C g b)).filter
    (fun k => AndSignature.isAnd C k = true)
  let B := R.filter (fun k => AndSignature.isAnd C k = true)
  have hdisU : Disjoint (U 0) (U 1) :=
    closed_tight_and_operands_T_disjoint n C hAO R hRreal hRclosed T g hgR hga htrue hmin htight
  have hdisA : Disjoint (A 0) (A 1) :=
    closed_tight_and_cones_disjoint n C hAO R hRreal hRclosed T g hgR hga htrue hmin htight
  have hunion : U 0 ∪ U 1 = T := and_operand_supports_union n C hAO T g hg htrue hmin
  have hUcard : (U 0).card + (U 1).card = T.card := by
    rw [← Finset.card_union_of_disjoint hdisU, hunion]
  have hminimal := and_operand_supports_minimal n C hAO T g hg hga htrue hmin hdisU
  have hbound (b : Fin 2) : (U b).card ≤ (A b).card + 1 := by
    have hw := opnd_back n C hAO g hg b
    have hwreal : opnd C g b < n + C.gates.length := by omega
    exact closed_minimal_support_card_le_ands n C hAO (wireCone n C (opnd C g b))
      (wireCone_real n C _ hwreal) (wireCone_closed n C hAO _ hwreal) (U b) _
      (wireCone_root n C _) (hminimal b).1 (hminimal b).2
  have hAsub (b : Fin 2) : A b ⊆ B := by
    intro k hk
    obtain ⟨hk, hka⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr
      ⟨wireCone_subset_closed n C hAO R hRclosed _ (hRclosed g hgR b) hk, hka⟩
  have hgnot (b : Fin 2) : g ∉ A b := by
    intro hk
    have hlt := Finset.mem_range.mp
      (wireCone_below n C _ g (opnd_back n C hAO g hg b) (Finset.mem_filter.mp hk).1)
    omega
  have hsub : insert g (A 0 ∪ A 1) ⊆ B := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_filter.mpr ⟨hgR, by simp [AndSignature.isAnd, hga]⟩
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact hAsub 0 hk
      · exact hAsub 1 hk
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_union]; exact not_or.mpr ⟨hgnot 0, hgnot 1⟩),
    Finset.card_union_of_disjoint hdisA] at hcard
  have h0 := hbound 0
  have h1 := hbound 1
  change T.card = B.card + 1 at htight
  intro b
  change (U b).card = (A b).card + 1 ∧ (A b).card < B.card
  fin_cases b
  · change (U 0).card = (A 0).card + 1 ∧ (A 0).card < B.card
    constructor <;> omega
  · change (U 1).card = (A 1).card + 1 ∧ (A 1).card < B.card
    constructor <;> omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma gateCone_subset_of_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R) :
    ∀ k, k < C.gates.length → k ∈ R → gateCone n C k ⊆ R := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hkR i hi
    rcases (mem_gateCone n C k i).mp hi with rfl | hanc
    · exact hkR
    · obtain ⟨_, j, hjk, hjin, hij⟩ := (TopNormal.inCone_iff n C i k).mp hanc
      have hjR : j ∈ R := by
        rw [inputs_two n C hAO k hk] at hjin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hjin
        rcases hjin with hjin | hjin
        · have h := hRclosed k hkR 0
          rw [← hjin] at h
          simpa only [Nat.add_sub_cancel_left, show ¬n + j < n by omega, false_or] using h
        · have h := hRclosed k hkR 1
          rw [← hjin] at h
          simpa only [Nat.add_sub_cancel_left, show ¬n + j < n by omega, false_or] using h
      exact ih j hjk (lt_trans hjk hk) hjR ((mem_gateCone n C j i).mpr hij)

lemma closed_tight_all_ands_in_subcone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) w = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (S : Finset Nat) (hSR : S ⊆ R)
    (hSclosed : ∀ k ∈ S, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ S)
    (hwS : w < n ∨ w - n ∈ S) :
    R.filter (fun k => AndSignature.isAnd C k = true) ⊆ S := by
  classical
  have hvalid : w < n + C.gates.length := by
    rcases hwR with hw | hw
    · omega
    · have := Finset.mem_range.mp (hRreal hw)
      omega
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ S ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) S
      (fun k hk _ => hSclosed k hk 0) (fun k hk _ => hSclosed k hk 1) w hvalid hwS
  have hsub : B ⊆ R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    obtain ⟨_, hkS, hboth⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hSR hkS, ?_⟩
    cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hboth ⊢
  have hBeq : B = R.filter (fun k => AndSignature.isAnd C k = true) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro k hk
  rw [← hBeq] at hk
  exact (Finset.mem_filter.mp hk).2.1

lemma closed_tight_all_ands_in_gateCone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) (n + g) = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    R.filter (fun k => AndSignature.isAnd C k = true) ⊆ gateCone n C g := by
  have hg := Finset.mem_range.mp (hRreal hgR)
  exact closed_tight_all_ands_in_subcone n C hAO R hRreal T (n + g)
    (Or.inr (by simpa using hgR)) htrue hmin htight (gateCone n C g)
    (gateCone_subset_of_closed n C hAO R hRclosed g hg hgR)
    (gateCone_closed n C hAO g hg)
    (Or.inr (by simpa using gateCone_self n C g))

lemma closed_tight_implying_and_last (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) w = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (j : Nat) (hjR : j ∈ R) (hja : (gateAt C j).op = GateOp.and)
    (himplies : ∀ U ⊆ T, wv n C (setInput U) (n + j) = true → wv n C (setInput U) w = true) :
    ∀ k ∈ R, (gateAt C k).op = GateOp.and → k ≤ j := by
  have hjtrue := closed_tight_all_ands_true n C hAO R hRreal hRclosed T w hwR
    htrue hmin htight j hjR hja
  have hjmin : ∀ U ⊆ T, wv n C (setInput U) (n + j) = true → T ⊆ U := by
    intro U hU hUj
    exact hmin U hU (himplies U hU hUj)
  have hcone := closed_tight_all_ands_in_gateCone n C hAO R hRreal hRclosed T j hjR
    hjtrue hjmin htight
  intro k hk hka
  have hmem : k ∈ R.filter (fun k => AndSignature.isAnd C k = true) :=
    Finset.mem_filter.mpr ⟨hk, by simp [AndSignature.isAnd, hka]⟩
  have hkle := Finset.mem_range.mp (gateCone_prefix n C j (hcone hmem))
  omega

lemma closed_tight_implying_and_unique (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) w = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (i j : Nat) (hiR : i ∈ R) (hjR : j ∈ R)
    (hia : (gateAt C i).op = GateOp.and) (hja : (gateAt C j).op = GateOp.and)
    (himplies : ∀ U ⊆ T, wv n C (setInput U) (n + i) = true → wv n C (setInput U) w = true)
    (hjimplies : ∀ U ⊆ T, wv n C (setInput U) (n + j) = true → wv n C (setInput U) w = true) : i = j := by
  have hji := closed_tight_implying_and_last n C hAO R hRreal hRclosed T w hwR
    htrue hmin htight i hiR hia himplies j hjR hja
  have hij := closed_tight_implying_and_last n C hAO R hRreal hRclosed T w hwR
    htrue hmin htight j hjR hja hjimplies i hiR hia
  omega

lemma exists_or_frontier_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R) :
    ∀ w, (w < n ∨ w - n ∈ R) → ∃ I : Finset (Fin n), ∃ A : Finset Nat,
      (∀ k ∈ A, k ∈ R ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.and) ∧
      ∀ x, wv n C x w = true ↔ (∃ i ∈ I, x i = true) ∨
        (∃ k ∈ A, wv n C x (n + k) = true) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR
    by_cases hwn : w < n
    · refine ⟨{⟨w, hwn⟩}, ∅, by simp, ?_⟩
      intro x
      rw [wv_input n C x w hwn]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hwR.resolve_left hwn
      have hk := Finset.mem_range.mp (hRreal hkR)
      rcases hAO.1 _ (gate_mem C k hk) with hand | hor
      · refine ⟨∅, {k}, ?_, ?_⟩
        · intro j hj
          have heq : j = k := Finset.mem_singleton.mp hj
          simpa only [heq] using ⟨hkR, hk, hand⟩
        · intro x
          simp
      · obtain ⟨I₀, A₀, hA₀, h₀⟩ := ih (opnd C k 0) (opnd_back n C hAO k hk 0) (hRclosed k hkR 0)
        obtain ⟨I₁, A₁, hA₁, h₁⟩ := ih (opnd C k 1) (opnd_back n C hAO k hk 1) (hRclosed k hkR 1)
        refine ⟨I₀ ∪ I₁, A₀ ∪ A₁, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · exact hA₀ j hj
          · exact hA₁ j hj
        · intro x
          rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp only [hor, GateOp.eval, Finset.mem_union]
          aesop

lemma closed_tight_or_frontier_last_and
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (hpos : 0 < (R.filter (fun k => AndSignature.isAnd C k = true)).card) :
    ∃ g : Nat, ∃ I : Finset (Fin n),
      g ∈ R ∧ g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      (∀ i ∈ I, i ∉ T) ∧
      wv n C (setInput T) (n + g) = true ∧
      (∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S) ∧
      R.filter (fun k => AndSignature.isAnd C k = true) ⊆ AncestorJunk.gateCone n C g ∧
      ∀ x, wv n C x w = true ↔ wv n C x (n + g) = true ∨ ∃ i ∈ I, x i = true := by
  classical
  obtain ⟨I, A, hA, hfront⟩ := exists_or_frontier_closed n C hAO R hRreal hRclosed w hwR
  have houtside : ∀ i ∈ I, i ∉ T := by
    intro i hi hiT
    have hroot : wv n C (setInput {i}) w = true :=
      (hfront _).mpr (Or.inl ⟨i, hi, by simp [setInput]⟩)
    have hsub := hmin {i} (Finset.singleton_subset_iff.mpr hiT) hroot
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hex : ∃ g ∈ A, wv n C (setInput T) (n + g) = true := by
    rcases (hfront _).mp htrue with ⟨i, hi, hit⟩ | ha
    · exact False.elim (houtside i hi (of_decide_eq_true hit))
    · exact ha
  obtain ⟨g, hgA, hgtrue⟩ := hex
  have hg := hA g hgA
  have himplies (k : Nat) (hk : k ∈ A) :
      ∀ S ⊆ T, wv n C (setInput S) (n + k) = true → wv n C (setInput S) w = true := by
    intro S _ ht
    exact (hfront _).mpr (Or.inr ⟨k, hk, ht⟩)
  have hsingleton : ∀ k ∈ A, k = g := by
    intro k hk
    exact closed_tight_implying_and_unique n C hAO R hRreal hRclosed T w hwR htrue hmin htight k g
      (hA k hk).1 hg.1 (hA k hk).2.2 hg.2.2 (himplies k hk) (himplies g hgA)
  have hgmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S := by
    intro S hS ht
    exact hmin S hS (himplies g hgA S hS ht)
  refine ⟨g, I, hg.1, hg.2.1, hg.2.2, houtside, hgtrue, hgmin,
    closed_tight_all_ands_in_gateCone n C hAO R hRreal hRclosed T g hg.1 hgtrue hgmin htight, ?_⟩
  intro x
  constructor
  · intro hx
    rcases (hfront x).mp hx with hi | ⟨k, hk, hkt⟩
    · exact Or.inr hi
    · exact Or.inl ((hsingleton k hk) ▸ hkt)
  · intro hx
    rcases hx with hgx | hi
    · exact (hfront x).mpr (Or.inr ⟨g, hgA, hgx⟩)
    · exact (hfront x).mpr (Or.inl hi)

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightCNF

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

def Holds {n : Nat} (clauses : Finset (Finset (Fin n))) (x : Fin n → Bool) : Prop :=
  ∀ clause ∈ clauses, ∃ v ∈ clause, x v = true

lemma holds_singleton {n : Nat} (I : Finset (Fin n)) (x : Fin n → Bool) :
    Holds {I} x ↔ ∃ v ∈ I, x v = true := by
  simp [Holds]

lemma holds_union {n : Nat} (A B : Finset (Finset (Fin n))) (x : Fin n → Bool) :
    Holds (A ∪ B) x ↔ Holds A x ∧ Holds B x := by
  simp only [Holds, Finset.mem_union]
  aesop

lemma holds_add_outside {n : Nat} (clauses : Finset (Finset (Fin n)))
    (I : Finset (Fin n)) (x : Fin n → Bool) :
    Holds (clauses.image (fun clause => clause ∪ I)) x ↔
      Holds clauses x ∨ ∃ v ∈ I, x v = true := by
  classical
  constructor
  · intro h
    by_cases hi : ∃ v ∈ I, x v = true
    · exact Or.inr hi
    · left
      intro clause hc
      obtain ⟨v, hv, hx⟩ := h (clause ∪ I) (Finset.mem_image.mpr ⟨clause, hc, rfl⟩)
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ⟨v, hv, hx⟩
      · exact False.elim (hi ⟨v, hv, hx⟩)
  · intro h clause hc
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    rcases h with h | ⟨v, hv, hx⟩
    · obtain ⟨v, hv, hx⟩ := h old hold
      exact ⟨v, Finset.mem_union_left I hv, hx⟩
    · exact ⟨v, Finset.mem_union_right old hv, hx⟩

lemma cnf_and_or_compose {n : Nat} (f g h : (Fin n → Bool) → Bool)
    (A B : Finset (Finset (Fin n))) (I : Finset (Fin n))
    (hf : ∀ x, f x = true ↔ Holds A x)
    (hg : ∀ x, g x = true ↔ Holds B x)
    (hh : ∀ x, h x = true ↔ (f x = true ∧ g x = true) ∨ ∃ v ∈ I, x v = true) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card ≤ A.card + B.card ∧
      ∀ x, h x = true ↔ Holds clauses x := by
  classical
  refine ⟨(A ∪ B).image (fun clause => clause ∪ I), ?_, ?_⟩
  · exact (Finset.card_image_le).trans (Finset.card_union_le A B)
  · intro x
    rw [holds_add_outside, holds_union, ← hf x, ← hg x]
    exact hh x

end PEqualNP.Outside.L_meta_2583.TightCNF

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma closed_tight_has_short_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card ≤ T.card ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  classical
  generalize ha : (R.filter (fun k => AndSignature.isAnd C k = true)).card = a at htight
  induction a using Nat.strong_induction_on generalizing R T w with
  | ind a ih =>
    by_cases hz : a = 0
    · obtain ⟨I, A, hA, hfront⟩ := exists_or_frontier_closed n C hAO R hRreal hRclosed w hwR
      have hAempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hkA := hA k hk
        have hm : k ∈ R.filter (fun k => AndSignature.isAnd C k = true) :=
          Finset.mem_filter.mpr ⟨hkA.1, by simp [AndSignature.isAnd, hkA.2.2]⟩
        have hempty : R.filter (fun k => AndSignature.isAnd C k = true) = ∅ :=
          Finset.card_eq_zero.mp (by omega)
        rw [hempty] at hm
        exact Finset.notMem_empty _ hm
      refine ⟨{I}, ?_, ?_⟩
      · simp only [Finset.card_singleton]
        omega
      · intro x
        rw [TightCNF.holds_singleton]
        simpa [hAempty] using hfront x
    · have hpos : 0 < (R.filter (fun k => AndSignature.isAnd C k = true)).card := by omega
      obtain ⟨g, I, hgR, hg, hga, _houtside, hgtrue, hgmin, _hcone, hsem⟩ :=
        closed_tight_or_frontier_last_and n C hAO R hRreal hRclosed T w hwR htrue hmin
          (by omega) hpos
      have hdis := closed_tight_and_operands_T_disjoint n C hAO R hRreal hRclosed
        T g hgR hga hgtrue hgmin (by omega)
      have hminimal := and_operand_supports_minimal n C hAO T g hg hga hgtrue hgmin hdis
      have hcounts := closed_tight_and_operand_counts n C hAO R hRreal hRclosed
        T g hgR hga hgtrue hgmin (by omega)
      have hrec (b : Fin 2) :
          ∃ clauses : Finset (Finset (Fin n)),
            clauses.card ≤ (T ∩ fullSupport n C hAO (opnd C g b)).card ∧
              ∀ x, wv n C x (opnd C g b) = true ↔ TightCNF.Holds clauses x := by
        have hback := opnd_back n C hAO g hg b
        have hvalid : opnd C g b < n + C.gates.length := by omega
        exact ih ((wireCone n C (opnd C g b)).filter
          (fun k => AndSignature.isAnd C k = true)).card
          (by have := (hcounts b).2; omega)
          (wireCone n C (opnd C g b)) (wireCone_real n C _ hvalid)
          (wireCone_closed n C hAO _ hvalid) (T ∩ fullSupport n C hAO (opnd C g b))
          (opnd C g b) (wireCone_root n C _) (hminimal b).1 (hminimal b).2 rfl (hcounts b).1
      obtain ⟨A, hAcard, hAsem⟩ := hrec 0
      obtain ⟨B, hBcard, hBsem⟩ := hrec 1
      have hroot : ∀ x, wv n C x w = true ↔
          (wv n C x (opnd C g 0) = true ∧ wv n C x (opnd C g 1) = true) ∨
            ∃ i ∈ I, x i = true := by
        intro x
        rw [hsem x, wv_rec n C x hAO.2.1 g hg, inputs_two n C hAO g hg]
        simp [hga, GateOp.eval]
      obtain ⟨clauses, hcard, hclauses⟩ := TightCNF.cnf_and_or_compose
        (fun x => wv n C x (opnd C g 0)) (fun x => wv n C x (opnd C g 1))
        (fun x => wv n C x w) A B I hAsem hBsem hroot
      refine ⟨clauses, ?_, hclauses⟩
      have hunion := and_operand_supports_union n C hAO T g hg hgtrue hgmin
      have hsum : (T ∩ fullSupport n C hAO (opnd C g 0)).card +
          (T ∩ fullSupport n C hAO (opnd C g 1)).card = T.card := by
        rw [← Finset.card_union_of_disjoint hdis, hunion]
      omega

lemma tight_has_short_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card ≤ T.card ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  have hvalid : w < n + C.gates.length := by
    by_contra hn
    rw [wv_missing n C (setInput T) w (by omega)] at htrue
    cases htrue
  exact closed_tight_has_short_cnf n C hAO (Finset.range C.gates.length)
    (fun _ h => h)
    (fun k hk b => by
      have hb := opnd_back n C hAO k (Finset.mem_range.mp hk) b
      by_cases hbn : opnd C k b < n
      · exact Or.inl hbn
      · exact Or.inr (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)))
    T w (by
      by_cases hwn : w < n
      · exact Or.inl hwn
      · exact Or.inr (Finset.mem_range.mpr (by omega))) htrue hmin htight

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightCNF

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma minimal_support_clause_witness {n : Nat}
    (clauses : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (htrue : Holds clauses (setInput T))
    (hmin : ∀ S ⊆ T, Holds clauses (setInput S) → T ⊆ S)
    (t : Fin n) (ht : t ∈ T) :
    ∃ clause ∈ clauses, clause ∩ T = {t} := by
  classical
  have hnot : ¬ Holds clauses (setInput (T.erase t)) := by
    intro h
    exact Finset.notMem_erase t T (hmin (T.erase t) (Finset.erase_subset t T) h ht)
  unfold Holds at hnot
  push Not at hnot
  obtain ⟨clause, hc, hno⟩ := hnot
  obtain ⟨v, hv, hvT⟩ := htrue clause hc
  have hvT : v ∈ T := of_decide_eq_true hvT
  have hvt : v = t := by
    by_contra hvn
    exact hno v hv (decide_eq_true (Finset.mem_erase.mpr ⟨hvn, hvT⟩))
  subst v
  refine ⟨clause, hc, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpT⟩ := Finset.mem_inter.mp hp
    apply Finset.mem_singleton.mpr
    by_contra hpn
    exact hno p hpc (decide_eq_true (Finset.mem_erase.mpr ⟨hpn, hpT⟩))
  · intro hp
    have hpt := Finset.mem_singleton.mp hp
    subst p
    exact Finset.mem_inter.mpr ⟨hv, ht⟩

lemma minimal_support_short_clauses_exact {n : Nat}
    (clauses : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (htrue : Holds clauses (setInput T))
    (hmin : ∀ S ⊆ T, Holds clauses (setInput S) → T ⊆ S)
    (hcard : clauses.card ≤ T.card) :
    clauses.card = T.card ∧ ∀ clause ∈ clauses, ∃ t ∈ T, clause ∩ T = {t} := by
  classical
  choose f hf using fun t : {t // t ∈ T} =>
    minimal_support_clause_witness clauses T htrue hmin t.val t.property
  have hfinj : Function.Injective f := by
    intro s t hst
    have heq : ({s.val} : Finset (Fin n)) = {t.val} := by
      rw [← (hf s).2, ← (hf t).2, hst]
    apply Subtype.ext
    exact Finset.singleton_injective heq
  let chosen : Finset (Finset (Fin n)) := T.attach.image f
  have hchosen : chosen.card = T.card := by
    rw [Finset.card_image_of_injective _ hfinj]
    exact Finset.card_attach
  have hsub : chosen ⊆ clauses := by
    intro clause hc
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
    exact (hf t).1
  have heq : chosen = clauses := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨by rw [← heq, hchosen], ?_⟩
  intro clause hc
  rw [← heq] at hc
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨t.val, t.property, (hf t).2⟩

end PEqualNP.Outside.L_meta_2583.TightCNF

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma closed_tight_has_exact_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card = T.card ∧
      (∀ clause ∈ clauses, ∃ t ∈ T, clause ∩ T = {t}) ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  obtain ⟨clauses, hcard, hsem⟩ := closed_tight_has_short_cnf n C hAO
    R hRreal hRclosed T w hwR htrue hmin htight
  have hclauses := TightCNF.minimal_support_short_clauses_exact clauses T
    ((hsem _).mp htrue) (fun S hS h => hmin S hS ((hsem _).mpr h)) hcard
  exact ⟨clauses, hclauses.1, hclauses.2, hsem⟩

lemma tight_has_exact_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card = T.card ∧
      (∀ clause ∈ clauses, ∃ t ∈ T, clause ∩ T = {t}) ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  obtain ⟨clauses, hcard, hsem⟩ := tight_has_short_cnf n C hAO T w htrue hmin htight
  have hclauses := TightCNF.minimal_support_short_clauses_exact clauses T
    ((hsem _).mp htrue) (fun S hS h => hmin S hS ((hsem _).mpr h)) hcard
  exact ⟨clauses, hclauses.1, hclauses.2, hsem⟩

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma active_ands_false_wire_has_no_and (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool)
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C x (n + k) = true)
    (v : Nat) (hv : v < n + C.gates.length) (hfalse : wv n C x v = false) :
    ∀ k ∈ wireCone n C v, AndSignature.isAnd C k = false := by
  classical
  intro k hk
  apply Bool.eq_false_iff.mpr
  intro hkA
  let A := (wireCone n C v).filter (fun j => AndSignature.isAnd C j = true)
  have hA : A.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hkA⟩⟩
  let g := A.max' hA
  have hgA : g ∈ A := Finset.max'_mem A hA
  obtain ⟨hgR, hgAnd⟩ := Finset.mem_filter.mp hgA
  have hreal := Finset.mem_range.mp (wireCone_real n C v hv hgR)
  have hop : (gateAt C g).op = GateOp.and := by
    cases hop : (gateAt C g).op <;> simp [AndSignature.isAnd, hop] at hgAnd ⊢
  have ht := max_and_forces_wire n C hAO g v hv hgR
    (fun j hj hjop => by
      apply Finset.le_max' A j
      exact Finset.mem_filter.mpr ⟨hj, by simp [AndSignature.isAnd, hjop]⟩)
    x (hactive g hreal hop)
  rw [hfalse] at ht
  contradiction

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma tight_false_support_safe_product_has_or_endpoint
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (F : (Fin n → Bool) → Bool) (hfalse : F (setInput T) = false)
    (u v : Nat) (hu : u < n + C.gates.length) (hv : v < n + C.gates.length)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → F x = true) :
    ((∀ k ∈ wireCone n C u, AndSignature.isAnd C k = false) ∧
      ∃ S : Finset (Fin n), (∀ i ∈ S, i ∉ T) ∧
        ∀ x, wv n C x u = true ↔ ∃ i ∈ S, x i = true) ∨
    ((∀ k ∈ wireCone n C v, AndSignature.isAnd C k = false) ∧
      ∃ S : Finset (Fin n), (∀ i ∈ S, i ∉ T) ∧
        ∀ x, wv n C x v = true ↔ ∃ i ∈ S, x i = true) := by
  have hactive := tight_all_ands_true n C hAO T w htrue hmin htight
  have hendpoint (a : Nat) (ha : a < n + C.gates.length)
      (haf : wv n C (setInput T) a = false) :
      (∀ k ∈ wireCone n C a, AndSignature.isAnd C k = false) ∧
        ∃ S : Finset (Fin n), (∀ i ∈ S, i ∉ T) ∧
          ∀ x, wv n C x a = true ↔ ∃ i ∈ S, x i = true :=
    ⟨active_ands_false_wire_has_no_and n C hAO (setInput T) hactive a ha haf,
      true_ands_false_wire_is_outside_or n C hAO T hactive a haf⟩
  by_cases hut : wv n C (setInput T) u = true
  · right
    apply hendpoint v hv
    apply Bool.eq_false_iff.mpr
    intro hvt
    have hFt := hsafe (setInput T) hut hvt
    rw [hfalse] at hFt
    contradiction
  · exact Or.inl (hendpoint u hu (Bool.eq_false_iff.mpr hut))

end PEqualNP.Outside.L_meta_2583.TightMinterm
