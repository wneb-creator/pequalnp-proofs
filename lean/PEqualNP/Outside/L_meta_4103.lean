import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4103_aux

-- The structural argument in this namespace is reused from the project proof L_meta_2613.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def E (u t : Fin 13) : Prop :=
  u - t = (0 : Fin 13) ∨ u - t = (1 : Fin 13) ∨ u - t = (3 : Fin 13) ∨ u - t = (9 : Fin 13)

def adj (a b : Fin 26) : Bool :=
  if h1 : a.val < 13 then
    if h2 : 13 ≤ b.val then
      let u : Fin 13 := ⟨a.val, h1⟩
      let t : Fin 13 := ⟨b.val - 13, by omega⟩
      let d := u - t
      decide (d = (0 : Fin 13) ∨ d = (1 : Fin 13) ∨ d = (3 : Fin 13) ∨ d = (9 : Fin 13))
    else false
  else
    if h2 : b.val < 13 then
      let u : Fin 13 := ⟨b.val, h2⟩
      let t : Fin 13 := ⟨a.val - 13, by omega⟩
      let d := u - t
      decide (d = (0 : Fin 13) ∨ d = (1 : Fin 13) ∨ d = (3 : Fin 13) ∨ d = (9 : Fin 13))
    else false

def nbrs (u : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter fun v => adj u v = true

lemma adj_symm : ∀ a b : Fin 26, adj a b = adj b a := by decide
lemma adj_irrefl : ∀ a : Fin 26, adj a a = false := by decide
lemma nbrs_card : ∀ u : Fin 26, (nbrs u).card = 4 := by decide
lemma no_four_cycle : ∀ u v : Fin 26, u ≠ v → (nbrs u ∩ nbrs v).card ≤ 1 := by decide
lemma same_side_common : ∀ u v : Fin 26, u ≠ v → (u.val < 13 ↔ v.val < 13) →
    (nbrs u ∩ nbrs v).card = 1 := by decide
lemma adj_diff_side : ∀ u v : Fin 26, adj u v = true → (u.val < 13 ↔ 13 ≤ v.val) := by decide
lemma pts_card : (Finset.univ.filter fun u : Fin 26 => u.val < 13).card = 13 := by decide
lemma lines_card : (Finset.univ.filter fun u : Fin 26 => 13 ≤ u.val).card = 13 := by decide

def edgePairs : Finset (Fin 26 × Fin 26) :=
  Finset.univ.filter fun p => p.1.val < 13 ∧ adj p.1 p.2 = true

lemma edgePairs_card : edgePairs.card = 52 := by decide +kernel

def hit (x : Fin 26 → Bool) : Prop :=
  ∃ u t : Fin 13, E u t ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true

def single (a : Fin 26) : Fin 26 → Bool := fun i => decide (i = a)
def pair (a b : Fin 26) : Fin 26 → Bool := fun i => decide (i = a ∨ i = b)

lemma hit_single (a : Fin 26) : ¬ hit (single a) := by
  rintro ⟨u, t, _, hu, ht⟩
  have h1 : Fin.castAdd 13 u = a := of_decide_eq_true hu
  have h2 : Fin.natAdd 13 t = a := of_decide_eq_true ht
  have h3 : (Fin.castAdd 13 u).val = (Fin.natAdd 13 t).val := by rw [h1, h2]
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h3
  omega

lemma hit_pair (a b : Fin 26) : hit (pair a b) ↔ adj a b = true := by
  constructor
  · rintro ⟨u, t, hut, hu, ht⟩
    have h1 := of_decide_eq_true hu
    have h2 := of_decide_eq_true ht
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have h3 : (Fin.castAdd 13 u).val = (Fin.natAdd 13 t).val := by rw [h1, h2]
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h3; omega
    · rw [← h1, ← h2]
      unfold adj
      simp only [Fin.val_castAdd, Fin.val_natAdd, u.isLt, dite_true, Nat.le_add_right,
        Nat.add_sub_cancel_left]
      exact decide_eq_true hut
    · rw [← h1, ← h2]
      unfold adj
      have hnot : ¬ (13 + t.val < 13) := by omega
      simp only [Fin.val_castAdd, Fin.val_natAdd, hnot, dite_false, u.isLt, dite_true,
        Nat.add_sub_cancel_left]
      exact decide_eq_true hut
    · have h3 : (Fin.castAdd 13 u).val = (Fin.natAdd 13 t).val := by rw [h1, h2]
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h3; omega
  · intro hab
    unfold adj at hab
    by_cases h1 : a.val < 13
    · simp only [h1, dite_true] at hab
      by_cases h2 : 13 ≤ b.val
      · simp only [h2, dite_true] at hab
        have hd := of_decide_eq_true hab
        refine ⟨⟨a.val, h1⟩, ⟨b.val - 13, by omega⟩, hd, ?_, ?_⟩
        · exact decide_eq_true (Or.inl (Fin.ext rfl))
        · exact decide_eq_true (Or.inr (Fin.ext (by simp; omega)))
      · simp only [h2, dite_false] at hab; contradiction
    · simp only [h1, dite_false] at hab
      by_cases h2 : b.val < 13
      · simp only [h2, dite_true] at hab
        have hd := of_decide_eq_true hab
        refine ⟨⟨b.val, h2⟩, ⟨a.val - 13, by omega⟩, hd, ?_, ?_⟩
        · exact decide_eq_true (Or.inr (Fin.ext rfl))
        · exact decide_eq_true (Or.inl (Fin.ext (by simp; omega)))
      · simp only [h2, dite_false] at hab; contradiction

lemma no_mixed_indep_13 (U : Finset (Fin 26)) (hcard : U.card = 13)
    (hind : ∀ u ∈ U, ∀ v ∈ U, adj u v = false) :
    (∀ u ∈ U, u.val < 13) ∨ (∀ u ∈ U, 13 ≤ u.val) := by
  let S := U.filter fun u => u.val < 13
  let T := U.filter fun u => 13 ≤ u.val
  have hST : S.card + T.card = 13 := by
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      have h1 := (Finset.mem_filter.mp hu1).2
      have h2 := (Finset.mem_filter.mp hu2).2
      omega
    have hunion : S ∪ T = U := by
      ext u
      simp only [S, T, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
      · intro hu; by_cases h : u.val < 13
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard]
  have hS_sub : S ⊆ Finset.univ.filter fun u : Fin 26 => u.val < 13 := fun u hu =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  have hT_sub : T ⊆ Finset.univ.filter fun u : Fin 26 => 13 ≤ u.val := fun u hu =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  have hbound : ∀ (A B : Finset (Fin 26)) (P : Fin 26 → Prop) [DecidablePred P],
      (∀ u ∈ A, P u) → (∀ v ∈ B, ¬ P v) →
      (∀ u ∈ A, ∀ v ∈ nbrs u, ¬ P v) →
      (Finset.univ.filter fun v : Fin 26 => ¬ P v).card = 13 →
      (∀ u ∈ A, ∀ v ∈ B, adj u v = false) →
      (1 ≤ A.card → B.card ≤ 9) ∧
      (2 ≤ A.card → B.card ≤ 6) ∧
      (3 ≤ A.card → B.card ≤ 4) := by
    intro A B P _ hAP hBP hN h13 hno
    have hdisj_nbr (u : Fin 26) (hu : u ∈ A) : Disjoint (nbrs u) B := by
      rw [Finset.disjoint_left]
      intro v hv hvb
      have ha : adj u v = true := (Finset.mem_filter.mp hv).2
      have hf := hno u hu v hvb
      rw [ha] at hf; contradiction
    have hsub_all (X : Finset (Fin 26)) (hX : ∀ v ∈ X, ¬ P v) :
        X.card + B.card ≤ 13 → Disjoint X B → X.card + B.card ≤ 13 := fun h _ => h
    have hcompl (X : Finset (Fin 26)) (hX : ∀ v ∈ X, ¬ P v) (hd : Disjoint X B) :
        X.card + B.card ≤ 13 := by
      rw [← Finset.card_union_of_disjoint hd, ← h13]
      apply Finset.card_le_card
      intro v hv
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hX v hv
      · exact hBP v hv
    refine ⟨?_, ?_, ?_⟩
    · intro h1
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      have hc := hcompl (nbrs u) (hN u hu) (hdisj_nbr u hu)
      rw [nbrs_card u] at hc; omega
    · intro h2
      obtain ⟨u1, hu1, u2, hu2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      have hc := hcompl (nbrs u1 ∪ nbrs u2)
        (fun v hv => (Finset.mem_union.mp hv).elim (hN u1 hu1 v) (hN u2 hu2 v))
        (Finset.disjoint_union_left.mpr ⟨hdisj_nbr u1 hu1, hdisj_nbr u2 hu2⟩)
      have hu12 : (nbrs u1 ∪ nbrs u2).card + (nbrs u1 ∩ nbrs u2).card =
          (nbrs u1).card + (nbrs u2).card := Finset.card_union_add_card_inter _ _
      have hint := no_four_cycle u1 u2 hne
      rw [nbrs_card u1, nbrs_card u2] at hu12
      omega
    · intro h3
      obtain ⟨u1, hu1, u2, hu2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      have hrem : 0 < (A.erase u1 |>.erase u2).card := by
        have h1 : (A.erase u1).card = A.card - 1 := Finset.card_erase_of_mem hu1
        have h2 : u2 ∈ A.erase u1 := Finset.mem_erase.mpr ⟨h12.symm, hu2⟩
        have h3' : ((A.erase u1).erase u2).card = (A.erase u1).card - 1 := Finset.card_erase_of_mem h2
        omega
      obtain ⟨u3, hu3'⟩ := Finset.card_pos.mp hrem
      have h32 : u3 ≠ u2 := (Finset.mem_erase.mp hu3').1
      have h31 : u3 ≠ u1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hu3').2).1
      have hu3 : u3 ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hu3').2).2
      let X := (nbrs u1 ∪ nbrs u2) ∪ nbrs u3
      have hX_prop : ∀ v ∈ X, ¬ P v := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_union.mp hv).elim (hN u1 hu1 v) (hN u2 hu2 v)
        · exact hN u3 hu3 v hv
      have hX_disj : Disjoint X B :=
        Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr ⟨hdisj_nbr u1 hu1, hdisj_nbr u2 hu2⟩, hdisj_nbr u3 hu3⟩
      have hc := hcompl X hX_prop hX_disj
      have hu12 : (nbrs u1 ∪ nbrs u2).card + (nbrs u1 ∩ nbrs u2).card =
          (nbrs u1).card + (nbrs u2).card := Finset.card_union_add_card_inter _ _
      have hu123 : X.card + ((nbrs u1 ∪ nbrs u2) ∩ nbrs u3).card =
          (nbrs u1 ∪ nbrs u2).card + (nbrs u3).card := Finset.card_union_add_card_inter _ _
      have hint12 := no_four_cycle u1 u2 h12
      have hint3 : ((nbrs u1 ∪ nbrs u2) ∩ nbrs u3).card ≤ 2 := by
        rw [Finset.union_inter_distrib_right]
        exact (Finset.card_union_le _ _).trans
          (Nat.add_le_add (no_four_cycle u1 u3 h31.symm) (no_four_cycle u2 u3 h32.symm))
      rw [nbrs_card u1, nbrs_card u2] at hu12
      rw [nbrs_card u3] at hu123
      omega
  have hB1 := hbound S T (fun u => u.val < 13)
    (fun u hu => (Finset.mem_filter.mp hu).2)
    (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
    (fun u hu v hv => by
      have ha := (Finset.mem_filter.mp hv).2
      have h1 := (adj_diff_side u v ha).mp (Finset.mem_filter.mp hu).2
      omega)
    (by
      have heq : (Finset.univ.filter fun v : Fin 26 => ¬ v.val < 13) =
          (Finset.univ.filter fun v : Fin 26 => 13 ≤ v.val) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [heq, lines_card])
    (fun u hu v hv => hind u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1)
  have hB2 := hbound T S (fun u => 13 ≤ u.val)
    (fun u hu => (Finset.mem_filter.mp hu).2)
    (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
    (fun u hu v hv => by
      have ha := (Finset.mem_filter.mp hv).2
      have h1 := (adj_diff_side u v ha).mpr
      have h2 := (Finset.mem_filter.mp hu).2
      have h3 := (adj_diff_side v u (by rw [adj_symm]; exact ha)).mpr h2
      omega)
    (by
      have heq : (Finset.univ.filter fun v : Fin 26 => ¬ 13 ≤ v.val) =
          (Finset.univ.filter fun v : Fin 26 => v.val < 13) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [heq, pts_card])
    (fun u hu v hv => hind u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1)
  by_cases hS0 : S.card = 0
  · right
    intro u hu
    by_contra hlt
    have : u ∈ S := Finset.mem_filter.mpr ⟨hu, by omega⟩
    have : 0 < S.card := Finset.card_pos.mpr ⟨u, this⟩
    omega
  · by_cases hT0 : T.card = 0
    · left
      intro u hu
      by_contra hge
      have : u ∈ T := Finset.mem_filter.mpr ⟨hu, by omega⟩
      have : 0 < T.card := Finset.card_pos.mpr ⟨u, this⟩
      omega
    · exfalso
      have hS1 : 1 ≤ S.card := by omega
      have hT1 : 1 ≤ T.card := by omega
      by_cases hS2 : S.card = 1
      · have := hB1.1 hS1; omega
      · by_cases hS3 : S.card = 2
        · have := hB1.2.1 (by omega); omega
        · have hT4 := hB1.2.2 (by omega)
          by_cases hT2 : T.card = 1
          · have := hB2.1 hT1; omega
          · by_cases hT3 : T.card = 2
            · have := hB2.2.1 (by omega); omega
            · have hS4 := hB2.2.2 (by omega); omega

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wval (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def opnd0 (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 0 0
def opnd1 (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 1 0

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length (by simp [stepWire])]
      have hlast : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [List.getElem_cons_zero, hlast]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
    | succ j =>
      have key := ih (stepWire w g) j (by simpa using hj)
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using key

lemma wval_input (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) :
    wval C x i.val = x i := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
  rw [foldl_getD_lt C.gates (List.ofFn x) i.val (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

lemma wval_beyond (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (hw : 26 + C.gates.length ≤ w) :
    wval C x w = false := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD w false = false
  have hlen : (C.gates.foldl stepWire (List.ofFn x)).length = 26 + C.gates.length := by
    rw [foldl_length]; simp
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.gates.foldl stepWire (List.ofFn x)).length ≤ w), Option.getD_none]

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma inputs_eq_pair {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd0 C j, opnd1 C j] := by
  have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hj]; exact List.getElem_mem hj
  have hlen := hAO.2.2 (gateAt C j) hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  simp only [opnd0, opnd1, hab, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

lemma opnd_lt {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    opnd0 C j < 26 + j ∧ opnd1 C j < 26 + j := by
  have hin := inputs_eq_pair hAO hj
  have hrb := hAO.2.1 j hj
  rw [hin] at hrb
  exact ⟨hrb _ (by simp), hrb _ (by simp)⟩

lemma wval_and {C : Circuit} (hAO : IsAO2 26 C) (x : Fin 26 → Bool) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (26 + j) = (wval C x (opnd0 C j) && wval C x (opnd1 C j)) := by
  have hl : (List.ofFn x).length = 26 := by simp
  have hge := foldl_getD_gate C.gates (List.ofFn x) j hj
  rw [hl] at hge
  have hgat : gateAt C j = C.gates[j] := gateAt_eq hj
  have hin := inputs_eq_pair hAO hj
  have ⟨h0, h1⟩ := opnd_lt hAO hj
  change (C.gates.foldl stepWire (List.ofFn x)).getD (26 + j) false = _
  rw [hge, ← hgat, hin, hop]
  simp only [List.map_cons, List.map_nil, ite_eq_left h0, ite_eq_left h1, GateOp.eval,
    List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rfl

lemma wval_or {C : Circuit} (hAO : IsAO2 26 C) (x : Fin 26 → Bool) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (26 + j) = (wval C x (opnd0 C j) || wval C x (opnd1 C j)) := by
  have hl : (List.ofFn x).length = 26 := by simp
  have hge := foldl_getD_gate C.gates (List.ofFn x) j hj
  rw [hl] at hge
  have hgat : gateAt C j = C.gates[j] := gateAt_eq hj
  have hin := inputs_eq_pair hAO hj
  have ⟨h0, h1⟩ := opnd_lt hAO hj
  change (C.gates.foldl stepWire (List.ofFn x)).getD (26 + j) false = _
  rw [hge, ← hgat, hin, hop]
  simp only [List.map_cons, List.map_nil, ite_eq_left h0, ite_eq_left h1, GateOp.eval,
    List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma wval_mono {C : Circuit} (hAO : IsAO2 26 C) {x y : Fin 26 → Bool}
    (hle : ∀ i : Fin 26, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hw : w < 26
    · let i : Fin 26 := ⟨w, hw⟩
      rw [wval_input C x i] at hx
      rw [wval_input C y i]
      exact hle i hx
    · by_cases hlt : w - 26 < C.gates.length
      · have hw' : w = 26 + (w - 26) := by omega
        rw [hw'] at hx ⊢
        have ⟨h0, h1⟩ := opnd_lt hAO hlt
        have hmem : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq hlt]; exact List.getElem_mem hlt
        rcases hAO.1 _ hmem with hand | hor
        · rw [wval_and hAO x hlt hand, Bool.and_eq_true] at hx
          rw [wval_and hAO y hlt hand, Bool.and_eq_true]
          exact ⟨ih _ (by omega) hx.1, ih _ (by omega) hx.2⟩
        · rw [wval_or hAO x hlt hor, Bool.or_eq_true] at hx
          rw [wval_or hAO y hlt hor, Bool.or_eq_true]
          exact hx.elim (fun h => Or.inl (ih _ (by omega) h))
            (fun h => Or.inr (ih _ (by omega) h))
      · rw [wval_beyond C x w (by omega)] at hx
        contradiction

def orInAux (C : Circuit) : ℕ → ℕ → Finset (Fin 26)
  | 0, _ => ∅
  | fuel + 1, w =>
    if hw : w < 26 then {⟨w, hw⟩}
    else
      let j := w - 26
      if j < C.gates.length then
        match (gateAt C j).op with
        | GateOp.or => orInAux C fuel (opnd0 C j) ∪ orInAux C fuel (opnd1 C j)
        | _ => ∅
      else ∅

def orInW (C : Circuit) (w : ℕ) : Finset (Fin 26) := orInAux C (w + 1) w

lemma orInAux_stable {C : Circuit} (hAO : IsAO2 26 C) :
    ∀ f1 f2 w, w < f1 → w < f2 → orInAux C f1 w = orInAux C f2 w := by
  intro f1
  induction f1 with
  | zero => intro f2 w hw _; omega
  | succ f1 ih =>
    intro f2 w hw1 hw2
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold orInAux
      by_cases hw : w < 26
      · simp [hw]
      · by_cases hlt : w - 26 < C.gates.length
        · simp only [hw, dite_false, hlt, ite_true]
          have ⟨h0, h1⟩ := opnd_lt hAO hlt
          cases (gateAt C (w - 26)).op
          · rfl
          · rw [ih f2 _ (by omega) (by omega), ih f2 _ (by omega) (by omega)]
          · rfl
          · rfl
          · rfl
        · simp [hw, hlt]

lemma orInW_input (C : Circuit) (w : ℕ) (hw : w < 26) : orInW C w = {⟨w, hw⟩} := by
  unfold orInW orInAux
  simp [hw]

lemma orInW_and (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : orInW C (26 + j) = ∅ := by
  unfold orInW orInAux
  have h1 : ¬ (26 + j < 26) := by omega
  have h2 : 26 + j - 26 = j := by omega
  simp [h1, h2, hj, hop]

lemma orInW_or {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    orInW C (26 + j) = orInW C (opnd0 C j) ∪ orInW C (opnd1 C j) := by
  have ⟨h0, h1⟩ := opnd_lt hAO hj
  unfold orInW
  conv_lhs => unfold orInAux
  have hn : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  simp only [hn, dite_false, hsub, hj, ite_true, hop]
  rw [orInAux_stable hAO (26 + j) (opnd0 C j + 1) (opnd0 C j) h0 (by omega),
      orInAux_stable hAO (26 + j) (opnd1 C j + 1) (opnd1 C j) h1 (by omega)]

lemma wval_of_mem_orInW {C : Circuit} (hAO : IsAO2 26 C) :
    ∀ w (i : Fin 26), i ∈ orInW C w → wval C (single i) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro i hi
    by_cases hw : w < 26
    · rw [orInW_input C w hw, Finset.mem_singleton] at hi
      subst hi
      rw [wval_input C (single ⟨w, hw⟩) ⟨w, hw⟩]
      exact decide_eq_true rfl
    · by_cases hlt : w - 26 < C.gates.length
      · have hw' : w = 26 + (w - 26) := by omega
        rw [hw'] at hi ⊢
        have hmem : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq hlt]; exact List.getElem_mem hlt
        rcases hAO.1 _ hmem with hand | hor
        · rw [orInW_and C hlt hand] at hi; simp at hi
        · rw [orInW_or hAO hlt hor, Finset.mem_union] at hi
          have ⟨h0, h1⟩ := opnd_lt hAO hlt
          rw [wval_or hAO (single i) hlt hor, Bool.or_eq_true]
          rcases hi with hi | hi
          · exact Or.inl (ih _ (by omega) i hi)
          · exact Or.inr (ih _ (by omega) i hi)
      · unfold orInW orInAux at hi
        simp [hw, hlt] at hi

lemma belowF_iff_orInW_empty {C : Circuit} (hAO : IsAO2 26 C)
    (hfun : ∀ x : Fin 26 → Bool, wval C x C.output = true ↔ hit x)
    (hnojunk : ∀ j, (gateAt C j).op = GateOp.and →
      ∀ x : Fin 26 → Bool, wval C x (26 + j) = true → wval C x C.output = true) :
    ∀ w < 26 + C.gates.length,
      (∀ x : Fin 26 → Bool, wval C x w = true → hit x) ↔ orInW C w = ∅ := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt
    constructor
    · intro hbelow
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      exact hit_single i (hbelow (single i) (wval_of_mem_orInW hAO w i hi))
    · intro hempty x hwx
      by_cases hw : w < 26
      · rw [orInW_input C w hw] at hempty
        exact False.elim (Finset.singleton_ne_empty _ hempty)
      · have hlt : w - 26 < C.gates.length := by omega
        have hw' : w = 26 + (w - 26) := by omega
        rw [hw'] at hempty hwx
        have hmem : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq hlt]; exact List.getElem_mem hlt
        rcases hAO.1 _ hmem with hand | hor
        · exact (hfun x).mp (hnojunk (w - 26) hand x hwx)
        · rw [orInW_or hAO hlt hor, Finset.union_eq_empty] at hempty
          have ⟨h0, h1⟩ := opnd_lt hAO hlt
          rw [wval_or hAO x hlt hor, Bool.or_eq_true] at hwx
          rcases hwx with hwx | hwx
          · exact ((ih _ (by omega) (by omega)).mpr hempty.1) x hwx
          · exact ((ih _ (by omega) (by omega)).mpr hempty.2) x hwx

def reachAux (C : Circuit) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | fuel + 1, j =>
    let a := opnd0 C j
    let b := opnd1 C j
    let sa := if 26 ≤ a then reachAux C fuel (a - 26) else ∅
    let sb := if 26 ≤ b then reachAux C fuel (b - 26) else ∅
    insert j (sa ∪ sb)

def liveOf (C : Circuit) (root : ℕ) : Finset ℕ := reachAux C (root + 1) root

lemma reachAux_stable {C : Circuit} (hAO : IsAO2 26 C) :
    ∀ f1 f2 j, j < C.gates.length → j < f1 → j < f2 → reachAux C f1 j = reachAux C f2 j := by
  intro f1
  induction f1 with
  | zero => intro f2 j _ h1 _; omega
  | succ f1 ih =>
    intro f2 j hj h1 h2
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold reachAux
      dsimp only
      have ⟨ha, hb⟩ := opnd_lt hAO hj
      congr 1; congr 1
      · split_ifs with hge
        · exact ih f2 _ (by omega) (by omega) (by omega)
        · rfl
      · split_ifs with hge
        · exact ih f2 _ (by omega) (by omega) (by omega)
        · rfl

lemma liveOf_unfold {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    liveOf C j = insert j
      ((if 26 ≤ opnd0 C j then liveOf C (opnd0 C j - 26) else ∅) ∪
       (if 26 ≤ opnd1 C j then liveOf C (opnd1 C j - 26) else ∅)) := by
  have ⟨ha, hb⟩ := opnd_lt hAO hj
  unfold liveOf
  conv_lhs => unfold reachAux
  dsimp only
  congr 1; congr 1
  · split_ifs with hge
    · exact reachAux_stable hAO j (opnd0 C j - 26 + 1) (opnd0 C j - 26) (by omega) (by omega) (by omega)
    · rfl
  · split_ifs with hge
    · exact reachAux_stable hAO j (opnd1 C j - 26 + 1) (opnd1 C j - 26) (by omega) (by omega) (by omega)
    · rfl

lemma liveOf_le {C : Circuit} (hAO : IsAO2 26 C) :
    ∀ r < C.gates.length, ∀ j ∈ liveOf C r, j ≤ r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr j hj
    rw [liveOf_unfold hAO hr, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact le_rfl
    · have ⟨ha, hb⟩ := opnd_lt hAO hr
      rcases Finset.mem_union.mp hj with hj | hj
      · split_ifs at hj with hge
        · have := ih (opnd0 C r - 26) (by omega) (by omega) j hj; omega
        · simp at hj
      · split_ifs at hj with hge
        · have := ih (opnd1 C r - 26) (by omega) (by omega) j hj; omega
        · simp at hj

lemma liveOf_closed {C : Circuit} (hAO : IsAO2 26 C) {r : ℕ} (hr : r < C.gates.length) :
    ∀ j ∈ liveOf C r,
      (26 ≤ opnd0 C j → opnd0 C j - 26 ∈ liveOf C r) ∧
      (26 ≤ opnd1 C j → opnd1 C j - 26 ∈ liveOf C r) := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro j hj
    rw [liveOf_unfold hAO hr] at hj ⊢
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · have ⟨ha, hb⟩ := opnd_lt hAO hr
      constructor <;> intro hge
      · apply Finset.mem_insert_of_mem; apply Finset.mem_union_left
        rw [ite_eq_left hge, liveOf_unfold hAO (by omega)]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem; apply Finset.mem_union_right
        rw [ite_eq_left hge, liveOf_unfold hAO (by omega)]; exact Finset.mem_insert_self _ _
    · have ⟨ha, hb⟩ := opnd_lt hAO hr
      rcases Finset.mem_union.mp hj' with hj0 | hj1
      · split_ifs at hj0 with hge0
        · have hcl := ih (opnd0 C r - 26) (by omega) (by omega) j hj0
          constructor <;> intro hge
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by rw [ite_eq_left hge0]; exact hcl.1 hge))
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by rw [ite_eq_left hge0]; exact hcl.2 hge))
        · simp at hj0
      · split_ifs at hj1 with hge1
        · have hcl := ih (opnd1 C r - 26) (by omega) (by omega) j hj1
          constructor <;> intro hge
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (by rw [ite_eq_left hge1]; exact hcl.1 hge))
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (by rw [ite_eq_left hge1]; exact hcl.2 hge))
        · simp at hj1

lemma liveOf_has_reader {C : Circuit} (hAO : IsAO2 26 C) :
    ∀ r < C.gates.length, ∀ j ∈ liveOf C r, j ≠ r →
      ∃ k ∈ liveOf C r, opnd0 C k = 26 + j ∨ opnd1 C k = 26 + j := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr j hj hne
    rw [liveOf_unfold hAO hr] at hj
    have hj' : j ∈ (if 26 ≤ opnd0 C r then liveOf C (opnd0 C r - 26) else ∅) ∪
        (if 26 ≤ opnd1 C r then liveOf C (opnd1 C r - 26) else ∅) :=
      (Finset.mem_insert.mp hj).resolve_left hne
    have ⟨ha, hb⟩ := opnd_lt hAO hr
    rcases Finset.mem_union.mp hj' with h0 | h1
    · split_ifs at h0 with hge0
      · by_cases heq : j = opnd0 C r - 26
        · refine ⟨r, ?_, Or.inl (by omega)⟩
          rw [liveOf_unfold hAO hr]; exact Finset.mem_insert_self _ _
        · obtain ⟨k, hk, hread⟩ := ih (opnd0 C r - 26) (by omega) (by omega) j h0 heq
          refine ⟨k, ?_, hread⟩
          rw [liveOf_unfold hAO hr]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by rw [ite_eq_left hge0]; exact hk))
      · simp at h0
    · split_ifs at h1 with hge1
      · by_cases heq : j = opnd1 C r - 26
        · refine ⟨r, ?_, Or.inr (by omega)⟩
          rw [liveOf_unfold hAO hr]; exact Finset.mem_insert_self _ _
        · obtain ⟨k, hk, hread⟩ := ih (opnd1 C r - 26) (by omega) (by omega) j h1 heq
          refine ⟨k, ?_, hread⟩
          rw [liveOf_unfold hAO hr]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (by rw [ite_eq_left hge1]; exact hk))
      · simp at h1

def mergeReps : List (Fin 26 × Fin 26) → (Fin 26 → Fin 26)
  | [] => id
  | (a, b) :: rest =>
    let f := mergeReps rest
    fun x => if f x = f b then f a else f x

lemma mergeReps_image_card (V : Finset (Fin 26)) :
    ∀ L : List (Fin 26 × Fin 26), V.card ≤ (V.image (mergeReps L)).card + L.length := by
  intro L
  induction L with
  | nil => simp [mergeReps]
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    let f := mergeReps rest
    let g : Fin 26 → Fin 26 := fun x => if f x = f b then f a else f x
    have hsub : V.image f ⊆ insert (f b) (V.image g) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      by_cases hxb : f x = f b
      · rw [hxb]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨x, hx, by simp [g, hxb]⟩
    have hc : (V.image f).card ≤ (V.image g).card + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have ih' : V.card ≤ (V.image f).card + rest.length := ih
    change V.card ≤ (V.image g).card + (rest.length + 1)
    omega

lemma mergeReps_eq_of_mem :
    ∀ (L : List (Fin 26 × Fin 26)) (p : Fin 26 × Fin 26), p ∈ L →
      mergeReps L p.1 = mergeReps L p.2 := by
  intro L
  induction L with
  | nil => intro p hp; simp at hp
  | cons q rest ih =>
    intro p hp
    obtain ⟨a, b⟩ := q
    simp only [mergeReps]
    rcases List.mem_cons.mp hp with rfl | hmem
    · simp
    · have heq := ih p hmem
      simp [heq]

lemma pure_or_component_bound {C : Circuit} (hAO : IsAO2 26 C)
    (u : Fin 26) (Live : Finset ℕ)
    (hLive_lt : ∀ j ∈ Live, j < C.gates.length)
    (hLive_cl : ∀ j ∈ Live, (26 ≤ opnd0 C j → opnd0 C j - 26 ∈ Live) ∧
      (26 ≤ opnd1 C j → opnd1 C j - 26 ∈ Live))
    (Au : Finset ℕ) (Op : Finset ℕ) (leafWire : ℕ → ℕ)
    (hAu : ∀ j ∈ Au, leafWire j < 26 + C.gates.length ∧
      (26 ≤ leafWire j → leafWire j - 26 ∈ Live) ∧
      (orInW C (leafWire j)).Nonempty ∧ orInW C (leafWire j) ⊆ nbrs u)
    (hOp : ∀ h ∈ Live, (gateAt C h).op = GateOp.or →
      (orInW C (opnd0 C h)).Nonempty → (orInW C (opnd1 C h)).Nonempty →
      2 ≤ (orInW C (26 + h)).card → orInW C (26 + h) ⊆ nbrs u → h ∈ Op)
    (hOp_valid : ∀ h ∈ Op, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
      (orInW C (opnd0 C h)).Nonempty ∧ (orInW C (opnd1 C h)).Nonempty)
    (Su : Finset (Fin 26))
    (hSu_sub : Su ⊆ nbrs u)
    (hSu_cov : ∀ v ∈ Su, ∃ j ∈ Au, v ∈ orInW C (leafWire j)) :
    Su.card ≤ Au.card + Op.card := by
  classical
  let edgeOf (h : ℕ) : Fin 26 × Fin 26 :=
    if hh : h ∈ Op then
      ((hOp_valid h hh).2.2.1.choose, (hOp_valid h hh).2.2.2.choose)
    else (u, u)
  let L : List (Fin 26 × Fin 26) := Op.toList.map edgeOf
  let rep := mergeReps L
  have hconst : ∀ w < 26 + C.gates.length, (26 ≤ w → w - 26 ∈ Live) →
      orInW C w ⊆ nbrs u →
      ∀ x ∈ orInW C w, ∀ y ∈ orInW C w, rep x = rep y := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt hwLive hsub x hx y hy
      by_cases hw : w < 26
      · rw [orInW_input C w hw, Finset.mem_singleton] at hx hy
        rw [hx, hy]
      · have hjL : w - 26 ∈ Live := hwLive (by omega)
        have hj : w - 26 < C.gates.length := hLive_lt (w - 26) hjL
        have hw' : w = 26 + (w - 26) := by omega
        rw [hw'] at hsub hx hy
        have hmem : gateAt C (w - 26) ∈ C.gates := by
          rw [gateAt_eq hj]; exact List.getElem_mem hj
        rcases hAO.1 _ hmem with hand | hor
        · rw [orInW_and C hj hand] at hx; simp at hx
        · rw [orInW_or hAO hj hor] at hsub hx hy
          have ⟨h0, h1⟩ := opnd_lt hAO hj
          have hcl := hLive_cl (w - 26) hjL
          have hsub0 : orInW C (opnd0 C (w - 26)) ⊆ nbrs u :=
            Finset.subset_union_left.trans hsub
          have hsub1 : orInW C (opnd1 C (w - 26)) ⊆ nbrs u :=
            Finset.subset_union_right.trans hsub
          rcases Finset.mem_union.mp hx with hx0 | hx1 <;>
          rcases Finset.mem_union.mp hy with hy0 | hy1
          · exact ih _ (by omega) (by omega) hcl.1 hsub0 x hx0 y hy0
          · by_cases hcard : 2 ≤ (orInW C (26 + (w - 26))).card
            · have hne0 : (orInW C (opnd0 C (w - 26))).Nonempty := ⟨x, hx0⟩
              have hne1 : (orInW C (opnd1 C (w - 26))).Nonempty := ⟨y, hy1⟩
              have hsubW : orInW C (26 + (w - 26)) ⊆ nbrs u := by
                rw [orInW_or hAO hj hor]; exact hsub
              have hinOp : w - 26 ∈ Op := hOp (w - 26) hjL hor hne0 hne1 hcard hsubW
              have hp : edgeOf (w - 26) ∈ L :=
                List.mem_map_of_mem (Finset.mem_toList.mpr hinOp)
              have heq := mergeReps_eq_of_mem L (edgeOf (w - 26)) hp
              simp only [edgeOf, dif_pos hinOp] at heq
              have ha_mem := (hOp_valid (w - 26) hinOp).2.2.1.choose_spec
              have hb_mem := (hOp_valid (w - 26) hinOp).2.2.2.choose_spec
              exact (ih _ (by omega) (by omega) hcl.1 hsub0 x hx0 _ ha_mem).trans
                (heq.trans (ih _ (by omega) (by omega) hcl.2 hsub1 _ hb_mem y hy1))
            · have hle1 : (orInW C (opnd0 C (w - 26)) ∪ orInW C (opnd1 C (w - 26))).card ≤ 1 := by
                rw [← orInW_or hAO hj hor]; omega
              have hxy : x = y := Finset.card_le_one.mp hle1
                x (Finset.mem_union_left _ hx0) y (Finset.mem_union_right _ hy1)
              rw [hxy]
          · by_cases hcard : 2 ≤ (orInW C (26 + (w - 26))).card
            · have hne0 : (orInW C (opnd0 C (w - 26))).Nonempty := ⟨y, hy0⟩
              have hne1 : (orInW C (opnd1 C (w - 26))).Nonempty := ⟨x, hx1⟩
              have hsubW : orInW C (26 + (w - 26)) ⊆ nbrs u := by
                rw [orInW_or hAO hj hor]; exact hsub
              have hinOp : w - 26 ∈ Op := hOp (w - 26) hjL hor hne0 hne1 hcard hsubW
              have hp : edgeOf (w - 26) ∈ L :=
                List.mem_map_of_mem (Finset.mem_toList.mpr hinOp)
              have heq := mergeReps_eq_of_mem L (edgeOf (w - 26)) hp
              simp only [edgeOf, dite_eq_left hinOp] at heq
              have ha_mem := (hOp_valid (w - 26) hinOp).2.2.1.choose_spec
              have hb_mem := (hOp_valid (w - 26) hinOp).2.2.2.choose_spec
              exact (ih _ (by omega) (by omega) hcl.2 hsub1 x hx1 _ hb_mem).trans
                (heq.symm.trans (ih _ (by omega) (by omega) hcl.1 hsub0 _ ha_mem y hy0))
            · have hle1 : (orInW C (opnd0 C (w - 26)) ∪ orInW C (opnd1 C (w - 26))).card ≤ 1 := by
                rw [← orInW_or hAO hj hor]; omega
              have hxy : x = y := Finset.card_le_one.mp hle1
                x (Finset.mem_union_right _ hx1) y (Finset.mem_union_left _ hy0)
              rw [hxy]
          · exact ih _ (by omega) (by omega) hcl.2 hsub1 x hx1 y hy1
  have h1 : (nbrs u).card ≤ ((nbrs u).image rep).card + Op.card := by
    have h1' := mergeReps_image_card (nbrs u) L
    have hLlen : L.length = Op.card := by simp [L]
    rw [hLlen] at h1'
    exact h1'
  let pick (j : ℕ) : Fin 26 :=
    if hj : j ∈ Au then rep (hAu j hj).2.2.1.choose else u
  have hSimg : Su.image rep ⊆ Au.image pick := by
    intro r hr
    obtain ⟨v, hvS, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨j, hjAu, hvw⟩ := hSu_cov v hvS
    apply Finset.mem_image.mpr
    refine ⟨j, hjAu, ?_⟩
    simp only [pick, dite_eq_left hjAu]
    have hmem := (hAu j hjAu).2.2.1.choose_spec
    exact hconst (leafWire j) (hAu j hjAu).1 (hAu j hjAu).2.1 (hAu j hjAu).2.2.2 _ hmem v hvw
  have hScard : (Su.image rep).card ≤ Au.card :=
    (Finset.card_le_card hSimg).trans Finset.card_image_le
  have hNsplit : (nbrs u).image rep = Su.image rep ∪ (nbrs u \ Su).image rep := by
    rw [← Finset.image_union, Finset.union_sdiff_of_subset hSu_sub]
  have hNimg : ((nbrs u).image rep).card ≤ Au.card + (nbrs u \ Su).card := by
    rw [hNsplit]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hScard Finset.card_image_le)
  have hNs : Su.card + (nbrs u \ Su).card = (nbrs u).card := by
    rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hSu_sub]
  omega

def bConeAux (C : Circuit) (Au : Finset ℕ) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | fuel + 1, j =>
    if j ∈ Au then {j}
    else
      let a := opnd0 C j
      let b := opnd1 C j
      insert j ((if 26 ≤ a then bConeAux C Au fuel (a - 26) else ∅) ∪
        (if 26 ≤ b then bConeAux C Au fuel (b - 26) else ∅))

def bCone (C : Circuit) (Au : Finset ℕ) (j : ℕ) : Finset ℕ := bConeAux C Au (j + 1) j

lemma bConeAux_stable {C : Circuit} (hAO : IsAO2 26 C) (Au : Finset ℕ) :
    ∀ f1 f2 j, j < C.gates.length → j < f1 → j < f2 →
      bConeAux C Au f1 j = bConeAux C Au f2 j := by
  intro f1
  induction f1 with
  | zero => intro f2 j _ h1 _; omega
  | succ f1 ih =>
    intro f2 j hj h1 h2
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold bConeAux
      dsimp only
      by_cases hAu : j ∈ Au
      · simp [hAu]
      · simp only [hAu, ite_false]
        have ⟨ha, hb⟩ := opnd_lt hAO hj
        congr 1; congr 1
        · split_ifs with hge
          · exact ih f2 _ (by omega) (by omega) (by omega)
          · rfl
        · split_ifs with hge
          · exact ih f2 _ (by omega) (by omega) (by omega)
          · rfl

lemma bCone_mem_self (C : Circuit) (Au : Finset ℕ) (j : ℕ) : j ∈ bCone C Au j := by
  unfold bCone bConeAux
  split_ifs
  · exact Finset.mem_singleton_self j
  · exact Finset.mem_insert_self j _

lemma bCone_au (C : Circuit) (Au : Finset ℕ) {j : ℕ} (hj : j ∈ Au) :
    bCone C Au j = {j} := by
  unfold bCone bConeAux
  simp [hj]

lemma bCone_step {C : Circuit} (hAO : IsAO2 26 C) (Au : Finset ℕ) {j : ℕ}
    (hj : j < C.gates.length) (hnot : j ∉ Au)
    (h0 : 26 ≤ opnd0 C j) (h1 : 26 ≤ opnd1 C j) :
    bCone C Au j = insert j (bCone C Au (opnd0 C j - 26) ∪ bCone C Au (opnd1 C j - 26)) := by
  have ⟨ha, hb⟩ := opnd_lt hAO hj
  unfold bCone
  conv_lhs => unfold bConeAux
  simp only [hnot, ite_false, h0, h1, ite_true]
  rw [bConeAux_stable hAO Au j (opnd0 C j - 26 + 1) (opnd0 C j - 26) (by omega) (by omega) (by omega),
      bConeAux_stable hAO Au j (opnd1 C j - 26 + 1) (opnd1 C j - 26) (by omega) (by omega) (by omega)]

lemma bCone_le {C : Circuit} (hAO : IsAO2 26 C) (Au : Finset ℕ) :
    ∀ j < C.gates.length, ∀ g ∈ bCone C Au j, g ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj g hg
    by_cases hAu : j ∈ Au
    · rw [bCone_au C Au hAu, Finset.mem_singleton] at hg; omega
    · unfold bCone at hg
      unfold bConeAux at hg
      simp only [hAu, ite_false, Finset.mem_insert, Finset.mem_union] at hg
      rcases hg with rfl | hg0 | hg1
      · exact le_rfl
      · split_ifs at hg0 with h0
        · have ⟨ha, _⟩ := opnd_lt hAO hj
          rw [bConeAux_stable hAO Au j (opnd0 C j - 26 + 1) (opnd0 C j - 26) (by omega) (by omega) (by omega)] at hg0
          have := ih (opnd0 C j - 26) (by omega) (by omega) g hg0; omega
        · simp at hg0
      · split_ifs at hg1 with h1
        · have ⟨_, hb⟩ := opnd_lt hAO hj
          rw [bConeAux_stable hAO Au j (opnd1 C j - 26 + 1) (opnd1 C j - 26) (by omega) (by omega) (by omega)] at hg1
          have := ih (opnd1 C j - 26) (by omega) (by omega) g hg1; omega
        · simp at hg1

lemma bCone_has_reader {C : Circuit} (hAO : IsAO2 26 C) (Au B : Finset ℕ)
    (hB_lt : ∀ j ∈ B, j < C.gates.length)
    (hB_ch : ∀ j ∈ B, j ∉ Au →
      26 ≤ opnd0 C j ∧ opnd0 C j - 26 ∈ B ∧ 26 ≤ opnd1 C j ∧ opnd1 C j - 26 ∈ B) :
    ∀ j ∈ B, ∀ g ∈ bCone C Au j, g ≠ j →
      ∃ k ∈ B, k ≤ j ∧ (opnd0 C k = 26 + g ∨ opnd1 C k = 26 + g) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjB g hg hne
    by_cases hAu : j ∈ Au
    · rw [bCone_au C Au hAu, Finset.mem_singleton] at hg
      exact False.elim (hne hg)
    · have hjlt := hB_lt j hjB
      have ⟨h0, hc0, h1, hc1⟩ := hB_ch j hjB hAu
      have ⟨ha, hb⟩ := opnd_lt hAO hjlt
      rw [bCone_step hAO Au hjlt hAu h0 h1, Finset.mem_insert, Finset.mem_union] at hg
      rcases hg with rfl | hg0 | hg1
      · exact False.elim (hne rfl)
      · by_cases heq : g = opnd0 C j - 26
        · exact ⟨j, hjB, le_rfl, Or.inl (by omega)⟩
        · obtain ⟨k, hkB, hkle, hread⟩ := ih (opnd0 C j - 26) (by omega) hc0 g hg0 heq
          exact ⟨k, hkB, by omega, hread⟩
      · by_cases heq : g = opnd1 C j - 26
        · exact ⟨j, hjB, le_rfl, Or.inr (by omega)⟩
        · obtain ⟨k, hkB, hkle, hread⟩ := ih (opnd1 C j - 26) (by omega) hc1 g hg1 heq
          exact ⟨k, hkB, by omega, hread⟩

lemma bCone_has_leaf {C : Circuit} (hAO : IsAO2 26 C) (Au B : Finset ℕ)
    (hB_lt : ∀ j ∈ B, j < C.gates.length)
    (hB_ch : ∀ j ∈ B, j ∉ Au →
      26 ≤ opnd0 C j ∧ opnd0 C j - 26 ∈ B ∧ 26 ≤ opnd1 C j ∧ opnd1 C j - 26 ∈ B) :
    ∀ j ∈ B, ∃ g ∈ Au, g ∈ bCone C Au j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjB
    by_cases hAu : j ∈ Au
    · exact ⟨j, hAu, bCone_mem_self C Au j⟩
    · have hjlt := hB_lt j hjB
      have ⟨h0, hc0, h1, _⟩ := hB_ch j hjB hAu
      have ⟨ha, _⟩ := opnd_lt hAO hjlt
      obtain ⟨g, hgAu, hgc⟩ := ih (opnd0 C j - 26) (by omega) hc0
      refine ⟨g, hgAu, ?_⟩
      rw [bCone_step hAO Au hjlt hAu h0 h1]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hgc)

lemma bCone_tree_order {C : Circuit} (hAO : IsAO2 26 C) (Au B : Finset ℕ)
    (hB_lt : ∀ j ∈ B, j < C.gates.length)
    (hB_ch : ∀ j ∈ B, j ∉ Au →
      26 ≤ opnd0 C j ∧ opnd0 C j - 26 ∈ B ∧ 26 ≤ opnd1 C j ∧ opnd1 C j - 26 ∈ B)
    (huniq : ∀ g ∈ B, ∀ k1 ∈ B, ∀ k2 ∈ B,
      (opnd0 C k1 = 26 + g ∨ opnd1 C k1 = 26 + g) →
      (opnd0 C k2 = 26 + g ∨ opnd1 C k2 = 26 + g) → k1 = k2) :
    ∀ s : ℕ, ∀ j1 ∈ B, ∀ j2 ∈ B, j1 + j2 ≤ s → ∀ g ∈ Au,
      g ∈ bCone C Au j1 → g ∈ bCone C Au j2 →
      j1 ∈ bCone C Au j2 ∨ j2 ∈ bCone C Au j1 := by
  intro s
  induction s with
  | zero =>
    intro j1 _ j2 _ hle _ _ _ _
    have h1 : j1 = 0 := by omega
    have h2 : j2 = 0 := by omega
    subst h1; subst h2
    exact Or.inl (bCone_mem_self C Au 0)
  | succ s ih =>
    intro j1 hj1 j2 hj2 hsum g hgAu hg1 hg2
    by_cases heq : j1 = j2
    · subst heq; exact Or.inl (bCone_mem_self C Au j1)
    · have step_lt : ∀ a ∈ B, ∀ b ∈ B, a < b → a + b ≤ s + 1 →
          g ∈ bCone C Au a → g ∈ bCone C Au b → a ∈ bCone C Au b := by
        intro a ha b hb hab hle hga hgb
        have hbnot : b ∉ Au := by
          intro hba
          rw [bCone_au C Au hba, Finset.mem_singleton] at hgb
          have hga_le := bCone_le hAO Au a (hB_lt a ha) g hga
          omega
        have hblt := hB_lt b hb
        have ⟨h0, hc0, h1, hc1⟩ := hB_ch b hb hbnot
        have ⟨ha', hb'⟩ := opnd_lt hAO hblt
        rw [bCone_step hAO Au hblt hbnot h0 h1] at hgb ⊢
        have hgb' : g ∈ bCone C Au (opnd0 C b - 26) ∨ g ∈ bCone C Au (opnd1 C b - 26) := by
          rcases Finset.mem_insert.mp hgb with hbg | hu
          · have hga_le := bCone_le hAO Au a (hB_lt a ha) g hga; omega
          · exact Finset.mem_union.mp hu
        rcases hgb' with hgc | hgc
        · have hord := ih a ha (opnd0 C b - 26) hc0 (by omega) g hgAu hga hgc
          rcases hord with hac | hca
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hac)
          · by_cases heqc : opnd0 C b - 26 = a
            · rw [← heqc]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (bCone_mem_self C Au _))
            · obtain ⟨k, hkB, hkle, hread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch a ha _ hca heqc
              have hkb := huniq _ hc0 k hkB b hb hread (Or.inl (by omega))
              omega
        · have hord := ih a ha (opnd1 C b - 26) hc1 (by omega) g hgAu hga hgc
          rcases hord with hac | hca
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hac)
          · by_cases heqc : opnd1 C b - 26 = a
            · rw [← heqc]
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (bCone_mem_self C Au _))
            · obtain ⟨k, hkB, hkle, hread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch a ha _ hca heqc
              have hkb := huniq _ hc1 k hkB b hb hread (Or.inr (by omega))
              omega
      rcases lt_or_gt_of_ne heq with hlt | hgt
      · exact Or.inl (step_lt j1 hj1 j2 hj2 hlt hsum hg1 hg2)
      · exact Or.inr (step_lt j2 hj2 j1 hj1 hgt (by omega) hg2 hg1)

def mixInAux (C : Circuit) (Omix : Finset ℕ) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | fuel + 1, w =>
    if w < 26 then ∅
    else
      let j := w - 26
      if j < C.gates.length then
        match (gateAt C j).op with
        | GateOp.or =>
          if j ∈ Omix then
            insert j (if (orInW C (opnd0 C j)).Nonempty then mixInAux C Omix fuel (opnd0 C j)
                      else mixInAux C Omix fuel (opnd1 C j))
          else
            mixInAux C Omix fuel (opnd0 C j) ∪ mixInAux C Omix fuel (opnd1 C j)
        | _ => ∅
      else ∅

def mixIn (C : Circuit) (Omix : Finset ℕ) (w : ℕ) : Finset ℕ := mixInAux C Omix (w + 1) w

lemma mixInAux_stable {C : Circuit} (hAO : IsAO2 26 C) (Omix : Finset ℕ) :
    ∀ f1 f2 w, w < f1 → w < f2 → mixInAux C Omix f1 w = mixInAux C Omix f2 w := by
  intro f1
  induction f1 with
  | zero => intro f2 w hw _; omega
  | succ f1 ih =>
    intro f2 w hw1 hw2
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold mixInAux
      dsimp only
      by_cases hw : w < 26
      · simp [hw]
      · by_cases hlt : w - 26 < C.gates.length
        · simp only [hw, ite_false, hlt, ite_true]
          have ⟨h0, h1⟩ := opnd_lt hAO hlt
          cases (gateAt C (w - 26)).op
          · rfl
          · by_cases hm : w - 26 ∈ Omix
            · simp only [hm, ite_true]
              congr 1
              split_ifs
              · exact ih f2 (opnd0 C (w - 26)) (by omega) (by omega)
              · exact ih f2 (opnd1 C (w - 26)) (by omega) (by omega)
            · simp only [hm, ite_false]
              rw [ih f2 (opnd0 C (w - 26)) (by omega) (by omega),
                  ih f2 (opnd1 C (w - 26)) (by omega) (by omega)]
          · rfl
          · rfl
          · rfl
        · simp [hw, hlt]

lemma mixIn_subset_orInW {C : Circuit} (hAO : IsAO2 26 C) (Omix : Finset ℕ)
    (hOm : ∀ h ∈ Omix, h < C.gates.length ∧ (gateAt C h).op = GateOp.or) :
    ∀ w < 26 + C.gates.length, ∀ h ∈ mixIn C Omix w,
      h ∈ Omix ∧ h ≤ w - 26 ∧ orInW C (26 + h) ⊆ orInW C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt h hh
    by_cases hw : w < 26
    · unfold mixIn mixInAux at hh; simp [hw] at hh
    · have hj : w - 26 < C.gates.length := by omega
      have hw' : w = 26 + (w - 26) := by omega
      have ⟨h0, h1⟩ := opnd_lt hAO hj
      unfold mixIn at hh
      unfold mixInAux at hh
      simp only [hw, ite_false, hj, ite_true] at hh
      cases hop : (gateAt C (w - 26)).op with
      | or =>
        rw [hop] at hh
        have hor : orInW C w = orInW C (opnd0 C (w - 26)) ∪ orInW C (opnd1 C (w - 26)) := by
          conv_lhs => rw [hw']
          exact orInW_or hAO hj hop
        split_ifs at hh with hmem hne0
        · rcases Finset.mem_insert.mp hh with rfl | hh'
          · exact ⟨hmem, le_rfl, by rw [← hw']⟩
          · rw [mixInAux_stable hAO Omix w (opnd0 C (w - 26) + 1) (opnd0 C (w - 26)) (by omega) (by omega)] at hh'
            obtain ⟨hm, hle, hsub⟩ := ih (opnd0 C (w - 26)) (by omega) (by omega) h hh'
            exact ⟨hm, by omega, hsub.trans (by rw [hor]; exact Finset.subset_union_left)⟩
        · rcases Finset.mem_insert.mp hh with rfl | hh'
          · exact ⟨hmem, le_rfl, by rw [← hw']⟩
          · rw [mixInAux_stable hAO Omix w (opnd1 C (w - 26) + 1) (opnd1 C (w - 26)) (by omega) (by omega)] at hh'
            obtain ⟨hm, hle, hsub⟩ := ih (opnd1 C (w - 26)) (by omega) (by omega) h hh'
            exact ⟨hm, by omega, hsub.trans (by rw [hor]; exact Finset.subset_union_right)⟩
        · rcases Finset.mem_union.mp hh with hh0 | hh1
          · rw [mixInAux_stable hAO Omix w (opnd0 C (w - 26) + 1) (opnd0 C (w - 26)) (by omega) (by omega)] at hh0
            obtain ⟨hm, hle, hsub⟩ := ih (opnd0 C (w - 26)) (by omega) (by omega) h hh0
            exact ⟨hm, by omega, hsub.trans (by rw [hor]; exact Finset.subset_union_left)⟩
          · rw [mixInAux_stable hAO Omix w (opnd1 C (w - 26) + 1) (opnd1 C (w - 26)) (by omega) (by omega)] at hh1
            obtain ⟨hm, hle, hsub⟩ := ih (opnd1 C (w - 26)) (by omega) (by omega) h hh1
            exact ⟨hm, by omega, hsub.trans (by rw [hor]; exact Finset.subset_union_right)⟩
      | _ => rw [hop] at hh; simp at hh

lemma wval_above_decompose {C : Circuit} (hAO : IsAO2 26 C) (Omix : Finset ℕ)
    (hOm_iff : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      (orInW C (26 + j)).Nonempty →
      (j ∈ Omix ↔ (orInW C (opnd0 C j) = ∅ ∨ orInW C (opnd1 C j) = ∅))) :
    ∀ w < 26 + C.gates.length, (orInW C w).Nonempty →
      ∀ x : Fin 26 → Bool, wval C x w = true →
      (∃ i ∈ orInW C w, x i = true) ∨
      (∃ h ∈ mixIn C Omix w, ∃ c < 26 + h, (c = opnd0 C h ∨ c = opnd1 C h) ∧
        orInW C c = ∅ ∧ wval C x c = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hne x hwx
    by_cases hw : w < 26
    · left
      refine ⟨⟨w, hw⟩, ?_, ?_⟩
      · rw [orInW_input C w hw]; exact Finset.mem_singleton_self _
      · rw [wval_input C x ⟨w, hw⟩] at hwx; exact hwx
    · have hj : w - 26 < C.gates.length := by omega
      have hw' : w = 26 + (w - 26) := by omega
      have hmem : gateAt C (w - 26) ∈ C.gates := by rw [gateAt_eq hj]; exact List.getElem_mem hj
      rcases hAO.1 _ hmem with hand | hor
      · rw [hw', orInW_and C hj hand] at hne; exact False.elim (Finset.not_nonempty_empty hne)
      · have ⟨h0, h1⟩ := opnd_lt hAO hj
        have horIn : orInW C w = orInW C (opnd0 C (w - 26)) ∪ orInW C (opnd1 C (w - 26)) := by
          conv_lhs => rw [hw']; exact orInW_or hAO hj hor
        have hwx' : wval C x (opnd0 C (w - 26)) = true ∨ wval C x (opnd1 C (w - 26)) = true := by
          rw [hw', wval_or hAO x hj hor, Bool.or_eq_true] at hwx; exact hwx
        have hne_j : (orInW C (26 + (w - 26))).Nonempty := by rw [← hw']; exact hne
        by_cases hmix : w - 26 ∈ Omix
        · have hem := (hOm_iff (w - 26) hj hor hne_j).mp hmix
          have hmix_eq : mixIn C Omix w =
              insert (w - 26) (if (orInW C (opnd0 C (w - 26))).Nonempty
                then mixIn C Omix (opnd0 C (w - 26))
                else mixIn C Omix (opnd1 C (w - 26))) := by
            unfold mixIn
            conv_lhs => unfold mixInAux
            simp only [hw, ite_false, hj, ite_true, hor, hmix]
            congr 1
            split_ifs
            · exact mixInAux_stable hAO Omix w (opnd0 C (w - 26) + 1) (opnd0 C (w - 26)) (by omega) (by omega)
            · exact mixInAux_stable hAO Omix w (opnd1 C (w - 26) + 1) (opnd1 C (w - 26)) (by omega) (by omega)
          rcases hem with he0 | he1
          · have hne1 : (orInW C (opnd1 C (w - 26))).Nonempty := by
              rw [horIn, he0, Finset.empty_union] at hne; exact hne
            have hnot0 : ¬ (orInW C (opnd0 C (w - 26))).Nonempty := by simp [he0]
            rcases hwx' with hw0 | hw1
            · right
              refine ⟨w - 26, ?_, opnd0 C (w - 26), h0, Or.inl rfl, he0, hw0⟩
              rw [hmix_eq]; exact Finset.mem_insert_self _ _
            · rcases ih (opnd1 C (w - 26)) (by omega) (by omega) hne1 x hw1 with ⟨i, hi, hxi⟩ | ⟨h, hh, c, hc⟩
              · exact Or.inl ⟨i, by rw [horIn]; exact Finset.mem_union_right _ hi, hxi⟩
              · refine Or.inr ⟨h, ?_, c, hc⟩
                rw [hmix_eq, ite_eq_right hnot0]; exact Finset.mem_insert_of_mem hh
          · have hne0 : (orInW C (opnd0 C (w - 26))).Nonempty := by
              rw [horIn, he1, Finset.union_empty] at hne; exact hne
            rcases hwx' with hw0 | hw1
            · rcases ih (opnd0 C (w - 26)) (by omega) (by omega) hne0 x hw0 with ⟨i, hi, hxi⟩ | ⟨h, hh, c, hc⟩
              · exact Or.inl ⟨i, by rw [horIn]; exact Finset.mem_union_left _ hi, hxi⟩
              · refine Or.inr ⟨h, ?_, c, hc⟩
                rw [hmix_eq, ite_eq_left hne0]; exact Finset.mem_insert_of_mem hh
            · right
              refine ⟨w - 26, ?_, opnd1 C (w - 26), h1, Or.inr rfl, he1, hw1⟩
              rw [hmix_eq]; exact Finset.mem_insert_self _ _
        · have hboth := (hOm_iff (w - 26) hj hor hne_j).not.mp hmix
          push Not at hboth
          have hne0 : (orInW C (opnd0 C (w - 26))).Nonempty := hboth.1
          have hne1 : (orInW C (opnd1 C (w - 26))).Nonempty := hboth.2
          have hmix_eq : mixIn C Omix w =
              mixIn C Omix (opnd0 C (w - 26)) ∪ mixIn C Omix (opnd1 C (w - 26)) := by
            unfold mixIn
            conv_lhs => unfold mixInAux
            simp only [hw, ite_false, hj, ite_true, hor, hmix]
            rw [mixInAux_stable hAO Omix w (opnd0 C (w - 26) + 1) (opnd0 C (w - 26)) (by omega) (by omega),
                mixInAux_stable hAO Omix w (opnd1 C (w - 26) + 1) (opnd1 C (w - 26)) (by omega) (by omega)]
          rcases hwx' with hw0 | hw1
          · rcases ih (opnd0 C (w - 26)) (by omega) (by omega) hne0 x hw0 with ⟨i, hi, hxi⟩ | ⟨h, hh, c, hc⟩
            · exact Or.inl ⟨i, by rw [horIn]; exact Finset.mem_union_left _ hi, hxi⟩
            · exact Or.inr ⟨h, by rw [hmix_eq]; exact Finset.mem_union_left _ hh, c, hc⟩
          · rcases ih (opnd1 C (w - 26)) (by omega) (by omega) hne1 x hw1 with ⟨i, hi, hxi⟩ | ⟨h, hh, c, hc⟩
            · exact Or.inl ⟨i, by rw [horIn]; exact Finset.mem_union_right _ hi, hxi⟩
            · exact Or.inr ⟨h, by rw [hmix_eq]; exact Finset.mem_union_right _ hh, c, hc⟩

set_option maxHeartbeats 1600000 in
theorem main_proof (C : Circuit) (hsize : C.size ≤ 64) (hAO : IsAO2 26 C)
    (hnodup : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.inputs.Nodup)
    (hfun : ∀ x : Fin 26 → Bool, wval C x C.output = true ↔ hit x)
    (hnojunk : ∀ j : ℕ, (gateAt C j).op = GateOp.and →
      ∀ x : Fin 26 → Bool, wval C x (26 + j) = true → wval C x C.output = true)
    (p l : Fin 13) (hpl : E p l) :
    let P : Fin 26 := Fin.castAdd 13 p
    let L : Fin 26 := Fin.natAdd 13 l
    ∀ k a b : ℕ,
      C.gates[k]? = some ⟨GateOp.and, [a, b]⟩ →
      wval C (pair P L) (26 + k) = true →
      (wval C (single P) a || wval C (single P) b) = true ∨
      (wval C (single L) a || wval C (single L) b) = true := by
  classical
  have hout_ge : 26 ≤ C.output := by
    by_contra hlt; push Not at hlt
    let i : Fin 26 := ⟨C.output, hlt⟩
    have h1 : wval C (single i) C.output = true := by
      rw [wval_input C (single i) i]; exact decide_eq_true rfl
    exact hit_single i ((hfun (single i)).mp h1)
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge; push Not at hge
    have h1 : wval C (pair (Fin.castAdd 13 p) (Fin.natAdd 13 l)) C.output = false :=
      wval_beyond C _ C.output hge
    have h2 : hit (pair (Fin.castAdd 13 p) (Fin.natAdd 13 l)) :=
      ⟨p, l, hpl, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
    have h3 := (hfun _).mpr h2
    rw [h1] at h3; contradiction
  let root : ℕ := C.output - 26
  have hroot_lt : root < C.gates.length := by omega
  have hroot_eq : 26 + root = C.output := by omega
  have hbelow := belowF_iff_orInW_empty hAO hfun hnojunk
  have hroot_empty : orInW C (26 + root) = ∅ := by
    rw [hroot_eq]
    exact (hbelow C.output hout_lt).mp fun x hx => (hfun x).mp hx
  let Live := liveOf C root
  have hLive_lt : ∀ j ∈ Live, j < C.gates.length := fun j hj => by
    have := liveOf_le hAO root hroot_lt j hj; omega
  have hLive_sub : Live ⊆ Finset.range C.gates.length := fun j hj =>
    Finset.mem_range.mpr (hLive_lt j hj)
  have hLive_card : Live.card ≤ 64 := by
    have h1 := Finset.card_le_card hLive_sub
    rw [Finset.card_range] at h1
    change C.gates.length ≤ 64 at hsize
    omega
  have hroot_live : root ∈ Live := by
    change root ∈ liveOf C root
    rw [liveOf_unfold hAO hroot_lt]
    exact Finset.mem_insert_self _ _
  -- Partition Live into 5 disjoint sets:
  let Au := Live.filter fun j => (gateAt C j).op = GateOp.and ∧
    (orInW C (opnd0 C j)).Nonempty ∧ (orInW C (opnd1 C j)).Nonempty
  let As := Live.filter fun j => (gateAt C j).op = GateOp.and ∧
    (orInW C (opnd0 C j) = ∅ ∨ orInW C (opnd1 C j) = ∅)
  let Ob := Live.filter fun j => (gateAt C j).op = GateOp.or ∧
    orInW C (opnd0 C j) = ∅ ∧ orInW C (opnd1 C j) = ∅
  let Om := Live.filter fun j => (gateAt C j).op = GateOp.or ∧
    ((orInW C (opnd0 C j) = ∅ ∧ (orInW C (opnd1 C j)).Nonempty) ∨
     ((orInW C (opnd0 C j)).Nonempty ∧ orInW C (opnd1 C j) = ∅))
  let Op := Live.filter fun j => (gateAt C j).op = GateOp.or ∧
    (orInW C (opnd0 C j)).Nonempty ∧ (orInW C (opnd1 C j)).Nonempty
  let B := Live.filter fun j => orInW C (26 + j) = ∅
  have hB_eq : B = Au ∪ (As ∪ Ob) := by
    ext j
    simp only [B, Au, As, Ob, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hjL, hem⟩
      have hjlt := hLive_lt j hjL
      have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hjlt]; exact List.getElem_mem hjlt
      rcases hAO.1 _ hmem with hand | hor
      · by_cases h0 : orInW C (opnd0 C j) = ∅
        · exact Or.inr (Or.inl ⟨hjL, hand, Or.inl h0⟩)
        · by_cases h1 : orInW C (opnd1 C j) = ∅
          · exact Or.inr (Or.inl ⟨hjL, hand, Or.inr h1⟩)
          · exact Or.inl ⟨hjL, hand, Finset.nonempty_iff_ne_empty.mpr h0, Finset.nonempty_iff_ne_empty.mpr h1⟩
      · rw [orInW_or hAO hjlt hor, Finset.union_eq_empty] at hem
        exact Or.inr (Or.inr ⟨hjL, hor, hem.1, hem.2⟩)
    · rintro (⟨hjL, hand, _, _⟩ | ⟨hjL, hand, _⟩ | ⟨hjL, hor, h0, h1⟩)
      · exact ⟨hjL, orInW_and C (hLive_lt j hjL) hand⟩
      · exact ⟨hjL, orInW_and C (hLive_lt j hjL) hand⟩
      · exact ⟨hjL, by rw [orInW_or hAO (hLive_lt j hjL) hor, h0, h1, Finset.empty_union]⟩
  have hpart_sum : Au.card + As.card + Ob.card + Om.card + Op.card = Live.card := by
    have hdisj : ∀ (X Y : Finset ℕ), (∀ j, j ∈ X → j ∉ Y) → Disjoint X Y :=
      fun X Y h => Finset.disjoint_left.mpr h
    have hd1 : Disjoint Au As := hdisj _ _ fun j hj1 hj2 => by
      simp only [Au, As, Finset.mem_filter] at hj1 hj2
      rcases hj2.2.2 with h0 | h1
      · exact Finset.nonempty_iff_ne_empty.mp hj1.2.2.1 h0
      · exact Finset.nonempty_iff_ne_empty.mp hj1.2.2.2 h1
    have hd2 : Disjoint (Au ∪ As) Ob := hdisj _ _ fun j hj1 hj2 => by
      simp only [Au, As, Ob, Finset.mem_union, Finset.mem_filter] at hj1 hj2
      rcases hj1 with h | h <;> rw [h.2.1] at hj2 <;> simp at hj2
    have hd3 : Disjoint (Au ∪ As ∪ Ob) Om := hdisj _ _ fun j hj1 hj2 => by
      simp only [Au, As, Ob, Om, Finset.mem_union, Finset.mem_filter] at hj1 hj2
      rcases hj1 with (h | h) | h
      · rw [h.2.1] at hj2; simp at hj2
      · rw [h.2.1] at hj2; simp at hj2
      · rcases hj2.2.2 with ⟨_, h1⟩ | ⟨h0, _⟩
        · exact Finset.nonempty_iff_ne_empty.mp h1 h.2.2.2
        · exact Finset.nonempty_iff_ne_empty.mp h0 h.2.2.1
    have hd4 : Disjoint (Au ∪ As ∪ Ob ∪ Om) Op := hdisj _ _ fun j hj1 hj2 => by
      simp only [Au, As, Ob, Om, Op, Finset.mem_union, Finset.mem_filter] at hj1 hj2
      rcases hj1 with ((h | h) | h) | h
      · rw [h.2.1] at hj2; simp at hj2
      · rw [h.2.1] at hj2; simp at hj2
      · exact Finset.nonempty_iff_ne_empty.mp hj2.2.2.1 h.2.2.1
      · rcases h.2.2 with ⟨h0, _⟩ | ⟨_, h1⟩
        · exact Finset.nonempty_iff_ne_empty.mp hj2.2.2.1 h0
        · exact Finset.nonempty_iff_ne_empty.mp hj2.2.2.2 h1
    have hunion : Au ∪ As ∪ Ob ∪ Om ∪ Op = Live := by
      ext j
      simp only [Au, As, Ob, Om, Op, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((((h | h) | h) | h) | h) <;> exact h.1
      · intro hjL
        have hjlt := hLive_lt j hjL
        have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hjlt]; exact List.getElem_mem hjlt
        rcases hAO.1 _ hmem with hand | hor
        · by_cases h0 : orInW C (opnd0 C j) = ∅
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hjL, hand, Or.inl h0⟩)))
          · by_cases h1 : orInW C (opnd1 C j) = ∅
            · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hjL, hand, Or.inr h1⟩)))
            · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hjL, hand,
                Finset.nonempty_iff_ne_empty.mpr h0, Finset.nonempty_iff_ne_empty.mpr h1⟩)))
        · by_cases h0 : orInW C (opnd0 C j) = ∅ <;> by_cases h1 : orInW C (opnd1 C j) = ∅
          · exact Or.inl (Or.inl (Or.inr ⟨hjL, hor, h0, h1⟩))
          · exact Or.inl (Or.inr ⟨hjL, hor, Or.inl ⟨h0, Finset.nonempty_iff_ne_empty.mpr h1⟩⟩)
          · exact Or.inl (Or.inr ⟨hjL, hor, Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h0, h1⟩⟩)
          · exact Or.inr ⟨hjL, hor, Finset.nonempty_iff_ne_empty.mpr h0, Finset.nonempty_iff_ne_empty.mpr h1⟩
    rw [← hunion, Finset.card_union_of_disjoint hd4, Finset.card_union_of_disjoint hd3,
        Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hB_card : B.card = Au.card + As.card + Ob.card := by
    have hd1 : Disjoint As Ob := Finset.disjoint_left.mpr fun j h1 h2 => by
      simp only [As, Ob, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; simp at h2
    have hd2 : Disjoint Au (As ∪ Ob) := Finset.disjoint_left.mpr fun j h1 h2 => by
      simp only [Au, As, Ob, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h2 with h2 | h2
      · rcases h2.2.2 with h0 | h1'
        · exact Finset.nonempty_iff_ne_empty.mp h1.2.2.1 h0
        · exact Finset.nonempty_iff_ne_empty.mp h1.2.2.2 h1'
      · rw [h1.2.1] at h2; simp at h2
    rw [hB_eq, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]; omega
  -- Step 5: Every edge (u, v) in edgePairs is a star edge of some j ∈ Au:
  have hAu_adj : ∀ j ∈ Au, ∀ a ∈ orInW C (opnd0 C j), ∀ b ∈ orInW C (opnd1 C j), adj a b = true := by
    intro j hjAu a ha b hb
    have hjL := (Finset.mem_filter.mp hjAu).1
    have hjlt := hLive_lt j hjL
    have hand := (Finset.mem_filter.mp hjAu).2.1
    have ha_t : wval C (pair a b) (opnd0 C j) = true :=
      wval_mono hAO (fun i hi => by
        have : i = a := of_decide_eq_true hi; subst this; exact decide_eq_true (Or.inl rfl))
        _ (wval_of_mem_orInW hAO _ a ha)
    have hb_t : wval C (pair a b) (opnd1 C j) = true :=
      wval_mono hAO (fun i hi => by
        have : i = b := of_decide_eq_true hi; subst this; exact decide_eq_true (Or.inr rfl))
        _ (wval_of_mem_orInW hAO _ b hb)
    have hj_t : wval C (pair a b) (26 + j) = true := by
      rw [wval_and hAO _ hjlt hand, ha_t, hb_t]; rfl
    exact (hit_pair a b).mp ((hfun _).mp (hnojunk j hand _ hj_t))
  have hAu_star : ∀ j ∈ Au, (orInW C (opnd0 C j)).card = 1 ∨ (orInW C (opnd1 C j)).card = 1 := by
    intro j hjAu
    by_contra hnot; push Not at hnot
    have hne0 := (Finset.mem_filter.mp hjAu).2.2.1
    have hne1 := (Finset.mem_filter.mp hjAu).2.2.2
    have h20 : 1 < (orInW C (opnd0 C j)).card := by
      have := Finset.card_pos.mpr hne0; omega
    have h21 : 1 < (orInW C (opnd1 C j)).card := by
      have := Finset.card_pos.mpr hne1; omega
    obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp h20
    have hsub : orInW C (opnd1 C j) ⊆ nbrs a1 ∩ nbrs a2 := by
      intro b hb
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAu_adj j hjAu a1 ha1 b hb⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAu_adj j hjAu a2 ha2 b hb⟩⟩
    have hc := (Finset.card_le_card hsub).trans (no_four_cycle a1 a2 hne)
    omega
  have hedge_cover : ∀ e ∈ edgePairs, ∃ j ∈ Au,
      (e.1 ∈ orInW C (opnd0 C j) ∧ e.2 ∈ orInW C (opnd1 C j)) ∨
      (e.2 ∈ orInW C (opnd0 C j) ∧ e.1 ∈ orInW C (opnd1 C j)) := by
    intro e he
    have he_adj : adj e.1 e.2 = true := (Finset.mem_filter.mp he).2.2
    let x := pair e.1 e.2
    have hx_root : wval C x (26 + root) = true := by
      rw [hroot_eq]; exact (hfun x).mpr ((hit_pair e.1 e.2).mpr he_adj)
    have hex : ∃ j : ℕ, j ∈ B ∧ wval C x (26 + j) = true :=
      ⟨root, Finset.mem_filter.mpr ⟨hroot_live, hroot_empty⟩, hx_root⟩
    let j := Nat.find hex
    have hj_spec := Nat.find_spec hex
    have hj_min : ∀ j' < j, ¬ (j' ∈ B ∧ wval C x (26 + j') = true) :=
      fun j' hlt => Nat.find_min hex hlt
    have hjL : j ∈ Live := (Finset.mem_filter.mp hj_spec.1).1
    have hj_emp : orInW C (26 + j) = ∅ := (Finset.mem_filter.mp hj_spec.1).2
    have hjlt := hLive_lt j hjL
    have hj_and : (gateAt C j).op = GateOp.and := by
      have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hjlt]; exact List.getElem_mem hjlt
      rcases hAO.1 _ hmem with hand | hor
      · exact hand
      · exfalso
        rw [orInW_or hAO hjlt hor, Finset.union_eq_empty] at hj_emp
        rw [wval_or hAO x hjlt hor, Bool.or_eq_true] at hj_spec
        have ⟨h0, h1⟩ := opnd_lt hAO hjlt
        have hcl := liveOf_closed hAO hroot_lt j hjL
        rcases hj_spec.2 with hw0 | hw1
        · have hge : 26 ≤ opnd0 C j := by
            by_contra hlt; push Not at hlt
            rw [orInW_input C (opnd0 C j) hlt] at hj_emp
            exact Finset.singleton_ne_empty _ hj_emp.1
          apply hj_min (opnd0 C j - 26) (by omega)
          refine ⟨Finset.mem_filter.mpr ⟨hcl.1 hge, by rw [show 26 + (opnd0 C j - 26) = opnd0 C j by omega]; exact hj_emp.1⟩, ?_⟩
          rw [show 26 + (opnd0 C j - 26) = opnd0 C j by omega]; exact hw0
        · have hge : 26 ≤ opnd1 C j := by
            by_contra hlt; push Not at hlt
            rw [orInW_input C (opnd1 C j) hlt] at hj_emp
            exact Finset.singleton_ne_empty _ hj_emp.2
          apply hj_min (opnd1 C j - 26) (by omega)
          refine ⟨Finset.mem_filter.mpr ⟨hcl.2 hge, by rw [show 26 + (opnd1 C j - 26) = opnd1 C j by omega]; exact hj_emp.2⟩, ?_⟩
          rw [show 26 + (opnd1 C j - 26) = opnd1 C j by omega]; exact hw1
    have hwire_in : ∀ w < 26 + j, (26 ≤ w → w - 26 ∈ Live) → wval C x w = true →
        ∃ i ∈ orInW C w, x i = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hwL hwx
        by_cases hwn : w < 26
        · refine ⟨⟨w, hwn⟩, by rw [orInW_input C w hwn]; exact Finset.mem_singleton_self _, ?_⟩
          rw [wval_input C x ⟨w, hwn⟩] at hwx; exact hwx
        · have hge : 26 ≤ w := by omega
          have hwLive : w - 26 ∈ Live := hwL hge
          have hw' : w = 26 + (w - 26) := by omega
          by_cases hemp : orInW C w = ∅
          · exfalso
            apply hj_min (w - 26) (by omega)
            exact ⟨Finset.mem_filter.mpr ⟨hwLive, by rwa [← hw']⟩, by rwa [← hw']⟩
          · have hglt := hLive_lt (w - 26) hwLive
            have hmem : gateAt C (w - 26) ∈ C.gates := by
              rw [gateAt_eq hglt]; exact List.getElem_mem hglt
            rcases hAO.1 _ hmem with hand | hor
            · exfalso; exact hemp (by rw [hw']; exact orInW_and C hglt hand)
            · rw [hw', wval_or hAO x hglt hor, Bool.or_eq_true] at hwx
              have ⟨h0, h1⟩ := opnd_lt hAO hglt
              have hcl := liveOf_closed hAO hroot_lt (w - 26) hwLive
              rcases hwx with hw0 | hw1
              · obtain ⟨i, hi, hxi⟩ := ih (opnd0 C (w - 26)) (by omega) (by omega) hcl.1 hw0
                exact ⟨i, by rw [hw', orInW_or hAO hglt hor]; exact Finset.mem_union_left _ hi, hxi⟩
              · obtain ⟨i, hi, hxi⟩ := ih (opnd1 C (w - 26)) (by omega) (by omega) hcl.2 hw1
                exact ⟨i, by rw [hw', orInW_or hAO hglt hor]; exact Finset.mem_union_right _ hi, hxi⟩
    have hj_t := hj_spec.2
    rw [wval_and hAO x hjlt hj_and, Bool.and_eq_true] at hj_t
    have ⟨h0, h1⟩ := opnd_lt hAO hjlt
    have hcl := liveOf_closed hAO hroot_lt j hjL
    obtain ⟨i0, hi0, hxi0⟩ := hwire_in (opnd0 C j) h0 hcl.1 hj_t.1
    obtain ⟨i1, hi1, hxi1⟩ := hwire_in (opnd1 C j) h1 hcl.2 hj_t.2
    have hjAu : j ∈ Au := Finset.mem_filter.mpr ⟨hjL, hj_and, ⟨i0, hi0⟩, ⟨i1, hi1⟩⟩
    have hi0_eq := of_decide_eq_true hxi0
    have hi1_eq := of_decide_eq_true hxi1
    have hne01 : i0 ≠ i1 := by
      intro heq; subst heq
      have ha := hAu_adj j hjAu i0 hi0 i0 hi1
      rw [adj_irrefl] at ha; contradiction
    refine ⟨j, hjAu, ?_⟩
    rcases hi0_eq with rfl | rfl <;> rcases hi1_eq with rfl | rfl
    · exact False.elim (hne01 rfl)
    · exact Or.inl ⟨hi0, hi1⟩
    · exact Or.inr ⟨hi0, hi1⟩
    · exact False.elim (hne01 rfl)
  -- Step 6: Assign each j ∈ Au a center and leafWire, and prove 52 ≤ Au.card + Op.card and 13 ≤ Au.card:
  let center (j : ℕ) : Fin 26 :=
    if hj : j ∈ Au then
      if h0 : (orInW C (opnd0 C j)).card = 1 then
        (Finset.card_eq_one.mp h0).choose
      else
        (Finset.card_eq_one.mp ((hAu_star j hj).resolve_left h0)).choose
    else ⟨0, by omega⟩
  let leafWire (j : ℕ) : ℕ :=
    if (orInW C (opnd0 C j)).card = 1 then opnd1 C j else opnd0 C j
  let centerWire (j : ℕ) : ℕ :=
    if (orInW C (opnd0 C j)).card = 1 then opnd0 C j else opnd1 C j
  have hcenter_spec : ∀ j ∈ Au,
      orInW C (centerWire j) = {center j} ∧
      (orInW C (leafWire j)).Nonempty ∧
      orInW C (leafWire j) ⊆ nbrs (center j) ∧
      leafWire j < 26 + C.gates.length ∧
      centerWire j < 26 + C.gates.length := by
    intro j hjAu
    have hjlt := hLive_lt j (Finset.mem_filter.mp hjAu).1
    have ⟨h0lt, h1lt⟩ := opnd_lt hAO hjlt
    have hne0 := (Finset.mem_filter.mp hjAu).2.2.1
    have hne1 := (Finset.mem_filter.mp hjAu).2.2.2
    by_cases h0 : (orInW C (opnd0 C j)).card = 1
    · have hce : orInW C (opnd0 C j) = {center j} := by
        simp only [center, dif_pos hjAu, dif_pos h0]
        exact (Finset.card_eq_one.mp h0).choose_spec
      refine ⟨by simpa [centerWire, h0] using hce, by simpa [leafWire, h0] using hne1, ?_, by simp [leafWire, h0]; omega, by simp [centerWire, h0]; omega⟩
      simp only [leafWire, ite_eq_left h0]
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAu_adj j hjAu (center j) (by rw [hce]; exact Finset.mem_singleton_self _) v hv⟩
    · have h1 : (orInW C (opnd1 C j)).card = 1 := (hAu_star j hjAu).resolve_left h0
      have hce : orInW C (opnd1 C j) = {center j} := by
        simp only [center, dif_pos hjAu, dif_neg h0]
        exact (Finset.card_eq_one.mp h1).choose_spec
      refine ⟨by simpa [centerWire, h0] using hce, by simpa [leafWire, h0] using hne0, ?_, by simp [leafWire, h0]; omega, by simp [centerWire, h0]; omega⟩
      simp only [leafWire, ite_eq_right h0]
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [adj_symm]; exact hAu_adj j hjAu v hv (center j) (by rw [hce]; exact Finset.mem_singleton_self _)⟩
  let Au_at (u : Fin 26) : Finset ℕ := Au.filter fun j => center j = u
  let Su (u : Fin 26) : Finset (Fin 26) := (Au_at u).biUnion fun j => orInW C (leafWire j)
  let Op_at (u : Fin 26) : Finset ℕ := Op.filter fun h =>
    2 ≤ (orInW C (26 + h)).card ∧ orInW C (26 + h) ⊆ nbrs u
  have hSu_sub (u : Fin 26) : Su u ⊆ nbrs u := by
    intro v hv
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨hjAu, hcu⟩ := Finset.mem_filter.mp hj
    rw [← hcu]
    exact (hcenter_spec j hjAu).2.2.1 hvj
  have hSu_card_le4 (u : Fin 26) : (Su u).card ≤ 4 :=
    (Finset.card_le_card (hSu_sub u)).trans (by rw [nbrs_card u])
  have hSu_le_4Au (u : Fin 26) : (Su u).card ≤ 4 * (Au_at u).card := by
    by_cases h0 : (Au_at u).card = 0
    · have hem : Au_at u = ∅ := Finset.card_eq_zero.mp h0
      simp [Su, hem]
    · have := hSu_card_le4 u; omega
  have hOp_bound (u : Fin 26) : (Su u).card ≤ (Au_at u).card + (Op_at u).card := by
    apply pure_or_component_bound hAO u Live hLive_lt (liveOf_closed hAO hroot_lt) (Au_at u) (Op_at u) leafWire
    · intro j hj
      obtain ⟨hjAu, rfl⟩ := Finset.mem_filter.mp hj
      have hs := hcenter_spec j hjAu
      have hcl := liveOf_closed hAO hroot_lt j (Finset.mem_filter.mp hjAu).1
      refine ⟨hs.2.2.2.1, ?_, hs.2.1, hs.2.2.1⟩
      intro hge
      by_cases h0 : (orInW C (opnd0 C j)).card = 1
      · simp only [leafWire, ite_eq_left h0] at hge ⊢; exact hcl.2 hge
      · simp only [leafWire, ite_eq_right h0] at hge ⊢; exact hcl.1 hge
    · intro h hL hor hne0 hne1 h2 hsub
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hL, hor, hne0, hne1⟩, h2, hsub⟩
    · intro h hh
      obtain ⟨hOp, _, _⟩ := Finset.mem_filter.mp hh
      obtain ⟨hL, hor, hne0, hne1⟩ := Finset.mem_filter.mp hOp
      exact ⟨hLive_lt h hL, hor, hne0, hne1⟩
    · exact hSu_sub u
    · intro v hv
      exact Finset.mem_biUnion.mp hv
  -- Sum over all u : Fin 26:
  have hOp_disj : ∀ u1 u2 : Fin 26, u1 ≠ u2 → Disjoint (Op_at u1) (Op_at u2) := by
    intro u1 u2 hne
    rw [Finset.disjoint_left]
    intro h h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    have hsub : orInW C (26 + h) ⊆ nbrs u1 ∩ nbrs u2 := Finset.subset_inter h1'.2 h2'.2
    have hc := (Finset.card_le_card hsub).trans (no_four_cycle u1 u2 hne)
    omega
  have hOp_sum : (∑ u : Fin 26, (Op_at u).card) ≤ Op.card := by
    rw [← Finset.card_biUnion (fun u1 _ u2 _ hne => hOp_disj u1 u2 hne)]
    apply Finset.card_le_card
    intro h hh
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hh
    exact (Finset.mem_filter.mp hu).1
  have hAu_sum : (∑ u : Fin 26, (Au_at u).card) = Au.card := by
    have hd : ∀ u1 u2 : Fin 26, u1 ≠ u2 → Disjoint (Au_at u1) (Au_at u2) := by
      intro u1 u2 hne
      rw [Finset.disjoint_left]
      intro j h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      exact hne (by rw [← (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2])
    rw [← Finset.card_biUnion (fun u1 _ u2 _ hne => hd u1 u2 hne)]
    congr 1; ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Au_at, Finset.mem_filter]
    exact ⟨fun ⟨_, hj, _⟩ => hj, fun hj => ⟨center j, hj, rfl⟩⟩
  have hSu_sum_ge : 52 ≤ ∑ u : Fin 26, (Su u).card := by
    let cov := Finset.univ.biUnion fun u : Fin 26 =>
      (Su u).image fun v => if u.val < 13 then (u, v) else (v, u)
    have hsub_e : edgePairs ⊆ cov := by
      intro e he
      obtain ⟨j, hjAu, hjcov⟩ := hedge_cover e he
      have hs := hcenter_spec j hjAu
      have he1 : e.1.val < 13 := (Finset.mem_filter.mp he).2.1
      have he2 : 13 ≤ e.2.val := (adj_diff_side e.1 e.2 (Finset.mem_filter.mp he).2.2).mp he1
      have hcw_eq : (e.1 ∈ orInW C (centerWire j) ∧ e.2 ∈ orInW C (leafWire j)) ∨
          (e.2 ∈ orInW C (centerWire j) ∧ e.1 ∈ orInW C (leafWire j)) := by
        by_cases h0 : (orInW C (opnd0 C j)).card = 1
        · simpa [centerWire, leafWire, h0] using hjcov
        · rcases hjcov with ⟨a, b⟩ | ⟨a, b⟩
          · exact Or.inr ⟨by simpa [centerWire, h0] using b, by simpa [leafWire, h0] using a⟩
          · exact Or.inl ⟨by simpa [centerWire, h0] using b, by simpa [leafWire, h0] using a⟩
      rw [hs.1, Finset.mem_singleton, Finset.mem_singleton] at hcw_eq
      rcases hcw_eq with ⟨hce, hle⟩ | ⟨hce, hle⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨center j, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.2, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjAu, rfl⟩, hle⟩
        · rw [← hce, ite_eq_left he1]
      · apply Finset.mem_biUnion.mpr
        refine ⟨center j, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.1, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjAu, rfl⟩, hle⟩
        · have hn : ¬ (center j).val < 13 := by rw [← hce]; omega
          rw [ite_eq_right hn, ← hce]
    have h1 : 52 ≤ cov.card := by rw [← edgePairs_card]; exact Finset.card_le_card hsub_e
    have h2 : cov.card ≤ ∑ u : Fin 26, (Su u).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun u _ => Finset.card_image_le)
    omega
  have h52_le : 52 ≤ Au.card + Op.card := by
    have h1 : (∑ u : Fin 26, (Su u).card) ≤ ∑ u : Fin 26, ((Au_at u).card + (Op_at u).card) :=
      Finset.sum_le_sum fun u _ => hOp_bound u
    rw [Finset.sum_add_distrib, hAu_sum] at h1
    omega
  have h13_le : 13 ≤ Au.card := by
    have h1 : (∑ u : Fin 26, (Su u).card) ≤ ∑ u : Fin 26, 4 * (Au_at u).card :=
      Finset.sum_le_sum fun u _ => hSu_le_4Au u
    rw [← Finset.mul_sum, hAu_sum] at h1
    omega
  -- Step 7: Out-degree count on B = Au ∪ As ∪ Ob:
  let R := As ∪ Ob ∪ Om
  let Slots : Finset (ℕ × Bool) :=
    (R ×ˢ ({false, true} : Finset Bool)).filter fun s =>
      let w := if s.2 then opnd1 C s.1 else opnd0 C s.1
      26 ≤ w ∧ w - 26 ∈ B
  have hslot_le : Slots.card ≤ 2 * As.card + 2 * Ob.card + Om.card := by
    have hd_As_Ob : Disjoint As Ob := Finset.disjoint_left.mpr fun j h1 h2 => by
      simp only [As, Ob, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; simp at h2
    have hd_AOb_Om : Disjoint (As ∪ Ob) Om := Finset.disjoint_left.mpr fun j h1 h2 => by
      simp only [As, Ob, Om, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with h1 | h1
      · rw [h1.2.1] at h2; simp at h2
      · rcases h2.2.2 with ⟨_, hne⟩ | ⟨hne, _⟩
        · exact Finset.nonempty_iff_ne_empty.mp hne h1.2.2.2
        · exact Finset.nonempty_iff_ne_empty.mp hne h1.2.2.1
    have hOm_slot (k : ℕ) (hk : k ∈ Om) :
        ((({false, true} : Finset Bool).filter fun b =>
          let w := if b then opnd1 C k else opnd0 C k
          26 ≤ w ∧ w - 26 ∈ B)).card ≤ 1 := by
      have hk' := (Finset.mem_filter.mp hk).2.2
      have hbad (w : ℕ) (hne : (orInW C w).Nonempty) : ¬ (26 ≤ w ∧ w - 26 ∈ B) := by
        rintro ⟨hge, hwB⟩
        have hem := (Finset.mem_filter.mp hwB).2
        rw [show 26 + (w - 26) = w by omega] at hem
        exact Finset.nonempty_iff_ne_empty.mp hne hem
      rcases hk' with ⟨_, hne1⟩ | ⟨hne0, _⟩
      · have hsub : (({false, true} : Finset Bool).filter fun b =>
            let w := if b then opnd1 C k else opnd0 C k
            26 ≤ w ∧ w - 26 ∈ B) ⊆ {false} := by
          intro b hb
          have hb' := (Finset.mem_filter.mp hb).2
          cases b
          · exact Finset.mem_singleton_self false
          · exact False.elim (hbad _ hne1 hb')
        exact (Finset.card_le_card hsub).trans (by simp)
      · have hsub : (({false, true} : Finset Bool).filter fun b =>
            let w := if b then opnd1 C k else opnd0 C k
            26 ≤ w ∧ w - 26 ∈ B) ⊆ {true} := by
          intro b hb
          have hb' := (Finset.mem_filter.mp hb).2
          cases b
          · exact False.elim (hbad _ hne0 hb')
          · exact Finset.mem_singleton_self true
        exact (Finset.card_le_card hsub).trans (by simp)
    let slotOf (k : ℕ) : Finset (ℕ × Bool) :=
      (({false, true} : Finset Bool).filter fun b =>
        let w := if b then opnd1 C k else opnd0 C k
        26 ≤ w ∧ w - 26 ∈ B).image (fun b => (k, b))
    have hslotOf_card (k : ℕ) : (slotOf k).card =
        (({false, true} : Finset Bool).filter fun b =>
          let w := if b then opnd1 C k else opnd0 C k
          26 ≤ w ∧ w - 26 ∈ B).card := by
      apply Finset.card_image_of_injective
      intro b1 b2 h; exact (Prod.mk.inj h).2
    have hsplit : Slots.card = ∑ k ∈ R,
        ((({false, true} : Finset Bool).filter fun b =>
          let w := if b then opnd1 C k else opnd0 C k
          26 ≤ w ∧ w - 26 ∈ B)).card := by
      have hbi : Slots = R.biUnion slotOf := by
        ext ⟨k, b⟩
        simp only [Slots, slotOf, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Finset.mem_image]
        constructor
        · rintro ⟨⟨hkR, hb⟩, hcond⟩
          exact ⟨k, hkR, b, ⟨hb, hcond⟩, rfl⟩
        · rintro ⟨k', hk', b', hb', heq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          exact ⟨⟨hk', hb'.1⟩, hb'.2⟩
      rw [hbi, Finset.card_biUnion]
      · exact Finset.sum_congr rfl fun k _ => hslotOf_card k
      · intro k1 _ k2 _ hne
        change Disjoint (slotOf k1) (slotOf k2)
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hp2
        exact hne (Prod.mk.inj heq).1.symm
    rw [hsplit]
    simp only [R]
    rw [Finset.sum_union hd_AOb_Om, Finset.sum_union hd_As_Ob]
    have h1 : (∑ k ∈ As, (({false, true} : Finset Bool).filter fun b =>
        let w := if b then opnd1 C k else opnd0 C k
        26 ≤ w ∧ w - 26 ∈ B).card) ≤ 2 * As.card := by
      calc _ ≤ ∑ _k ∈ As, 2 := Finset.sum_le_sum fun k _ => (Finset.card_filter_le _ _).trans (by decide)
        _ = As.card * 2 := by simp
        _ = 2 * As.card := Nat.mul_comm _ _
    have h2 : (∑ k ∈ Ob, (({false, true} : Finset Bool).filter fun b =>
        let w := if b then opnd1 C k else opnd0 C k
        26 ≤ w ∧ w - 26 ∈ B).card) ≤ 2 * Ob.card := by
      calc _ ≤ ∑ _k ∈ Ob, 2 := Finset.sum_le_sum fun k _ => (Finset.card_filter_le _ _).trans (by decide)
        _ = Ob.card * 2 := by simp
        _ = 2 * Ob.card := Nat.mul_comm _ _
    have h3 : (∑ k ∈ Om, (({false, true} : Finset Bool).filter fun b =>
        let w := if b then opnd1 C k else opnd0 C k
        26 ≤ w ∧ w - 26 ∈ B).card) ≤ Om.card := by
      calc _ ≤ ∑ _k ∈ Om, 1 := Finset.sum_le_sum fun k hk => hOm_slot k hk
        _ = Om.card := by simp
    exact Nat.add_le_add (Nat.add_le_add h1 h2) h3
  let slotTarget (s : ℕ × Bool) : ℕ := (if s.2 then opnd1 C s.1 else opnd0 C s.1) - 26
  have hslot_cov : B.erase root ⊆ Slots.image slotTarget := by
    intro j hj
    obtain ⟨hjne, hjB⟩ := Finset.mem_erase.mp hj
    have hjL := (Finset.mem_filter.mp hjB).1
    have hj_emp := (Finset.mem_filter.mp hjB).2
    obtain ⟨k, hkL, hread⟩ := liveOf_has_reader hAO root hroot_lt j hjL hjne
    have hklt := hLive_lt k hkL
    have hkR : k ∈ R := by
      have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq hklt]; exact List.getElem_mem hklt
      have hemp_read : orInW C (opnd0 C k) = ∅ ∨ orInW C (opnd1 C k) = ∅ := by
        rcases hread with h0 | h1
        · exact Or.inl (by rw [h0]; exact hj_emp)
        · exact Or.inr (by rw [h1]; exact hj_emp)
      simp only [R, Finset.mem_union]
      rcases hAO.1 _ hmem with hand | hor
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hkL, hand, hemp_read⟩))
      · by_cases h0 : orInW C (opnd0 C k) = ∅ <;> by_cases h1 : orInW C (opnd1 C k) = ∅
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hkL, hor, h0, h1⟩))
        · exact Or.inr (Finset.mem_filter.mpr ⟨hkL, hor, Or.inl ⟨h0, Finset.nonempty_iff_ne_empty.mpr h1⟩⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨hkL, hor, Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h0, h1⟩⟩)
        · exact False.elim (hemp_read.elim h0 h1)
    rcases hread with h0 | h1
    · refine Finset.mem_image.mpr ⟨(k, false), ?_, ?_⟩
      · simp only [Slots, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, true_or, Bool.false_eq_true, ite_false]
        refine ⟨⟨hkR, trivial⟩, by omega, by rwa [h0, Nat.add_sub_cancel_left]⟩
      · simp [slotTarget, h0]
    · refine Finset.mem_image.mpr ⟨(k, true), ?_, ?_⟩
      · simp only [Slots, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, or_true, ite_true]
        refine ⟨⟨hkR, trivial⟩, by omega, by rwa [h1, Nat.add_sub_cancel_left]⟩
      · simp [slotTarget, h1]
  have hB_erase_card : (B.erase root).card = B.card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hroot_live, hroot_empty⟩)
  have hslot_ge : B.card - 1 ≤ Slots.card := by
    rw [← hB_erase_card]
    exact (Finset.card_le_card hslot_cov).trans Finset.card_image_le
  -- Exact arithmetic pinch!
  have hAu_eq13 : Au.card = 13 := by omega
  have hOp_eq39 : Op.card = 39 := by omega
  have hLive_eq64 : Live.card = 64 := by omega
  have hR_sum12 : As.card + Ob.card + Om.card = 12 := by omega
  have hSlots_eq : Slots.card = B.card - 1 := by omega
  have hSlots_upper_eq : Slots.card = 2 * As.card + 2 * Ob.card + Om.card := by omega
  -- Exact equality consequences:
  -- 1. Live = Finset.range C.gates.length (every gate is live!)
  have hLive_all : ∀ j < C.gates.length, j ∈ Live := by
    have hlen64 : C.gates.length = 64 := by
      have h1 := Finset.card_le_card hLive_sub
      rw [Finset.card_range] at h1
      change C.gates.length ≤ 64 at hsize
      omega
    have heq : Live = Finset.range C.gates.length :=
      Finset.eq_of_subset_of_card_le hLive_sub (by rw [Finset.card_range]; omega)
    intro j hj; rw [heq]; exact Finset.mem_range.mpr hj
  -- 2. slotTarget is injective on Slots, and Slots.image slotTarget = B.erase root:
  have hslot_img_eq : Slots.image slotTarget = B.erase root :=
    (Finset.eq_of_subset_of_card_le hslot_cov (by rw [hB_erase_card, ← hSlots_eq]; exact Finset.card_image_le)).symm
  have hslot_inj : Set.InjOn slotTarget (Slots : Set (ℕ × Bool)) := by
    apply Finset.injOn_of_card_image_eq
    rw [hslot_img_eq, hB_erase_card, hSlots_eq]
  have hroot_not_slot : ∀ s ∈ Slots, slotTarget s ≠ root := by
    intro s hs heq
    have hmem : root ∈ B.erase root := by
      rw [← hslot_img_eq]; exact Finset.mem_image.mpr ⟨s, hs, heq⟩
    exact (Finset.mem_erase.mp hmem).1 rfl
  -- 3. Every k ∈ As ∪ Ob has BOTH operands in B!
  have hAsOb_both_B : ∀ k ∈ As ∪ Ob,
      26 ≤ opnd0 C k ∧ opnd0 C k - 26 ∈ B ∧ 26 ≤ opnd1 C k ∧ opnd1 C k - 26 ∈ B := by
    intro k hk
    by_contra hbad
    have hkR : k ∈ R := Finset.mem_union_left _ hk
    have hnot_both : ¬ ((k, false) ∈ Slots ∧ (k, true) ∈ Slots) := by
      rintro ⟨h0, h1⟩
      have h0' := (Finset.mem_filter.mp h0).2
      have h1' := (Finset.mem_filter.mp h1).2
      simp only [Bool.false_eq_true, ite_false, ite_true] at h0' h1'
      exact hbad ⟨h0'.1, h0'.2, h1'.1, h1'.2⟩
    -- If k misses a slot, Slots.card ≤ 2 * As.card + 2 * Ob.card + Om.card - 1, contradiction!
    have hlt_k : ((({false, true} : Finset Bool).filter fun b =>
        let w := if b then opnd1 C k else opnd0 C k
        26 ≤ w ∧ w - 26 ∈ B)).card < 2 := by
      by_contra hge; push Not at hge
      have heq : (({false, true} : Finset Bool).filter fun b =>
          let w := if b then opnd1 C k else opnd0 C k
          26 ≤ w ∧ w - 26 ∈ B) = {false, true} :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simp; omega)
      have hf : false ∈ ({false, true} : Finset Bool) := by simp
      have ht : true ∈ ({false, true} : Finset Bool) := by simp
      rw [← heq, Finset.mem_filter] at hf ht
      exact hnot_both ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hkR, hf.1⟩, hf.2⟩,
                       Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hkR, ht.1⟩, ht.2⟩⟩
    have hd_As_Ob : Disjoint As Ob := Finset.disjoint_left.mpr fun j h1 h2 => by
      simp only [As, Ob, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; simp at h2
    have hd_AOb_Om : Disjoint (As ∪ Ob) Om := Finset.disjoint_left.mpr fun j h1 h2 => by
      simp only [As, Ob, Om, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with h1 | h1
      · rw [h1.2.1] at h2; simp at h2
      · rcases h2.2.2 with ⟨_, hne⟩ | ⟨hne, _⟩
        · exact Finset.nonempty_iff_ne_empty.mp hne h1.2.2.2
        · exact Finset.nonempty_iff_ne_empty.mp hne h1.2.2.1
    let f (j : ℕ) := (({false, true} : Finset Bool).filter fun b =>
      let w := if b then opnd1 C j else opnd0 C j
      26 ≤ w ∧ w - 26 ∈ B).card
    let slotOf2 (j : ℕ) : Finset (ℕ × Bool) :=
      (({false, true} : Finset Bool).filter fun b =>
        let w := if b then opnd1 C j else opnd0 C j
        26 ≤ w ∧ w - 26 ∈ B).image (fun b => (j, b))
    have hsum_eq : Slots.card = ∑ j ∈ R, f j := by
      have hbi : Slots = R.biUnion slotOf2 := by
        ext ⟨j, b⟩
        simp only [Slots, slotOf2, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨⟨hjR, hb⟩, hc⟩; exact ⟨j, hjR, b, ⟨hb, hc⟩, rfl⟩
        · rintro ⟨j', hj', b', hb', heq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          exact ⟨⟨hj', hb'.1⟩, hb'.2⟩
      rw [hbi, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun j _ => ?_
        apply Finset.card_image_of_injective
        intro b1 b2 h; exact (Prod.mk.inj h).2
      · intro j1 _ j2 _ hne
        change Disjoint (slotOf2 j1) (slotOf2 j2)
        rw [Finset.disjoint_left]; intro p hp1 hp2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hp2
        exact hne (Prod.mk.inj heq).1.symm
    have hsum_lt : (∑ j ∈ As ∪ Ob, f j) < 2 * (As ∪ Ob).card := by
      calc ∑ j ∈ As ∪ Ob, f j
          < ∑ _j ∈ As ∪ Ob, 2 := Finset.sum_lt_sum (fun j _ => (Finset.card_filter_le _ _).trans (by decide)) ⟨k, hk, hlt_k⟩
        _ = (As ∪ Ob).card * 2 := by simp
        _ = 2 * (As ∪ Ob).card := Nat.mul_comm _ _
    have hsum_Om : (∑ j ∈ Om, f j) ≤ Om.card := by
      calc ∑ j ∈ Om, f j
          ≤ ∑ _j ∈ Om, 1 := Finset.sum_le_sum fun j hj => by
            have hj' := (Finset.mem_filter.mp hj).2.2
            have hbadw (w : ℕ) (hne : (orInW C w).Nonempty) : ¬ (26 ≤ w ∧ w - 26 ∈ B) := by
              rintro ⟨hge, hwB⟩
              have hem := (Finset.mem_filter.mp hwB).2
              rw [show 26 + (w - 26) = w by omega] at hem
              exact Finset.nonempty_iff_ne_empty.mp hne hem
            rcases hj' with ⟨_, hne1⟩ | ⟨hne0, _⟩
            · have hsub : (({false, true} : Finset Bool).filter fun b =>
                  26 ≤ (if b then opnd1 C j else opnd0 C j) ∧
                  (if b then opnd1 C j else opnd0 C j) - 26 ∈ B) ⊆ {false} := by
                intro b hb
                cases b
                · exact Finset.mem_singleton_self false
                · exact False.elim (hbadw _ hne1 (Finset.mem_filter.mp hb).2)
              exact (Finset.card_le_card hsub).trans (by simp)
            · have hsub : (({false, true} : Finset Bool).filter fun b =>
                  26 ≤ (if b then opnd1 C j else opnd0 C j) ∧
                  (if b then opnd1 C j else opnd0 C j) - 26 ∈ B) ⊆ {true} := by
                intro b hb
                cases b
                · exact False.elim (hbadw _ hne0 (Finset.mem_filter.mp hb).2)
                · exact Finset.mem_singleton_self true
              exact (Finset.card_le_card hsub).trans (by simp)
        _ = Om.card := by simp
    have htot : Slots.card < 2 * As.card + 2 * Ob.card + Om.card := by
      rw [hsum_eq]; simp only [R]; rw [Finset.sum_union hd_AOb_Om]
      rw [Finset.card_union_of_disjoint hd_As_Ob] at hsum_lt
      omega
    omega
  -- 4. Unique reader in R (and hence in B):
  have hmem_Slots : ∀ k ∈ R, ∀ b : Bool, ∀ g ∈ B,
      (if b then opnd1 C k else opnd0 C k) = 26 + g → (k, b) ∈ Slots := by
    intro k hkR b g hgB he
    simp only [Slots, Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨⟨hkR, by cases b <;> simp⟩, by omega, by rwa [he, Nat.add_sub_cancel_left]⟩
  have hroot_not_read : ∀ k ∈ R, opnd0 C k ≠ 26 + root ∧ opnd1 C k ≠ 26 + root := by
    intro k hkR
    have hrootB : root ∈ B := Finset.mem_filter.mpr ⟨hroot_live, hroot_empty⟩
    constructor
    · intro h0
      exact hroot_not_slot (k, false) (hmem_Slots k hkR false root hrootB h0) (by simp [slotTarget, h0])
    · intro h1
      exact hroot_not_slot (k, true) (hmem_Slots k hkR true root hrootB h1) (by simp [slotTarget, h1])
  have huniq_R : ∀ g ∈ B, ∀ k1 ∈ R, ∀ b1 : Bool, ∀ k2 ∈ R, ∀ b2 : Bool,
      (if b1 then opnd1 C k1 else opnd0 C k1) = 26 + g →
      (if b2 then opnd1 C k2 else opnd0 C k2) = 26 + g →
      k1 = k2 ∧ b1 = b2 := by
    intro g hgB k1 hk1 b1 k2 hk2 b2 he1 he2
    have hs1 := hmem_Slots k1 hk1 b1 g hgB he1
    have hs2 := hmem_Slots k2 hk2 b2 g hgB he2
    have hteq : slotTarget (k1, b1) = slotTarget (k2, b2) := by
      simp [slotTarget, he1, he2]
    exact Prod.mk.inj (hslot_inj hs1 hs2 hteq)
  have hB_ch : ∀ j ∈ B, j ∉ Au →
      26 ≤ opnd0 C j ∧ opnd0 C j - 26 ∈ B ∧ 26 ≤ opnd1 C j ∧ opnd1 C j - 26 ∈ B := by
    intro j hjB hnot
    have hj_in : j ∈ As ∪ Ob := by
      rw [hB_eq, Finset.mem_union] at hjB; exact hjB.resolve_left hnot
    exact hAsOb_both_B j hj_in
  have hB_lt : ∀ j ∈ B, j < C.gates.length := fun j hj => hLive_lt j (Finset.mem_filter.mp hj).1
  have huniq_B : ∀ g ∈ B, ∀ k1 ∈ B, ∀ k2 ∈ B,
      (opnd0 C k1 = 26 + g ∨ opnd1 C k1 = 26 + g) →
      (opnd0 C k2 = 26 + g ∨ opnd1 C k2 = 26 + g) → k1 = k2 := by
    intro g hgB k1 hk1 k2 hk2 hr1 hr2
    have hnotAu (k : ℕ) (hr : opnd0 C k = 26 + g ∨ opnd1 C k = 26 + g) : k ∉ Au := by
      intro hAu
      have hg_emp := (Finset.mem_filter.mp hgB).2
      rcases hr with h0 | h1
      · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [h0]; exact hg_emp)
      · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [h1]; exact hg_emp)
    have hk1R : k1 ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hk1)).resolve_left (hnotAu k1 hr1))
    have hk2R : k2 ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hk2)).resolve_left (hnotAu k2 hr2))
    rcases hr1 with h1 | h1 <;> rcases hr2 with h2 | h2
    · exact (huniq_R g hgB k1 hk1R false k2 hk2R false h1 h2).1
    · exact (huniq_R g hgB k1 hk1R false k2 hk2R true h1 h2).1
    · exact (huniq_R g hgB k1 hk1R true k2 hk2R false h1 h2).1
    · exact (huniq_R g hgB k1 hk1R true k2 hk2R true h1 h2).1
  -- Step 8: The 13 centers in Au are distinct, cover all 4 neighbors each, and all lie on the same side!
  have hSu_all_4 : ∀ u : Fin 26, (Su u).card = 4 * (Au_at u).card := by
    by_contra hnot
    push Not at hnot
    obtain ⟨u0, hu0⟩ := hnot
    have hlt0 : (Su u0).card < 4 * (Au_at u0).card := Nat.lt_of_le_of_ne (hSu_le_4Au u0) hu0
    have hsum_lt : (∑ u : Fin 26, (Su u).card) < ∑ u : Fin 26, 4 * (Au_at u).card :=
      Finset.sum_lt_sum (fun u _ => hSu_le_4Au u) ⟨u0, Finset.mem_univ _, hlt0⟩
    rw [← Finset.mul_sum, hAu_sum, hAu_eq13] at hsum_lt
    omega
  let U : Finset (Fin 26) := Au.image center
  have hcenter_inj : ∀ j1 ∈ Au, ∀ j2 ∈ Au, center j1 = center j2 → j1 = j2 := by
    intro j1 hj1 j2 hj2 heq
    by_contra hne
    have hge2 : 2 ≤ (Au_at (center j1)).card := by
      refine Finset.one_lt_card.mpr ⟨j1, Finset.mem_filter.mpr ⟨hj1, rfl⟩,
        j2, Finset.mem_filter.mpr ⟨hj2, heq.symm⟩, hne⟩
    have h4 := hSu_all_4 (center j1)
    have hle4 := hSu_card_le4 (center j1)
    omega
  have hU_card : U.card = 13 := by
    rw [Finset.card_image_of_injOn (fun a ha b hb h => hcenter_inj a ha b hb h), hAu_eq13]
  have hAu_full_nbrs : ∀ j ∈ Au, orInW C (leafWire j) = nbrs (center j) := by
    intro j hjAu
    have h1 : Au_at (center j) = {j} := by
      ext j'
      simp only [Au_at, Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨hj', heq⟩ => hcenter_inj j' hj' j hjAu heq, fun h => by subst h; exact ⟨hjAu, rfl⟩⟩
    have h4 : (orInW C (leafWire j)).card = 4 := by
      have := hSu_all_4 (center j)
      simpa [Su, h1] using this
    exact Finset.eq_of_subset_of_card_le (hcenter_spec j hjAu).2.2.1 (by rw [nbrs_card, h4])
  have hU_indep : ∀ u ∈ U, ∀ v ∈ U, adj u v = false := by
    intro u hu v hv
    by_contra hadj
    have hadj_t : adj u v = true := Bool.eq_true_of_not_eq_false hadj
    -- If u ~ v with u, v ∈ U, then edge (u, v) is counted TWICE in ∑ (Su w).card, so cov.card ≤ 51 < 52!
    let cov := Finset.univ.biUnion fun w : Fin 26 =>
      (Su w).image fun z => if w.val < 13 then (w, z) else (z, w)
    have hsub_e : edgePairs ⊆ cov := by
      intro e he
      obtain ⟨j, hjAu, hjcov⟩ := hedge_cover e he
      have hs := hcenter_spec j hjAu
      have he1 : e.1.val < 13 := (Finset.mem_filter.mp he).2.1
      have he2 : 13 ≤ e.2.val := (adj_diff_side e.1 e.2 (Finset.mem_filter.mp he).2.2).mp he1
      have hcw_eq : (e.1 ∈ orInW C (centerWire j) ∧ e.2 ∈ orInW C (leafWire j)) ∨
          (e.2 ∈ orInW C (centerWire j) ∧ e.1 ∈ orInW C (leafWire j)) := by
        by_cases h0 : (orInW C (opnd0 C j)).card = 1
        · simpa [centerWire, leafWire, h0] using hjcov
        · rcases hjcov with ⟨a, b⟩ | ⟨a, b⟩
          · exact Or.inr ⟨by simpa [centerWire, h0] using b, by simpa [leafWire, h0] using a⟩
          · exact Or.inl ⟨by simpa [centerWire, h0] using b, by simpa [leafWire, h0] using a⟩
      rw [hs.1, Finset.mem_singleton, Finset.mem_singleton] at hcw_eq
      rcases hcw_eq with ⟨hce, hle⟩ | ⟨hce, hle⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨center j, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.2, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjAu, rfl⟩, hle⟩
        · rw [← hce, ite_eq_left he1]
      · apply Finset.mem_biUnion.mpr
        refine ⟨center j, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.1, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjAu, rfl⟩, hle⟩
        · have hn : ¬ (center j).val < 13 := by rw [← hce]; omega
          rw [ite_eq_right hn, ← hce]
    have hcov52 : 52 ≤ cov.card := by rw [← edgePairs_card]; exact Finset.card_le_card hsub_e
    obtain ⟨ju, hju, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨jv, hjv, rfl⟩ := Finset.mem_image.mp hv
    have huv_ne : center ju ≠ center jv := by
      intro e; rw [e, adj_irrefl] at hadj_t; exact Bool.false_ne_true hadj_t
    let F (w : Fin 26) := (Su w).image fun z => if w.val < 13 then (w, z) else (z, w)
    have hF_le (w : Fin 26) : (F w).card ≤ (Su w).card := Finset.card_image_le
    have hshared : (F (center ju) ∩ F (center jv)).Nonempty := by
      have hv_in : center jv ∈ Su (center ju) := by
        apply Finset.mem_biUnion.mpr
        refine ⟨ju, Finset.mem_filter.mpr ⟨hju, rfl⟩, ?_⟩
        rw [hAu_full_nbrs ju hju]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_t⟩
      have hu_in : center ju ∈ Su (center jv) := by
        apply Finset.mem_biUnion.mpr
        refine ⟨jv, Finset.mem_filter.mpr ⟨hjv, rfl⟩, ?_⟩
        rw [hAu_full_nbrs jv hjv]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [adj_symm]; exact hadj_t⟩
      by_cases hlt : (center ju).val < 13
      · have hge : 13 ≤ (center jv).val := (adj_diff_side _ _ hadj_t).mp hlt
        refine ⟨(center ju, center jv), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_image.mpr ⟨center jv, hv_in, by simp [hlt]⟩
        · exact Finset.mem_image.mpr ⟨center ju, hu_in, by simp [show ¬ (center jv).val < 13 by omega]⟩
      · have hltv : (center jv).val < 13 := (adj_diff_side _ _ (by rw [adj_symm]; exact hadj_t)).mpr (by omega)
        refine ⟨(center jv, center ju), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_image.mpr ⟨center jv, hv_in, by simp [hlt]⟩
        · exact Finset.mem_image.mpr ⟨center ju, hu_in, by simp [hltv]⟩
    have hlt_pair : (F (center ju) ∪ F (center jv)).card < (F (center ju)).card + (F (center jv)).card := by
      have h1 := Finset.card_union_add_card_inter (F (center ju)) (F (center jv))
      have h2 := Finset.card_pos.mpr hshared
      omega
    let rest := (Finset.univ.erase (center ju)).erase (center jv)
    have huniv_eq : (Finset.univ : Finset (Fin 26)) = insert (center ju) (insert (center jv) rest) := by
      ext w; simp only [rest, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase, true_iff]
      by_cases h1 : w = center ju
      · exact Or.inl h1
      · by_cases h2 : w = center jv
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨h2, h1, trivial⟩)
    have hcov_lt : cov.card < ∑ w : Fin 26, (Su w).card := by
      have hcov_eq : cov = (F (center ju) ∪ F (center jv)) ∪ rest.biUnion F := by
        change Finset.univ.biUnion F = _
        rw [huniv_eq, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
      have hsum_eq : (∑ w : Fin 26, (Su w).card) =
          (Su (center ju)).card + (Su (center jv)).card + ∑ w ∈ rest, (Su w).card := by
        conv_lhs => rw [huniv_eq]
        rw [Finset.sum_insert (by simp [rest, huv_ne]), Finset.sum_insert (by simp [rest])]
        omega
      have hc1 : cov.card ≤ (F (center ju) ∪ F (center jv)).card + (rest.biUnion F).card := by
        rw [hcov_eq]; exact Finset.card_union_le _ _
      have hc2 : (rest.biUnion F).card ≤ ∑ w ∈ rest, (Su w).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ => hF_le w)
      have hfu := hF_le (center ju)
      have hfv := hF_le (center jv)
      omega
    have hsum52 : (∑ w : Fin 26, (Su w).card) = 52 := by
      calc ∑ w : Fin 26, (Su w).card = ∑ w : Fin 26, 4 * (Au_at w).card :=
            Finset.sum_congr rfl fun w _ => hSu_all_4 w
        _ = 4 * ∑ w : Fin 26, (Au_at w).card := (Finset.mul_sum ..).symm
        _ = 52 := by rw [hAu_sum, hAu_eq13]
    omega
  have hU_same_side : (∀ u ∈ U, u.val < 13) ∨ (∀ u ∈ U, 13 ≤ u.val) :=
    no_mixed_indep_13 U hU_card hU_indep
  -- Step 9: Prove Om = ∅ and As = ∅!
  have hOm_iff : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      (orInW C (26 + j)).Nonempty →
      (j ∈ Om ↔ (orInW C (opnd0 C j) = ∅ ∨ orInW C (opnd1 C j) = ∅)) := by
    intro j hjlt hor hne
    have hjL : j ∈ Live := hLive_all j hjlt
    rw [orInW_or hAO hjlt hor] at hne
    constructor
    · intro hOm
      rcases (Finset.mem_filter.mp hOm).2.2 with ⟨h0, _⟩ | ⟨_, h1⟩
      · exact Or.inl h0
      · exact Or.inr h1
    · intro hem
      apply Finset.mem_filter.mpr
      refine ⟨hjL, hor, ?_⟩
      rcases hem with h0 | h1
      · rw [h0, Finset.empty_union] at hne; exact Or.inl ⟨h0, hne⟩
      · rw [h1, Finset.union_empty] at hne; exact Or.inr ⟨hne, h1⟩
  have hOm_child : ∀ h ∈ Om, ∃ c ∈ B, c < h ∧ (opnd0 C h = 26 + c ∨ opnd1 C h = 26 + c) := by
    intro h hh
    have hL := (Finset.mem_filter.mp hh).1
    have hjlt := hLive_lt h hL
    have ⟨h0lt, h1lt⟩ := opnd_lt hAO hjlt
    have hcl := liveOf_closed hAO hroot_lt h hL
    rcases (Finset.mem_filter.mp hh).2.2 with ⟨he0, _⟩ | ⟨_, he1⟩
    · have hge : 26 ≤ opnd0 C h := by
        by_contra hlt; push Not at hlt; rw [orInW_input C _ hlt] at he0
        exact Finset.singleton_ne_empty _ he0
      refine ⟨opnd0 C h - 26, Finset.mem_filter.mpr ⟨hcl.1 hge, by rwa [show 26 + (opnd0 C h - 26) = opnd0 C h by omega]⟩,
        by omega, Or.inl (by omega)⟩
    · have hge : 26 ≤ opnd1 C h := by
        by_contra hlt; push Not at hlt; rw [orInW_input C _ hlt] at he1
        exact Finset.singleton_ne_empty _ he1
      refine ⟨opnd1 C h - 26, Finset.mem_filter.mpr ⟨hcl.2 hge, by rwa [show 26 + (opnd1 C h - 26) = opnd1 C h by omega]⟩,
        by omega, Or.inr (by omega)⟩
  -- Key disjointness of bCones for children of Om and root:
  have hOm_disj_root : ∀ h ∈ Om, ∀ c ∈ B, (opnd0 C h = 26 + c ∨ opnd1 C h = 26 + c) →
      ∀ g ∈ Au, g ∈ bCone C Au c → g ∉ bCone C Au root := by
    intro h hhOm c hcB hread g hgAu hgc hgr
    have hrootB : root ∈ B := Finset.mem_filter.mpr ⟨hroot_live, hroot_empty⟩
    have hc_ne_root : c ≠ root := by
      intro heq; subst heq
      have hhR : h ∈ R := Finset.mem_union_right _ hhOm
      exact hread.elim (hroot_not_read h hhR).1 (hroot_not_read h hhR).2
    have hord := bCone_tree_order hAO Au B hB_lt hB_ch huniq_B (c + root) c hcB root hrootB le_rfl g hgAu hgc hgr
    rcases hord with hcr | hrc
    · obtain ⟨k, hkB, _, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch root hrootB c hcr hc_ne_root
      have hk_not_Au : k ∉ Au := by
        intro hAu; have hc_emp := (Finset.mem_filter.mp hcB).2
        rcases hkread with h0 | h1
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [h0]; exact hc_emp)
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [h1]; exact hc_emp)
      have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
      have hhR : h ∈ R := Finset.mem_union_right _ hhOm
      have hkh : k = h := by
        rcases hkread with h1 | h1 <;> rcases hread with h2 | h2
        · exact (huniq_R c hcB k hkR false h hhR false h1 h2).1
        · exact (huniq_R c hcB k hkR false h hhR true h1 h2).1
        · exact (huniq_R c hcB k hkR true h hhR false h1 h2).1
        · exact (huniq_R c hcB k hkR true h hhR true h1 h2).1
      subst hkh
      have hOm_ne : (orInW C (26 + k)).Nonempty := by
        rw [orInW_or hAO (hB_lt k hkB) (Finset.mem_filter.mp hhOm).2.1]
        rcases (Finset.mem_filter.mp hhOm).2.2 with ⟨_, hne⟩ | ⟨hne, _⟩
        · exact hne.mono Finset.subset_union_right
        · exact hne.mono Finset.subset_union_left
      exact Finset.nonempty_iff_ne_empty.mp hOm_ne (Finset.mem_filter.mp hkB).2
    · obtain ⟨k, hkB, _, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch c hcB root hrc hc_ne_root.symm
      have hk_not_Au : k ∉ Au := by
        intro hAu
        rcases hkread with h0 | h1
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [h0]; exact hroot_empty)
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [h1]; exact hroot_empty)
      have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
      exact hkread.elim (hroot_not_read k hkR).1 (hroot_not_read k hkR).2
  have hOm_disj_Om : ∀ h1 ∈ Om, ∀ c1 ∈ B, (opnd0 C h1 = 26 + c1 ∨ opnd1 C h1 = 26 + c1) →
      ∀ h2 ∈ Om, ∀ c2 ∈ B, (opnd0 C h2 = 26 + c2 ∨ opnd1 C h2 = 26 + c2) →
      ∀ g ∈ Au, g ∈ bCone C Au c1 → g ∈ bCone C Au c2 → h1 = h2 := by
    intro h1 hh1 c1 hc1 hr1 h2 hh2 c2 hc2 hr2 g hgAu hg1 hg2
    by_cases hce : c1 = c2
    · subst hce
      have h1R : h1 ∈ R := Finset.mem_union_right _ hh1
      have h2R : h2 ∈ R := Finset.mem_union_right _ hh2
      rcases hr1 with a | a <;> rcases hr2 with b | b
      · exact (huniq_R c1 hc1 h1 h1R false h2 h2R false a b).1
      · exact (huniq_R c1 hc1 h1 h1R false h2 h2R true a b).1
      · exact (huniq_R c1 hc1 h1 h1R true h2 h2R false a b).1
      · exact (huniq_R c1 hc1 h1 h1R true h2 h2R true a b).1
    · exfalso
      have hord := bCone_tree_order hAO Au B hB_lt hB_ch huniq_B (c1 + c2) c1 hc1 c2 hc2 le_rfl g hgAu hg1 hg2
      have hcontra : ∀ (h : ℕ) (hh : h ∈ Om) (ca cb : ℕ) (hca : ca ∈ B) (hcb : cb ∈ B),
          (opnd0 C h = 26 + ca ∨ opnd1 C h = 26 + ca) → ca ≠ cb → ca ∈ bCone C Au cb → False := by
        intro h hh ca cb hca hcb hrh hne hmem
        obtain ⟨k, hkB, _, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch cb hcb ca hmem hne
        have hk_not_Au : k ∉ Au := by
          intro hAu; have hemp := (Finset.mem_filter.mp hca).2
          rcases hkread with h0 | h1
          · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [h0]; exact hemp)
          · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [h1]; exact hemp)
        have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
        have hhR : h ∈ R := Finset.mem_union_right _ hh
        have hkh : k = h := by
          rcases hkread with a | a <;> rcases hrh with b | b
          · exact (huniq_R ca hca k hkR false h hhR false a b).1
          · exact (huniq_R ca hca k hkR false h hhR true a b).1
          · exact (huniq_R ca hca k hkR true h hhR false a b).1
          · exact (huniq_R ca hca k hkR true h hhR true a b).1
        subst hkh
        have hOm_ne : (orInW C (26 + k)).Nonempty := by
          rw [orInW_or hAO (hB_lt k hkB) (Finset.mem_filter.mp hh).2.1]
          rcases (Finset.mem_filter.mp hh).2.2 with ⟨_, hne'⟩ | ⟨hne', _⟩
          · exact hne'.mono Finset.subset_union_right
          · exact hne'.mono Finset.subset_union_left
        exact Finset.nonempty_iff_ne_empty.mp hOm_ne (Finset.mem_filter.mp hkB).2
      rcases hord with h12 | h21
      · exact hcontra h1 hh1 c1 c2 hc1 hc2 hr1 hce h12
      · exact hcontra h2 hh2 c2 c1 hc2 hc1 hr2 (Ne.symm hce) h21
  have hAs_disj_children : ∀ j ∈ As,
      ∀ g ∈ Au, ¬ (g ∈ bCone C Au (opnd0 C j - 26) ∧ g ∈ bCone C Au (opnd1 C j - 26)) := by
    intro j hjAs g hgAu ⟨hg0, hg1⟩
    have hjB : j ∈ B := by rw [hB_eq]; exact Finset.mem_union_right _ (Finset.mem_union_left _ hjAs)
    have hjlt := hB_lt j hjB
    have ⟨h0ge, hc0B, h1ge, hc1B⟩ := hAsOb_both_B j (Finset.mem_union_left _ hjAs)
    have hnd : opnd0 C j ≠ opnd1 C j := by
      have hin := inputs_eq_pair hAO hjlt
      have hget : C.gates[j]? = some (gateAt C j) := by
        rw [gateAt_eq hjlt, List.getElem?_eq_getElem hjlt]
      have hnd' := hnodup j (gateAt C j) hget
      rw [hin] at hnd'; simpa using hnd'
    have hc_ne : opnd0 C j - 26 ≠ opnd1 C j - 26 := by omega
    have hord := bCone_tree_order hAO Au B hB_lt hB_ch huniq_B
      ((opnd0 C j - 26) + (opnd1 C j - 26)) (opnd0 C j - 26) hc0B (opnd1 C j - 26) hc1B le_rfl g hgAu hg0 hg1
    have ⟨h0lt, h1lt⟩ := opnd_lt hAO hjlt
    have hjR : j ∈ R := Finset.mem_union_left _ (Finset.mem_union_left _ hjAs)
    rcases hord with h01 | h10
    · obtain ⟨k, hkB, hkle, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch _ hc1B _ h01 hc_ne
      have hk_not_Au : k ∉ Au := by
        intro hAu; have hemp := (Finset.mem_filter.mp hc0B).2
        rcases hkread with a | a
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [a]; exact hemp)
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [a]; exact hemp)
      have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
      have hkj : k = j := by
        rcases hkread with a | a
        · exact (huniq_R _ hc0B k hkR false j hjR false a (show opnd0 C j = 26 + (opnd0 C j - 26) by omega)).1
        · exact (huniq_R _ hc0B k hkR true j hjR false a (show opnd0 C j = 26 + (opnd0 C j - 26) by omega)).1
      omega
    · obtain ⟨k, hkB, hkle, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch _ hc0B _ h10 hc_ne.symm
      have hk_not_Au : k ∉ Au := by
        intro hAu; have hemp := (Finset.mem_filter.mp hc1B).2
        rcases hkread with a | a
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [a]; exact hemp)
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [a]; exact hemp)
      have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
      have hkj : k = j := by
        rcases hkread with a | a
        · exact (huniq_R _ hc1B k hkR false j hjR true a (show opnd1 C j = 26 + (opnd1 C j - 26) by omega)).1
        · exact (huniq_R _ hc1B k hkR true j hjR true a (show opnd1 C j = 26 + (opnd1 C j - 26) by omega)).1
      omega
  -- Prove Om = ∅!
  have hOm_empty : Om = ∅ := by
    by_contra hne
    obtain ⟨h0, hh0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨c0, hc0B, _, hc0read⟩ := hOm_child h0 hh0
    obtain ⟨gu, hguAu, hgu_in⟩ := bCone_has_leaf hAO Au B hB_lt hB_ch c0 hc0B
    let u := center gu
    have huU : u ∈ U := Finset.mem_image.mpr ⟨gu, hguAu, rfl⟩
    have hv_clean : ∃ v ∈ nbrs u, ∀ u1 : Fin 26, orInW C (26 + h0) ⊆ {u1} → u1 ≠ u → v ∉ nbrs u1 := by
      by_cases hex : ∃ u1 : Fin 26, orInW C (26 + h0) ⊆ {u1} ∧ u1 ≠ u
      · obtain ⟨u1, hsub1, hu1ne⟩ := hex
        have hpos : 0 < (nbrs u \ nbrs u1).card := by
          have h1 : (nbrs u \ nbrs u1).card + (nbrs u ∩ nbrs u1).card = (nbrs u).card :=
            Finset.card_sdiff_add_card_inter _ _
          have h2 := no_four_cycle u u1 hu1ne.symm
          rw [nbrs_card u] at h1; omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        obtain ⟨hvu, hvnu1⟩ := Finset.mem_sdiff.mp hv
        refine ⟨v, hvu, fun u2 hsub2 hu2ne => ?_⟩
        have hne_h0 : (orInW C (26 + h0)).Nonempty := by
          rw [orInW_or hAO (hLive_lt h0 (Finset.mem_filter.mp hh0).1) (Finset.mem_filter.mp hh0).2.1]
          rcases (Finset.mem_filter.mp hh0).2.2 with ⟨_, hne'⟩ | ⟨hne', _⟩
          · exact hne'.mono Finset.subset_union_right
          · exact hne'.mono Finset.subset_union_left
        obtain ⟨w, hw⟩ := hne_h0
        have hw1 : w = u1 := Finset.mem_singleton.mp (hsub1 hw)
        have hw2 : w = u2 := Finset.mem_singleton.mp (hsub2 hw)
        rw [← hw2, hw1]; exact hvnu1
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [nbrs_card u]; omega : 0 < (nbrs u).card)
        exact ⟨v, hv, fun u1 hsub1 hu1ne => False.elim (hex ⟨u1, hsub1, hu1ne⟩)⟩
    obtain ⟨v, hvu, hv_avoid⟩ := hv_clean
    let x := pair u v
    have hkey : ∀ j ∈ B, wval C x (26 + j) = true → gu ∈ bCone C Au j := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hjB hjt
        have hjlt := hB_lt j hjB
        by_cases hjAu : j ∈ Au
        · by_cases heq : j = gu
          · subst heq; exact bCone_mem_self C Au j
          · exfalso
            have hcne : center j ≠ u := fun h => heq (hcenter_inj j hjAu gu hguAu h)
            have hjand := (Finset.mem_filter.mp hjAu).2.1
            rw [wval_and hAO x hjlt hjand, Bool.and_eq_true] at hjt
            have hs := hcenter_spec j hjAu
            have hcw_t : wval C x (centerWire j) = true := by
              by_cases h0c : (orInW C (opnd0 C j)).card = 1
              · simpa [centerWire, h0c] using hjt.1
              · simpa [centerWire, h0c] using hjt.2
            have hlw_t : wval C x (leafWire j) = true := by
              by_cases h0c : (orInW C (opnd0 C j)).card = 1
              · simpa [leafWire, h0c] using hjt.2
              · simpa [leafWire, h0c] using hjt.1
            have hcw_ne : (orInW C (centerWire j)).Nonempty := by rw [hs.1]; exact Finset.singleton_nonempty _
            have hdec := wval_above_decompose hAO Om hOm_iff (centerWire j) hs.2.2.2.2 hcw_ne x hcw_t
            rcases hdec with ⟨i, hi, hxi⟩ | ⟨h', hh', c', hc'lt, hc'op, hc'emp, hc't⟩
            · rw [hs.1, Finset.mem_singleton] at hi
              subst hi
              rcases of_decide_eq_true hxi with hcu | hcv
              · exact hcne hcu
              · have hadj_uv : adj u v = true := (Finset.mem_filter.mp hvu).2
                have hcjU : center j ∈ U := Finset.mem_image.mpr ⟨j, hjAu, rfl⟩
                rw [← hcv] at hadj_uv
                have hno := hU_indep u huU (center j) hcjU
                rw [hadj_uv] at hno; exact Bool.false_ne_true hno.symm
            · obtain ⟨hh'Om, hh'le, hh'sub⟩ := mixIn_subset_orInW hAO Om
                (fun h hh => ⟨hLive_lt h (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.1⟩)
                (centerWire j) hs.2.2.2.2 h' hh'
              have hc'ge : 26 ≤ c' := by
                by_contra hlt; push Not at hlt; rw [orInW_input C _ hlt] at hc'emp
                exact Finset.singleton_ne_empty _ hc'emp
              have hc'B : c' - 26 ∈ B := by
                have hcl := liveOf_closed hAO hroot_lt h' (Finset.mem_filter.mp hh'Om).1
                have hc'L : c' - 26 ∈ Live := hc'op.elim (fun e => e ▸ hcl.1 (e ▸ hc'ge)) (fun e => e ▸ hcl.2 (e ▸ hc'ge))
                exact Finset.mem_filter.mpr ⟨hc'L, by rwa [show 26 + (c' - 26) = c' by omega]⟩
              have hcw_lt_j : centerWire j < 26 + j := by
                have ⟨ha, hb⟩ := opnd_lt hAO hjlt
                by_cases h0c : (orInW C (opnd0 C j)).card = 1
                · simpa [centerWire, h0c] using ha
                · simpa [centerWire, h0c] using hb
              have hgu_c' : gu ∈ bCone C Au (c' - 26) :=
                ih (c' - 26) (by omega) hc'B (by rwa [show 26 + (c' - 26) = c' by omega])
              have hh'eq : h' = h0 := hOm_disj_Om h' hh'Om (c' - 26) hc'B
                (hc'op.elim (fun e => Or.inl (by omega)) (fun e => Or.inr (by omega)))
                h0 hh0 c0 hc0B hc0read gu hguAu hgu_c' hgu_in
              rw [hh'eq] at hh'sub
              rw [hs.1] at hh'sub
              have hv_not_nb : v ∉ nbrs (center j) := hv_avoid (center j) hh'sub hcne
              -- Now check leafWire j:
              have hdecL := wval_above_decompose hAO Om hOm_iff (leafWire j) hs.2.2.2.1 hs.2.1 x hlw_t
              rcases hdecL with ⟨i, hi, hxi⟩ | ⟨h'', hh'', c'', hc''lt, hc''op, hc''emp, hc''t⟩
              · rw [hAu_full_nbrs j hjAu] at hi
                rcases of_decide_eq_true hxi with rfl | rfl
                · have hadj_cu : adj (center j) u = true := (Finset.mem_filter.mp hi).2
                  have hcjU : center j ∈ U := Finset.mem_image.mpr ⟨j, hjAu, rfl⟩
                  have hno := hU_indep (center j) hcjU u huU
                  rw [hadj_cu] at hno; exact Bool.false_ne_true hno.symm
                · exact hv_not_nb hi
              · obtain ⟨hh''Om, hh''le, hh''sub⟩ := mixIn_subset_orInW hAO Om
                  (fun h hh => ⟨hLive_lt h (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.1⟩)
                  (leafWire j) hs.2.2.2.1 h'' hh''
                have hc''ge : 26 ≤ c'' := by
                  by_contra hlt; push Not at hlt; rw [orInW_input C _ hlt] at hc''emp
                  exact Finset.singleton_ne_empty _ hc''emp
                have hc''B : c'' - 26 ∈ B := by
                  have hcl := liveOf_closed hAO hroot_lt h'' (Finset.mem_filter.mp hh''Om).1
                  have hc''L : c'' - 26 ∈ Live := hc''op.elim (fun e => e ▸ hcl.1 (e ▸ hc''ge)) (fun e => e ▸ hcl.2 (e ▸ hc''ge))
                  exact Finset.mem_filter.mpr ⟨hc''L, by rwa [show 26 + (c'' - 26) = c'' by omega]⟩
                have hlw_lt_j : leafWire j < 26 + j := by
                  have ⟨ha, hb⟩ := opnd_lt hAO hjlt
                  by_cases h0c : (orInW C (opnd0 C j)).card = 1
                  · simpa [leafWire, h0c] using hb
                  · simpa [leafWire, h0c] using ha
                have hgu_c'' : gu ∈ bCone C Au (c'' - 26) :=
                  ih (c'' - 26) (by omega) hc''B (by rwa [show 26 + (c'' - 26) = c'' by omega])
                have hh''eq : h'' = h0 := hOm_disj_Om h'' hh''Om (c'' - 26) hc''B
                  (hc''op.elim (fun e => Or.inl (by omega)) (fun e => Or.inr (by omega)))
                  h0 hh0 c0 hc0B hc0read gu hguAu hgu_c'' hgu_in
                rw [hh''eq] at hh''sub
                have hne_h0 : (orInW C (26 + h0)).Nonempty := by
                  rw [orInW_or hAO (hLive_lt h0 (Finset.mem_filter.mp hh0).1) (Finset.mem_filter.mp hh0).2.1]
                  rcases (Finset.mem_filter.mp hh0).2.2 with ⟨_, hne'⟩ | ⟨hne', _⟩
                  · exact hne'.mono Finset.subset_union_right
                  · exact hne'.mono Finset.subset_union_left
                obtain ⟨w, hw⟩ := hne_h0
                have hw1 : w = center j := Finset.mem_singleton.mp (hh'sub hw)
                have hw2 : w ∈ nbrs (center j) := by
                  rw [← hAu_full_nbrs j hjAu]; exact hh''sub hw
                rw [hw1] at hw2
                have ha := (Finset.mem_filter.mp hw2).2
                rw [adj_irrefl] at ha; exact Bool.false_ne_true ha
        · have ⟨h0ge, hc0B', h1ge, hc1B'⟩ := hB_ch j hjB hjAu
          have ⟨h0lt, h1lt⟩ := opnd_lt hAO hjlt
          have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hjlt]; exact List.getElem_mem hjlt
          rcases hAO.1 _ hmem with hand | hor
          · rw [wval_and hAO x hjlt hand, Bool.and_eq_true] at hjt
            have hgu0 := ih (opnd0 C j - 26) (by omega) hc0B' (by rw [show 26 + (opnd0 C j - 26) = opnd0 C j by omega]; exact hjt.1)
            have hgu1 := ih (opnd1 C j - 26) (by omega) hc1B' (by rw [show 26 + (opnd1 C j - 26) = opnd1 C j by omega]; exact hjt.2)
            have hjAs : j ∈ As := by
              have h1 := (Finset.mem_union.mp (hB_eq ▸ hjB)).resolve_left hjAu
              rcases Finset.mem_union.mp h1 with h | h
              · exact h
              · exfalso; have := (Finset.mem_filter.mp h).2.1; rw [hand] at this; simp at this
            exact False.elim (hAs_disj_children j hjAs gu hguAu ⟨hgu0, hgu1⟩)
          · rw [wval_or hAO x hjlt hor, Bool.or_eq_true] at hjt
            rw [bCone_step hAO Au hjlt hjAu h0ge h1ge]
            rcases hjt with h0t | h1t
            · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (ih (opnd0 C j - 26) (by omega) hc0B' (by rwa [show 26 + (opnd0 C j - 26) = opnd0 C j by omega])))
            · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
                (ih (opnd1 C j - 26) (by omega) hc1B' (by rwa [show 26 + (opnd1 C j - 26) = opnd1 C j by omega])))
    have hroot_t : wval C x (26 + root) = true := by
      rw [hroot_eq]; exact (hfun x).mpr ((hit_pair u v).mpr (Finset.mem_filter.mp hvu).2)
    have hgu_root : gu ∈ bCone C Au root :=
      hkey root (Finset.mem_filter.mpr ⟨hroot_live, hroot_empty⟩) hroot_t
    exact hOm_disj_root h0 hh0 c0 hc0B hc0read gu hguAu hgu_in hgu_root
  -- Now prove As = ∅!
  have hAs_empty : As = ∅ := by
    by_contra hne
    obtain ⟨j0, hj0As⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have ⟨h0ge, hc0B, h1ge, hc1B⟩ := hAsOb_both_B j0 (Finset.mem_union_left _ hj0As)
    obtain ⟨gu, hguAu, hgu_in⟩ := bCone_has_leaf hAO Au B hB_lt hB_ch (opnd0 C j0 - 26) hc0B
    let u := center gu
    obtain ⟨v, hvu⟩ := Finset.card_pos.mp (by rw [nbrs_card u]; omega : 0 < (nbrs u).card)
    let x := pair u v
    -- With Om = ∅, every wire w with orInW C w ≠ ∅ satisfies wval C x w = true → ∃ i ∈ orInW C w, x i = true!
    have hpure_val : ∀ w < 26 + C.gates.length, (orInW C w).Nonempty →
        wval C x w = true → ∃ i ∈ orInW C w, x i = true := by
      intro w hwlt hnew hwt
      rcases wval_above_decompose hAO Om hOm_iff w hwlt hnew x hwt with h | ⟨h, hh, _⟩
      · exact h
      · exfalso
        have hhOm := (mixIn_subset_orInW hAO Om
          (fun h hh => ⟨hLive_lt h (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.1⟩) w hwlt h hh).1
        rw [hOm_empty] at hhOm; simp at hhOm
    -- By induction on j ∈ B, wval C x (26 + j) = true → j ≠ j0 ∧ gu ∈ bCone C Au j!
    have hkey2 : ∀ j ∈ B, wval C x (26 + j) = true → gu ∈ bCone C Au j ∧ j ∉ As := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hjB hjt
        have hjlt := hB_lt j hjB
        by_cases hjAu : j ∈ Au
        · by_cases heq : j = gu
          · subst heq
            refine ⟨bCone_mem_self C Au j, fun hjAs => ?_⟩
            rcases (Finset.mem_filter.mp hjAs).2.2 with h0 | h1
            · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hjAu).2.2.1 h0
            · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hjAu).2.2.2 h1
          · exfalso
            have hcne : center j ≠ u := fun h => heq (hcenter_inj j hjAu gu hguAu h)
            have hjand := (Finset.mem_filter.mp hjAu).2.1
            rw [wval_and hAO x hjlt hjand, Bool.and_eq_true] at hjt
            have hs := hcenter_spec j hjAu
            have hcw_t : wval C x (centerWire j) = true := by
              by_cases h0c : (orInW C (opnd0 C j)).card = 1
              · simpa [centerWire, h0c] using hjt.1
              · simpa [centerWire, h0c] using hjt.2
            obtain ⟨i, hi, hxi⟩ := hpure_val (centerWire j) hs.2.2.2.2 (by rw [hs.1]; exact Finset.singleton_nonempty _) hcw_t
            rw [hs.1, Finset.mem_singleton] at hi; subst hi
            rcases of_decide_eq_true hxi with hcu | hcv
            · exact hcne hcu
            · have hadj_uv : adj u v = true := (Finset.mem_filter.mp hvu).2
              have hcjU : center j ∈ U := Finset.mem_image.mpr ⟨j, hjAu, rfl⟩
              have huU : u ∈ U := Finset.mem_image.mpr ⟨gu, hguAu, rfl⟩
              rw [← hcv] at hadj_uv
              have hno := hU_indep u huU (center j) hcjU
              rw [hadj_uv] at hno; exact Bool.false_ne_true hno.symm
        · have ⟨h0ge', hc0B', h1ge', hc1B'⟩ := hB_ch j hjB hjAu
          have ⟨h0lt, h1lt⟩ := opnd_lt hAO hjlt
          have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hjlt]; exact List.getElem_mem hjlt
          rcases hAO.1 _ hmem with hand | hor
          · rw [wval_and hAO x hjlt hand, Bool.and_eq_true] at hjt
            have hgu0 := (ih (opnd0 C j - 26) (by omega) hc0B' (by rw [show 26 + (opnd0 C j - 26) = opnd0 C j by omega]; exact hjt.1)).1
            have hgu1 := (ih (opnd1 C j - 26) (by omega) hc1B' (by rw [show 26 + (opnd1 C j - 26) = opnd1 C j by omega]; exact hjt.2)).1
            have hjAs : j ∈ As := by
              have h1 := (Finset.mem_union.mp (hB_eq ▸ hjB)).resolve_left hjAu
              rcases Finset.mem_union.mp h1 with h | h
              · exact h
              · exfalso; have := (Finset.mem_filter.mp h).2.1; rw [hand] at this; simp at this
            exact False.elim (hAs_disj_children j hjAs gu hguAu ⟨hgu0, hgu1⟩)
          · rw [wval_or hAO x hjlt hor, Bool.or_eq_true] at hjt
            have hnotAs : j ∉ As := fun h => by
              have := (Finset.mem_filter.mp h).2.1; rw [hor] at this; simp at this
            rw [bCone_step hAO Au hjlt hjAu h0ge' h1ge']
            rcases hjt with h0t | h1t
            · exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _
                (ih (opnd0 C j - 26) (by omega) hc0B' (by rwa [show 26 + (opnd0 C j - 26) = opnd0 C j by omega])).1), hnotAs⟩
            · exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _
                (ih (opnd1 C j - 26) (by omega) hc1B' (by rwa [show 26 + (opnd1 C j - 26) = opnd1 C j by omega])).1), hnotAs⟩
    -- Even better: show wval C x (26 + j) = true → j0 ∉ bCone C Au j!
    have hkey3 : ∀ j ∈ B, wval C x (26 + j) = true → j0 ∉ bCone C Au j := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hjB hjt hj0mem
        have hjlt := hB_lt j hjB
        have hjnotAs := (hkey2 j hjB hjt).2
        by_cases hjAu : j ∈ Au
        · rw [bCone_au C Au hjAu, Finset.mem_singleton] at hj0mem
          subst hj0mem
          exact hjnotAs hj0As
        · have hjne : j ≠ j0 := fun e => hjnotAs (e ▸ hj0As)
          have ⟨h0ge', hc0B', h1ge', hc1B'⟩ := hB_ch j hjB hjAu
          have ⟨h0lt, h1lt⟩ := opnd_lt hAO hjlt
          have hmem : gateAt C j ∈ C.gates := by rw [gateAt_eq hjlt]; exact List.getElem_mem hjlt
          rcases hAO.1 _ hmem with hand | hor
          · exact hjnotAs (by
              have h1 := (Finset.mem_union.mp (hB_eq ▸ hjB)).resolve_left hjAu
              rcases Finset.mem_union.mp h1 with h | h
              · exact h
              · exfalso; have := (Finset.mem_filter.mp h).2.1; rw [hand] at this; simp at this)
          · rw [bCone_step hAO Au hjlt hjAu h0ge' h1ge'] at hj0mem
            have hj0' := (Finset.mem_insert.mp hj0mem).resolve_left hjne.symm
            rw [wval_or hAO x hjlt hor, Bool.or_eq_true] at hjt
            have hgu_j0 : gu ∈ bCone C Au j0 := by
              have hj0B : j0 ∈ B := by rw [hB_eq]; exact Finset.mem_union_right _ (Finset.mem_union_left _ hj0As)
              have hj0notAu : j0 ∉ Au := fun hAu => by
                rcases (Finset.mem_filter.mp hj0As).2.2 with h0 | h1
                · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 h0
                · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 h1
              rw [bCone_step hAO Au (hB_lt j0 hj0B) hj0notAu h0ge h1ge]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hgu_in)
            -- Wait: bCone is transitive! Actually we just need: whichever child of j is true contains gu, and whichever contains j0 ALSO contains gu!
            have hcone_trans : ∀ a ∈ B, ∀ b ∈ B, a ∈ bCone C Au b → ∀ g ∈ bCone C Au a, g ∈ bCone C Au b := by
              intro a ha b
              induction b using Nat.strong_induction_on with
              | ind b ihb =>
                intro hb hab g hga
                by_cases hba : b ∈ Au
                · rw [bCone_au C Au hba, Finset.mem_singleton] at hab
                  subst hab; exact hga
                · have ⟨hb0, hcb0, hb1, hcb1⟩ := hB_ch b hb hba
                  have ⟨hbl0, hbl1⟩ := opnd_lt hAO (hB_lt b hb)
                  rw [bCone_step hAO Au (hB_lt b hb) hba hb0 hb1] at hab
                  rcases Finset.mem_insert.mp hab with rfl | hab'
                  · exact hga
                  · rw [bCone_step hAO Au (hB_lt b hb) hba hb0 hb1]
                    rcases Finset.mem_union.mp hab' with ha0 | ha1
                    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihb _ (by omega) hcb0 ha0 g hga))
                    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihb _ (by omega) hcb1 ha1 g hga))
            have hdisj_Ob : ∀ g ∈ Au, ¬ (g ∈ bCone C Au (opnd0 C j - 26) ∧ g ∈ bCone C Au (opnd1 C j - 26)) := by
              intro g hgAu ⟨hg0, hg1⟩
              have hnd : opnd0 C j ≠ opnd1 C j := by
                have hin := inputs_eq_pair hAO hjlt
                have hget : C.gates[j]? = some (gateAt C j) := by
                  rw [gateAt_eq hjlt, List.getElem?_eq_getElem hjlt]
                have hnd' := hnodup j (gateAt C j) hget
                rw [hin] at hnd'; simpa using hnd'
              have hc_ne : opnd0 C j - 26 ≠ opnd1 C j - 26 := by omega
              have hord := bCone_tree_order hAO Au B hB_lt hB_ch huniq_B
                ((opnd0 C j - 26) + (opnd1 C j - 26)) (opnd0 C j - 26) hc0B' (opnd1 C j - 26) hc1B' le_rfl g hgAu hg0 hg1
              have hjR : j ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hjB)).resolve_left hjAu)
              rcases hord with h01 | h10
              · obtain ⟨k, hkB, hkle, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch _ hc1B' _ h01 hc_ne
                have hk_not_Au : k ∉ Au := by
                  intro hAu; have hemp := (Finset.mem_filter.mp hc0B').2
                  rcases hkread with a | a
                  · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [a]; exact hemp)
                  · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [a]; exact hemp)
                have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
                have hkj : k = j := by
                  rcases hkread with a | a
                  · exact (huniq_R _ hc0B' k hkR false j hjR false a (show opnd0 C j = 26 + (opnd0 C j - 26) by omega)).1
                  · exact (huniq_R _ hc0B' k hkR true j hjR false a (show opnd0 C j = 26 + (opnd0 C j - 26) by omega)).1
                omega
              · obtain ⟨k, hkB, hkle, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch _ hc0B' _ h10 hc_ne.symm
                have hk_not_Au : k ∉ Au := by
                  intro hAu; have hemp := (Finset.mem_filter.mp hc1B').2
                  rcases hkread with a | a
                  · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [a]; exact hemp)
                  · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [a]; exact hemp)
                have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
                have hkj : k = j := by
                  rcases hkread with a | a
                  · exact (huniq_R _ hc1B' k hkR false j hjR true a (show opnd1 C j = 26 + (opnd1 C j - 26) by omega)).1
                  · exact (huniq_R _ hc1B' k hkR true j hjR true a (show opnd1 C j = 26 + (opnd1 C j - 26) by omega)).1
                omega
            have hj0B : j0 ∈ B := by rw [hB_eq]; exact Finset.mem_union_right _ (Finset.mem_union_left _ hj0As)
            rcases Finset.mem_union.mp hj0' with hj0_0 | hj0_1 <;> rcases hjt with h0t | h1t
            · exact ih (opnd0 C j - 26) (by omega) hc0B' (by rwa [show 26 + (opnd0 C j - 26) = opnd0 C j by omega]) hj0_0
            · have hgu1 := (hkey2 (opnd1 C j - 26) hc1B' (by rwa [show 26 + (opnd1 C j - 26) = opnd1 C j by omega])).1
              have hgu0 := hcone_trans j0 hj0B (opnd0 C j - 26) hc0B' hj0_0 gu hgu_j0
              exact hdisj_Ob gu hguAu ⟨hgu0, hgu1⟩
            · have hgu0 := (hkey2 (opnd0 C j - 26) hc0B' (by rwa [show 26 + (opnd0 C j - 26) = opnd0 C j by omega])).1
              have hgu1 := hcone_trans j0 hj0B (opnd1 C j - 26) hc1B' hj0_1 gu hgu_j0
              exact hdisj_Ob gu hguAu ⟨hgu0, hgu1⟩
            · exact ih (opnd1 C j - 26) (by omega) hc1B' (by rwa [show 26 + (opnd1 C j - 26) = opnd1 C j by omega]) hj0_1
    have hroot_t : wval C x (26 + root) = true := by
      rw [hroot_eq]; exact (hfun x).mpr ((hit_pair u v).mpr (Finset.mem_filter.mp hvu).2)
    have hrootB : root ∈ B := Finset.mem_filter.mpr ⟨hroot_live, hroot_empty⟩
    have hgu_root := (hkey2 root hrootB hroot_t).1
    have hj0B : j0 ∈ B := by rw [hB_eq]; exact Finset.mem_union_right _ (Finset.mem_union_left _ hj0As)
    have hgu_j0 : gu ∈ bCone C Au j0 := by
      have hj0notAu : j0 ∉ Au := fun hAu => by
        rcases (Finset.mem_filter.mp hj0As).2.2 with h0 | h1
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 h0
        · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 h1
      rw [bCone_step hAO Au (hB_lt j0 hj0B) hj0notAu h0ge h1ge]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hgu_in)
    have hord := bCone_tree_order hAO Au B hB_lt hB_ch huniq_B (j0 + root) j0 hj0B root hrootB le_rfl gu hguAu hgu_j0 hgu_root
    have hj0_in_root : j0 ∈ bCone C Au root := by
      rcases hord with h1 | h2
      · exact h1
      · by_cases heq : j0 = root
        · exact heq ▸ bCone_mem_self C Au root
        · exfalso
          obtain ⟨k, hkB, _, hkread⟩ := bCone_has_reader hAO Au B hB_lt hB_ch j0 hj0B root h2 (Ne.symm heq)
          have hk_not_Au : k ∉ Au := by
            intro hAu
            rcases hkread with a | a
            · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.1 (by rw [a]; exact hroot_empty)
            · exact Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hAu).2.2.2 (by rw [a]; exact hroot_empty)
          have hkR : k ∈ R := Finset.mem_union_left _ ((Finset.mem_union.mp (hB_eq ▸ hkB)).resolve_left hk_not_Au)
          exact hkread.elim (hroot_not_read k hkR).1 (hroot_not_read k hkR).2
    exact hkey3 root hrootB hroot_t hj0_in_root
  -- Step 10: Conclude the main theorem!
  intro P L k a b hgate htrue
  have hklt : k < C.gates.length := (List.getElem?_eq_some_iff.mp hgate).1
  have hgat : gateAt C k = ⟨GateOp.and, [a, b]⟩ := by
    change C.gates.getD k ⟨GateOp.or, []⟩ = _
    simp [List.getD_eq_getElem?_getD, hgate]
  have hop : (gateAt C k).op = GateOp.and := by rw [hgat]
  have ha_eq : opnd0 C k = a := by simp [opnd0, hgat]
  have hb_eq : opnd1 C k = b := by simp [opnd1, hgat]
  have hkL : k ∈ Live := hLive_all k hklt
  have hkAu : k ∈ Au := by
    by_contra hnot
    have hkAs : k ∈ As := by
      apply Finset.mem_filter.mpr
      refine ⟨hkL, hop, ?_⟩
      by_contra hboth; push Not at hboth
      exact hnot (Finset.mem_filter.mpr ⟨hkL, hop, hboth.1, hboth.2⟩)
    rw [hAs_empty] at hkAs; simp at hkAs
  have ⟨ha_lt, _⟩ := opnd_lt hAO hklt
  rw [wval_and hAO (pair P L) hklt hop, ha_eq, hb_eq, Bool.and_eq_true] at htrue
  have ha_ne : (orInW C a).Nonempty := ha_eq ▸ (Finset.mem_filter.mp hkAu).2.2.1
  have hdec := wval_above_decompose hAO Om hOm_iff a (by omega) ha_ne (pair P L) htrue.1
  rcases hdec with ⟨i, hi, hxi⟩ | ⟨h, hh, _⟩
  · rcases of_decide_eq_true hxi with rfl | rfl
    · left
      rw [Bool.or_eq_true]
      exact Or.inl (wval_of_mem_orInW hAO a P hi)
    · right
      rw [Bool.or_eq_true]
      exact Or.inl (wval_of_mem_orInW hAO a L hi)
  · exfalso
    have hhOm := (mixIn_subset_orInW hAO Om
      (fun h hh => ⟨hLive_lt h (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.1⟩) a (by omega) h hh).1
    rw [hOm_empty] at hhOm; simp at hhOm

end PEqualNP.Outside.L_meta_4103_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4103_aux

theorem PEqualNP.Outside.L_meta_4103 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1;   have x3 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : ℕ) => (x1.wires (List.ofFn x3)).getD x4 Bool.false;   have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => x4 - x5 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))];   x1.size ≤ (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ x7 ∈ x1.gates, x7.inputs.Nodup) →         (∀ (x8 : Fin (26 : ℕ) → Bool), x3 x8 x1.output = Bool.true ↔ ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x4 x9 x10 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) →           (∀ (x9 : ℕ), (x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin (26 : ℕ) → Bool), x3 x11 ((26 : ℕ) + x9) = Bool.true → x3 x11 x1.output = Bool.true) →             ∀ (x10 x11 : Fin (13 : ℕ)) (x12 x13 x14 x15 x16 : ℕ),               have x17 : Fin (26 : ℕ) → Bool := fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = Fin.castAdd (13 : ℕ) x10 ∨ x17 = Fin.natAdd (13 : ℕ) x11);               have x18 : ℕ → ℕ → Prop := fun (x18 x19 : ℕ) => (x2 x18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3 x17 ((26 : ℕ) + x18) = Bool.true ∧ Relation.ReflTransGen (fun (x20 x21 : ℕ) => ∃ (x22 : ℕ), x21 = (26 : ℕ) + x22 ∧ (x2 x22).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x20 ∈ (x2 x22).inputs) ((26 : ℕ) + x18) x19;               x4 x10 x11 → x2 x12 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x13, x14] : PEqualNP.CircuitLowerBounds.Gate } → x3 x17 ((26 : ℕ) + x12) = Bool.true → (∀ (x22 : Fin (26 : ℕ)), x17 x22 = Bool.true → (x3 (fun (x24 : Fin (26 : ℕ)) => Decidable.decide (x24 = x22)) x13 || x3 (fun (x24 : Fin (26 : ℕ)) => Decidable.decide (x24 = x22)) x14) = Bool.false) → x18 x15 x13 → x18 x16 x14 → x15 ≠ x16 → False := by
  dsimp only
  intro C hsize hAO hnodup hfun hclean p l j a b _ _ hinc hgate htrue hnone _ _ _
  have hn (k : Nat) (g : Gate) (hg : C.gates[k]? = some g) : g.inputs.Nodup :=
    hnodup g (List.mem_of_getElem? hg)
  have hhit (x : Fin 26 → Bool) : wval C x C.output = true ↔ hit x := by
    simpa only [wval, hit, E, List.mem_cons, List.not_mem_nil, or_false] using hfun x
  have hE : E p l := by
    simpa only [E, List.mem_cons, List.not_mem_nil, or_false] using hinc
  have hget : C.gates[j]? = some ⟨.and, [a, b]⟩ := by
    cases he : C.gates[j]? with
    | none =>
        have hop : (gateAt C j).op = GateOp.or := by
          simp [gateAt, List.getD_eq_getElem?_getD, he]
        rw [hgate] at hop
        cases hop
    | some g =>
        have hh : g = ⟨.and, [a, b]⟩ := by
          simpa [gateAt, List.getD_eq_getElem?_getD, he] using hgate
        rw [hh]
  have hsingleton := main_proof C hsize hAO hn hhit hclean p l hE j a b hget htrue
  rcases hsingleton with hp | hl
  · have hp0 := hnone (Fin.castAdd 13 p) (decide_eq_true (Or.inl rfl))
    exact Bool.false_ne_true (hp0.symm.trans hp)
  · have hl0 := hnone (Fin.natAdd 13 l) (decide_eq_true (Or.inr rfl))
    exact Bool.false_ne_true (hl0.symm.trans hl)
