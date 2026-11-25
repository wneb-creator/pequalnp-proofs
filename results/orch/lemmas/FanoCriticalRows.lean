import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.FanoCriticalRows

def incident (p l : Fin 7) : Prop :=
  (p.val + 7 - l.val) % 7 ∈ ({0, 1, 3} : Finset ℕ)

instance (p l : Fin 7) : Decidable (incident p l) := inferInstanceAs
  (Decidable ((p.val + 7 - l.val) % 7 ∈ ({0, 1, 3} : Finset ℕ)))

def target (x : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, incident p l ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

def maskInput (m : BitVec 14) (i : Fin 14) : Bool := m.getLsbD i.val

def edgeMask (p l : Fin 7) : BitVec 14 :=
  (1 <<< p.val) ||| (1 <<< (7 + l.val))

def edges : List (BitVec 14) :=
  [129, 130, 136, 258, 260, 272, 516, 520, 544, 1032, 1040,
   1088, 2049, 2064, 2080, 4098, 4128, 4160, 8193, 8196, 8256]

def maximalFalse : List (BitVec 14) :=
  [16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361,
   10250, 6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632,
   1313, 9250, 1188, 1063, 8488, 8368, 8250, 3008, 833,
   2626, 2244, 2376, 2126, 720, 595, 480, 361, 244, 127]

def Below (x y : Fin 14 → Bool) : Prop := ∀ i, x i = true → y i = true

instance (x y : Fin 14 → Bool) : Decidable (Below x y) := inferInstanceAs
  (Decidable (∀ i, x i = true → y i = true))

def closedInput (s : BitVec 7) (i : Fin 14) : Bool :=
  if h : i.val < 7 then s.getLsbD i.val else
    decide (∀ p : Fin 7,
      incident p ⟨i.val - 7, by omega⟩ → s.getLsbD p.val = false)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem closure_check : ∀ s : BitVec 7,
    maximalFalse.any (fun m => decide (Below (closedInput s) (maskInput m))) = true := by
  decide +kernel

theorem closure_covered (s : BitVec 7) :
    ∃ m ∈ maximalFalse, Below (closedInput s) (maskInput m) := by
  obtain ⟨m, hm, h⟩ := List.any_eq_true.mp (closure_check s)
  exact ⟨m, hm, of_decide_eq_true h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem edge_mem : ∀ p l : Fin 7, incident p l → edgeMask p l ∈ edges := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem edge_bits : ∀ (p l : Fin 7) (i : Fin 14),
    maskInput (edgeMask p l) i = true ↔
      i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem rows_correct :
    (∀ e ∈ edges, target (maskInput e) = true) ∧
    (∀ m ∈ maximalFalse, target (maskInput m) = false) := by
  have h :
      edges.all (fun e => target (maskInput e)) = true ∧
      maximalFalse.all (fun m => !(target (maskInput m))) = true := by
    decide +kernel
  refine ⟨List.all_eq_true.mp h.1, ?_⟩
  intro m hm
  have hh := List.all_eq_true.mp h.2 m hm
  cases hb : target (maskInput m) <;> simp_all

theorem false_below (x : Fin 14 → Bool) (hx : target x = false) :
    ∃ m ∈ maximalFalse, Below x (maskInput m) := by
  let s : BitVec 7 :=
    (BitVec.ofBoolListLE (List.ofFn (fun p : Fin 7 => x (Fin.castAdd 7 p)))).cast
      (by simp)
  have hs (p : Fin 7) : s.getLsbD p.val = x (Fin.castAdd 7 p) := by
    simp only [s, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos p.isLt, Option.getD_some]
  obtain ⟨m, hm, hcover⟩ := closure_covered s
  refine ⟨m, hm, fun i hi => hcover i ?_⟩
  unfold closedInput
  split_ifs with h
  · rw [hs ⟨i.val, h⟩]
    simpa using hi
  · apply decide_eq_true
    intro p hp
    cases hb : s.getLsbD p.val with
    | false => rfl
    | true =>
      have htrue : target x = true := by
        apply decide_eq_true
        refine ⟨p, ⟨i.val - 7, by omega⟩, hp, (hs p).symm.trans hb, ?_⟩
        have heq : Fin.natAdd 7 (⟨i.val - 7, by omega⟩ : Fin 7) = i := by
          apply Fin.ext
          simp only [Fin.natAdd_mk]
          omega
        simpa only [heq] using hi
      exact Bool.noConfusion (hx.symm.trans htrue)

theorem true_above (x : Fin 14 → Bool) (hx : target x = true) :
    ∃ e ∈ edges, Below (maskInput e) x := by
  obtain ⟨p, l, hp, hxp, hxl⟩ := of_decide_eq_true hx
  refine ⟨edgeMask p l, edge_mem p l hp, fun i hi => ?_⟩
  rcases (edge_bits p l i).mp hi with rfl | rfl
  · exact hxp
  · exact hxl

theorem correct_of_critical_rows
    (f : (Fin 14 → Bool) → Bool)
    (mono : ∀ x y, Below x y → f x = true → f y = true)
    (positive : ∀ e ∈ edges, f (maskInput e) = true)
    (negative : ∀ m ∈ maximalFalse, f (maskInput m) = false) :
    ∀ x, f x = target x := by
  intro x
  cases hx : target x with
  | false =>
    obtain ⟨m, hm, hxm⟩ := false_below x hx
    cases hf : f x with
    | false => rfl
    | true => exact Bool.noConfusion ((negative m hm).symm.trans (mono x _ hxm hf))
  | true =>
    obtain ⟨e, he, hex⟩ := true_above x hx
    exact mono _ x hex (positive e he)

end PEqualNP.Outside.L_meta_2583.FanoCriticalRows
