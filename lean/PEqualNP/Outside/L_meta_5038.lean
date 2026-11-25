import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5038

def ds : Finset (Fin 13) := {0, 1, 3, 9}

def diffList : List (Fin 13) := [0, 1, 3, 9]

def rows : List Nat :=
  [7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587,
   19988517, 3211303, 19415081, 7372867, 24117317, 7340103, 23085129,
   23068749, 22052945, 5275731, 22020181, 19939425, 19923045, 18890857,
   6389891, 6619269, 6357127, 6570121, 6553741, 6324419, 6308041,
   21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625,
   17891877]

def inP (m : Nat) (a : Fin 13) : Bool := m.testBit a.val

def inL (m : Nat) (b : Fin 13) : Bool := m.testBit (13 + b.val)

def isInc (a b : Fin 13) : Bool := diffList.any (fun d => a == b + d)

def okMask (m : Nat) : Bool :=
  (List.finRange 13).all (fun l =>
    inL m l == (List.finRange 13).all (fun p => !inP m p || !isInc p l)) &&
  (List.finRange 13).all (fun p =>
    inP m p || (List.finRange 13).any (fun l => inL m l && isInc p l)) &&
  (List.finRange 13).all (fun l =>
    (List.finRange 13).any (fun p => inP m p && !isInc p l)) &&
  (List.finRange 13).all (fun p =>
    (List.finRange 13).any (fun l => inL m l && !isInc p l))

lemma all_ok : rows.all okMask = true := by decide +kernel

lemma shift_eq (a b d s : Fin 13) : a - s = b - s + d ↔ a = b + d := by
  have h1 : b - s + d = (b + d) - s := by
    rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]
  rw [h1]
  exact sub_left_inj

lemma isInc_iff (a b s : Fin 13) : isInc (a - s) (b - s) = true ↔ ∃ d ∈ ds, a = b + d := by
  unfold isInc diffList ds
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨0, Or.inl rfl, (shift_eq a b 0 s).mp h⟩
    · exact ⟨1, Or.inr (Or.inl rfl), (shift_eq a b 1 s).mp h⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), (shift_eq a b 3 s).mp h⟩
    · exact ⟨9, Or.inr (Or.inr (Or.inr rfl)), (shift_eq a b 9 s).mp h⟩
  · rintro ⟨d, rfl | rfl | rfl | rfl, h⟩
    · exact Or.inl ((shift_eq a b 0 s).mpr h)
    · exact Or.inr (Or.inl ((shift_eq a b 1 s).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((shift_eq a b 3 s).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((shift_eq a b 9 s).mpr h)))

lemma okMask_spec (m : Nat) (hm : okMask m = true) (s : Fin 13) :
    let P : Finset (Fin 13) := {p : Fin 13 | m.testBit (p - s).val = true}
    let Q : Finset (Fin 13) := {l : Fin 13 | m.testBit (13 + (l - s).val) = true}
    (∀ l : Fin 13, l ∈ Q ↔ ∀ p ∈ P, ¬∃ d ∈ ds, p = l + d) ∧
    (∀ p ∉ P, ∃ l ∈ Q, ∃ d ∈ ds, p = l + d) ∧
    (¬∃ l : Fin 13, ∀ p ∈ P, ∃ d ∈ ds, p = l + d) ∧
    (¬∃ p : Fin 13, ∀ l ∈ Q, ∃ d ∈ ds, p = l + d) := by
  simp only [okMask, Bool.and_eq_true] at hm
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    have hl := List.all_eq_true.mp h1 (l - s) (List.mem_finRange _)
    simp only [beq_iff_eq] at hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hml p hp hex
      have hml' : inL m (l - s) = true := hml
      rw [hl] at hml'
      have hp' := List.all_eq_true.mp hml' (p - s) (List.mem_finRange _)
      simp only [Bool.or_eq_true, Bool.not_eq_true', inP] at hp'
      rcases hp' with hnp | hni
      · exact Bool.false_ne_true (hnp.symm.trans hp)
      · exact Bool.false_ne_true (hni.symm.trans ((isInc_iff p l s).mpr hex))
    · intro hall
      change inL m (l - s) = true
      rw [hl]
      apply List.all_eq_true.mpr
      intro p' _
      simp only [Bool.or_eq_true, Bool.not_eq_true', inP]
      cases hp : m.testBit p'.val
      · exact Or.inl rfl
      · right
        cases hi : isInc p' (l - s)
        · rfl
        · exfalso
          have hsub : (p' + s) - s = p' := add_sub_cancel_right p' s
          have hmem : m.testBit ((p' + s) - s).val = true := by rw [hsub]; exact hp
          have hex : ∃ d ∈ ds, p' + s = l + d := (isInc_iff (p' + s) l s).mp (by rwa [hsub])
          exact hall (p' + s) hmem hex
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have h1p := List.all_eq_true.mp h2 (p - s) (List.mem_finRange _)
    simp only [Bool.or_eq_true, inP] at h1p
    rcases h1p with hpt | hex
    · exact absurd hpt hp
    · obtain ⟨l', _, hl'⟩ := List.any_eq_true.mp hex
      simp only [Bool.and_eq_true, inL] at hl'
      have hsub : (l' + s) - s = l' := add_sub_cancel_right l' s
      refine ⟨l' + s, ?_, (isInc_iff p (l' + s) s).mp (by rw [hsub]; exact hl'.2)⟩
      rw [hsub]; exact hl'.1
  · rintro ⟨l, hl⟩
    have h1l := List.all_eq_true.mp h3 (l - s) (List.mem_finRange _)
    obtain ⟨p', _, hp'⟩ := List.any_eq_true.mp h1l
    simp only [Bool.and_eq_true, Bool.not_eq_true', inP] at hp'
    have hsub : (p' + s) - s = p' := add_sub_cancel_right p' s
    have hmem : p' + s ∈ ({p : Fin 13 | m.testBit (p - s).val = true} : Finset (Fin 13)) := by
      simp [hsub, hp'.1]
    have hinc := (isInc_iff (p' + s) l s).mpr (hl (p' + s) hmem)
    rw [hsub] at hinc
    exact Bool.false_ne_true (hp'.2.symm.trans hinc)
  · rintro ⟨p, hp⟩
    have h1p := List.all_eq_true.mp h4 (p - s) (List.mem_finRange _)
    obtain ⟨l', _, hl'⟩ := List.any_eq_true.mp h1p
    simp only [Bool.and_eq_true, Bool.not_eq_true', inL] at hl'
    have hsub : (l' + s) - s = l' := add_sub_cancel_right l' s
    have hmem : l' + s ∈ ({l : Fin 13 | m.testBit (13 + (l - s).val) = true} : Finset (Fin 13)) := by
      simp [hsub, hl'.1]
    have hinc := (isInc_iff p (l' + s) s).mpr (hp (l' + s) hmem)
    rw [hsub] at hinc
    exact Bool.false_ne_true (hl'.2.symm.trans hinc)

lemma main_proof : ∀ m ∈ rows, ∀ s : Fin 13,
    let P : Finset (Fin 13) := {p : Fin 13 | m.testBit (p - s).val = true}
    let Q : Finset (Fin 13) := {l : Fin 13 | m.testBit (13 + (l - s).val) = true}
    (∀ l : Fin 13, l ∈ Q ↔ ∀ p ∈ P, ¬∃ d ∈ ds, p = l + d) ∧
    (∀ p ∉ P, ∃ l ∈ Q, ∃ d ∈ ds, p = l + d) ∧
    (¬∃ l : Fin 13, ∀ p ∈ P, ∃ d ∈ ds, p = l + d) ∧
    (¬∃ p : Fin 13, ∀ l ∈ Q, ∃ d ∈ ds, p = l + d) := fun m hm s =>
  okMask_spec m (List.all_eq_true.mp all_ok m hm) s

end PEqualNP.Outside.L_meta_5038

theorem PEqualNP.Outside.L_meta_5038 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x2;     have x3 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x2;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x2;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x3;   have x4 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x3;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x4; ∀ x3 ∈ x2,   ∀ (x5 : Fin (13 : ℕ)),     have x6 : Finset (Fin (13 : ℕ)) := {x6 : Fin (13 : ℕ) | x3.testBit ↑(x6 - x5) = Bool.true};     have x7 : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | x3.testBit ((13 : ℕ) + ↑(x7 - x5)) = Bool.true};     (∀ (x8 : Fin (13 : ℕ)), x8 ∈ x7 ↔ ∀ x9 ∈ x6, ¬∃ x11 ∈ x1, x9 = x8 + x11) ∧ (∀ x8 ∉ x6, ∃ x10 ∈ x7, ∃ x11 ∈ x1, x8 = x10 + x11) ∧ (¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x6, ∃ x11 ∈ x1, x9 = x8 + x11) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x7, ∃ x11 ∈ x1, x8 = x9 + x11 := by
  exact PEqualNP.Outside.L_meta_5038.main_proof
