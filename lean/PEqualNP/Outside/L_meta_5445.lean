import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5445_aux

open PEqualNP.CircuitLowerBounds

-- Generic exhaustive search over truth tables (bit j of a table is the value on row j).
-- A table list is kept newest first. M is the all-true table, F the target table.

def mem (t : ℕ) : List ℕ → Bool
  | [] => false
  | a :: r => Nat.beq t a || mem t r

def pairsWith (a : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | b :: r => (a &&& b) :: (a ||| b) :: pairsWith a acc r

-- every table one new gate can have (up to tables already present or zero)
def prs (M : ℕ) : List ℕ → List ℕ
  | [] => [M]
  | a :: r => (M ^^^ a) :: pairsWith a (prs M r) r

def c0 (F : ℕ) (L : List ℕ) : Bool := Nat.beq F 0 || mem F L

def nw (Z acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | t :: r => if (Nat.beq t 0 || mem t Z || mem t acc) = true then nw Z acc r else nw Z (t :: acc) r

def orHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t ||| c) F || orHit F t r

def andHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t &&& c) F || andHit F t r

-- can a gate reading the new table t and one old table (or t alone) give F
def newOK (M F t : ℕ) (L : List ℕ) : Bool :=
  Nat.beq F (M ^^^ t) || (Nat.beq (t ||| F) F && orHit F t L) ||
    (Nat.beq (t &&& F) F && andHit F t L)

def can (M F : ℕ) : ℕ → List ℕ → Bool
  | 0, L => c0 F L
  | 1, L => c0 F L || mem F (prs M L)
  | 2, L => c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)
  | k + 3, L => c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))

theorem mem_iff (t : ℕ) (L : List ℕ) : mem t L = true ↔ t ∈ L := by
  induction L with
  | nil => simp [mem]
  | cons a r ih => simp [mem, ih]

theorem pairsWith_mem (a x : ℕ) (acc r : List ℕ) :
    x ∈ pairsWith a acc r ↔ x ∈ acc ∨ ∃ c ∈ r, x = a &&& c ∨ x = a ||| c := by
  induction r with
  | nil => simp [pairsWith]
  | cons b r ih =>
    simp only [pairsWith, List.mem_cons, ih, or_and_right, exists_or, exists_eq_left]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | (h | h) | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

theorem prs_cons (M t x : ℕ) (L : List ℕ) :
    x ∈ prs M (t :: L) ↔ x = M ^^^ t ∨ x ∈ prs M L ∨ ∃ c ∈ L, x = t &&& c ∨ x = t ||| c := by
  simp only [prs, List.mem_cons, pairsWith_mem]

theorem M_mem (M : ℕ) (L : List ℕ) : M ∈ prs M L := by
  induction L with
  | nil => simp [prs]
  | cons a r ih => exact (prs_cons M a M r).2 (Or.inr (Or.inl ih))

theorem not_mem (M a : ℕ) (L : List ℕ) (h : a ∈ L) : M ^^^ a ∈ prs M L := by
  induction L with
  | nil => simp at h
  | cons b r ih =>
    rw [prs_cons]
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (ih h))

theorem pair_mem (M a b : ℕ) (L : List ℕ) (ha : a ∈ L) (hb : b ∈ L) :
    (a &&& b ∈ L ∨ a &&& b ∈ prs M L) ∧ (a ||| b ∈ L ∨ a ||| b ∈ prs M L) := by
  induction L with
  | nil => simp at ha
  | cons x r ih =>
    rcases List.mem_cons.1 ha with ha1 | ha1 <;> rcases List.mem_cons.1 hb with hb1 | hb1
    · rw [ha1, hb1]
      simp
    · rw [ha1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨b, hb1, Or.inl rfl⟩))),
        Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨b, hb1, Or.inr rfl⟩)))⟩
    · rw [hb1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨a, ha1, Or.inl (Nat.land_comm _ _)⟩))),
        Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨a, ha1, Or.inr (Nat.lor_comm _ _)⟩)))⟩
    · obtain ⟨h1, h2⟩ := ih ha1 hb1
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inl h1)))
      · rcases h2 with h2 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h2)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inl h2)))

theorem and_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a &&& b = 0 ∨ a &&& b ∈ L ∨ a &&& b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simp
  rcases hb with hb | hb
  · subst hb; simp
  exact Or.inr (pair_mem M a b L ha hb).1

theorem or_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a ||| b = 0 ∨ a ||| b ∈ L ∨ a ||| b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; rw [Nat.zero_or]; tauto
  rcases hb with hb | hb
  · subst hb; rw [Nat.or_zero]; tauto
  exact Or.inr (pair_mem M a b L ha hb).2

theorem not_in (M a : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) : M ^^^ a ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simpa using M_mem M L
  exact not_mem M a L ha

theorem nw_acc (Z acc ts : List ℕ) (t : ℕ) (h : t ∈ acc) : t ∈ nw Z acc ts := by
  induction ts generalizing acc with
  | nil => simpa [nw] using h
  | cons s r ih =>
    simp only [nw]
    split
    · exact ih acc h
    · exact ih (s :: acc) (List.mem_cons_of_mem _ h)

theorem nw_mem (Z acc ts : List ℕ) (t : ℕ) (h : t ∈ ts) (h0 : t ≠ 0) (hZ : t ∉ Z) :
    t ∈ nw Z acc ts := by
  induction ts generalizing acc with
  | nil => simp at h
  | cons s r ih =>
    simp only [nw]
    rcases List.mem_cons.1 h with h | h
    · subst h
      split
      · rename_i hc
        simp only [Bool.or_eq_true, Nat.beq_eq, mem_iff] at hc
        rcases hc with (hc | hc) | hc
        · exact absurd hc h0
        · exact absurd hc hZ
        · exact nw_acc Z acc r t hc
      · exact nw_acc Z (t :: acc) r t (List.mem_cons_self)
    · split
      · exact ih acc h
      · exact ih (s :: acc) h

theorem orHit_iff (F t : ℕ) (L : List ℕ) : orHit F t L = true ↔ ∃ c ∈ L, t ||| c = F := by
  induction L with
  | nil => simp [orHit]
  | cons c r ih => simp [orHit, ih]

theorem andHit_iff (F t : ℕ) (L : List ℕ) : andHit F t L = true ↔ ∃ c ∈ L, t &&& c = F := by
  induction L with
  | nil => simp [andHit]
  | cons c r ih => simp [andHit, ih]

theorem newOK_complete (M F t : ℕ) (L : List ℕ)
    (h : F = M ^^^ t ∨ ∃ c ∈ L, F = t &&& c ∨ F = t ||| c) : newOK M F t L = true := by
  unfold newOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff]
  rcases h with h | ⟨c, hc, h | h⟩
  · exact Or.inl (Or.inl h)
  · right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_land]
  · left; right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_lor]

theorem newOK_sound (M F t : ℕ) (L : List ℕ) (h : newOK M F t L = true) :
    F ∈ prs M (t :: L) := by
  unfold newOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff] at h
  rw [prs_cons]
  rcases h with (h | ⟨_, c, hc, h⟩) | ⟨_, c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨c, hc, Or.inr h.symm⟩)
  · exact Or.inr (Or.inr ⟨c, hc, Or.inl h.symm⟩)

-- a gate built only from old tables adds nothing new
theorem absorb (M t x : ℕ) (L : List ℕ) (ht : t = 0 ∨ t ∈ L) (hx : x ∈ prs M (t :: L)) :
    x = 0 ∨ x ∈ L ∨ x ∈ prs M L := by
  rcases (prs_cons M t x L).1 hx with h | h | ⟨c, hc, h | h⟩
  · subst h; exact Or.inr (Or.inr (not_in M t L ht))
  · exact Or.inr (Or.inr h)
  · subst h; exact and_in M t c L ht (Or.inr hc)
  · subst h; exact or_in M t c L ht (Or.inr hc)

theorem can_of_c0 (M F k : ℕ) (L : List ℕ) (h : c0 F L = true) : can M F k L = true := by
  rcases k with _ | _ | _ | k <;> simp [can, h]

theorem c0_iff (F : ℕ) (L : List ℕ) : c0 F L = true ↔ F = 0 ∨ F ∈ L := by
  simp [c0, mem_iff]

-- a found table F one gate away
theorem can_of_prs (M F k : ℕ) (L : List ℕ) (h : F ∈ prs M L) : can M F (k + 1) L = true := by
  rcases k with _ | _ | k
  · simp [can, mem_iff, h]
  · simp [can, mem_iff, h]
  · by_cases hc : c0 F L = true
    · exact can_of_c0 M F _ L hc
    · rw [c0_iff] at hc
      push_neg at hc
      show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨F, nw_mem L [] _ F h hc.1 hc.2, can_of_c0 M F _ _ (by simp [c0, mem_iff])⟩

theorem mono (M F : ℕ) : ∀ (k : ℕ) (L : List ℕ), can M F k L = true → can M F (k + 1) L = true := by
  intro k
  induction k with
  | zero =>
    intro L h
    exact can_of_c0 M F 1 L h
  | succ k ih =>
    intro L h
    rcases k with _ | _ | k
    · -- from fuel 1 to fuel 2
      simp only [can, Bool.or_eq_true, mem_iff] at h
      rcases h with h | h
      · exact can_of_c0 M F 2 L h
      · exact can_of_prs M F 1 L h
    · -- from fuel 2 to fuel 3
      simp only [can, Bool.or_eq_true, mem_iff, List.any_eq_true] at h
      rcases h with (h | h) | ⟨t, ht, h⟩
      · exact can_of_c0 M F 3 L h
      · exact can_of_prs M F 2 L h
      · have hF := newOK_sound M F t L h
        have ht' : t ∈ prs M L := ht
        by_cases h0 : t = 0 ∨ t ∈ L
        · rcases absorb M t F L h0 hF with h1 | h1 | h1
          · exact can_of_c0 M F 3 L (by simp [c0, h1])
          · exact can_of_c0 M F 3 L (by simp [c0, mem_iff, h1])
          · exact can_of_prs M F 2 L h1
        · push_neg at h0
          show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F 2 (t :: L))) = true
          simp only [Bool.or_eq_true, List.any_eq_true]
          refine Or.inr ⟨t, nw_mem L [] _ t ht' h0.1 h0.2, ?_⟩
          exact can_of_prs M F 1 (t :: L) hF
    · show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 1 + 2) (t :: L))) = true
      have h' : (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true := h
      simp only [Bool.or_eq_true, List.any_eq_true] at h' ⊢
      rcases h' with h' | ⟨t, ht, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨t, ht, ih (t :: L) h'⟩

-- one new gate whose table t is new
theorem can_step (M F k t : ℕ) (L : List ℕ) (ht : t ∈ prs M L) (h0 : t ≠ 0) (hL : t ∉ L)
    (h : can M F k (t :: L) = true) : can M F (k + 1) L = true := by
  rcases k with _ | _ | k
  · simp only [can, c0_iff, List.mem_cons] at h
    rcases h with h | h | h
    · exact can_of_c0 M F 1 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 0 L ht
    · exact can_of_c0 M F 1 L (by simp [c0, mem_iff, h])
  · simp only [can, Bool.or_eq_true, c0_iff, List.mem_cons, mem_iff] at h
    rcases h with (h | h | h) | h
    · exact can_of_c0 M F 2 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 1 L ht
    · exact can_of_c0 M F 2 L (by simp [c0, mem_iff, h])
    · rcases (prs_cons M t F L).1 h with h1 | h1 | h1
      · show (c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, newOK_complete M F t L (Or.inl h1)⟩
      · exact can_of_prs M F 1 L h1
      · show (c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, newOK_complete M F t L (Or.inr h1)⟩
  · show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true
    simp only [Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨t, nw_mem L [] _ t ht h0 hL, h⟩

-- every wire i (also a missing one) is matched on rows j < N by zero or a table of L
def Inv (N : ℕ) (L : List ℕ) (w : ℕ → List Bool) : Prop :=
  ∀ i, ∃ a, (a = 0 ∨ a ∈ L) ∧ ∀ j < N, a.testBit j = (w j).getD i false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eq_of_bits (N a b : ℕ) (ha : a < 2 ^ N) (hb : b < 2 ^ N)
    (h : ∀ j < N, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · exact h i hi
  · have hp : 2 ^ N ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem gate_tab (N M : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (L : List ℕ) (hb : ∀ a ∈ L, a < 2 ^ N) (w : ℕ → List Bool) (hI : Inv N L w) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ t, (t = 0 ∨ t ∈ L ∨ t ∈ prs M L) ∧ t < 2 ^ N ∧
      ∀ j < N, t.testBit j = g.op.eval (g.inputs.map fun i => (w j).getD i false) := by
  have hz : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have hbd : ∀ a, (a = 0 ∨ a ∈ L) → a < 2 ^ N := by
    intro a ha
    rcases ha with ha | ha
    · rw [ha]; exact hz
    · exact hb a ha
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with hop | hop | hop <;> subst hop
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
    · exact ⟨0, Or.inl rfl, hz, fun j _ => by simp [GateOp.eval]⟩
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
  | [i], _ =>
    obtain ⟨a, ha, haw⟩ := hI i
    rcases hop with hop | hop | hop <;> subst hop
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · refine ⟨M ^^^ a, Or.inr (Or.inr (not_in M a L ha)), Nat.xor_lt_two_pow hMb (hbd a ha),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_xor, haw j hj, hM j hj]
  | [i1, i2], _ =>
    obtain ⟨a, ha, haw⟩ := hI i1
    obtain ⟨b, hb', hbw⟩ := hI i2
    rcases hop with hop | hop | hop <;> subst hop
    · refine ⟨a &&& b, and_in M a b L ha hb', Nat.and_lt_two_pow _ (hbd b hb'), fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_land, haw j hj, hbw j hj]
    · refine ⟨a ||| b, or_in M a b L ha hb', Nat.or_lt_two_pow (hbd a ha) (hbd b hb'),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_lor, haw j hj, hbw j hj]
    · refine ⟨M ^^^ a, Or.inr (Or.inr (not_in M a L ha)), Nat.xor_lt_two_pow hMb (hbd a ha),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_xor, haw j hj, hM j hj]
  | _ :: _ :: _ :: _, h => simp at h

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h, List.getElem?_append_left h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem inv_snoc (N m : ℕ) (L L' : List ℕ) (w : ℕ → List Bool) (v : ℕ → Bool) (t : ℕ)
    (hw : ∀ j, (w j).length = m) (hI : Inv N L w) (hLL : ∀ a ∈ L, a ∈ L')
    (ht : t = 0 ∨ t ∈ L') (htv : ∀ j < N, t.testBit j = v j) :
    Inv N L' (fun j => w j ++ [v j]) := by
  intro i
  by_cases h1 : i < m
  · obtain ⟨a, ha, haw⟩ := hI i
    refine ⟨a, ?_, fun j hj => ?_⟩
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (hLL a ha)
    · simp only [getD_snoc, hw j, if_pos h1]
      exact haw j hj
  · by_cases h2 : i = m
    · refine ⟨t, ht, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_pos h2]
      exact htv j hj
    · refine ⟨0, Or.inl rfl, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_neg h2, Nat.zero_testBit]

theorem sound (N M F : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (hF : F < 2 ^ N) :
    ∀ (gs : List Gate) (k m : ℕ) (L : List ℕ) (w : ℕ → List Bool),
      (∀ a ∈ L, a < 2 ^ N) → (∀ j, (w j).length = m) → Inv N L w →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      gs.length ≤ k → ∀ o : ℕ,
      (∀ j < N, (gs.foldl stp (w j)).getD o false = F.testBit j) → can M F k L = true := by
  intro gs
  induction gs with
  | nil =>
    intro k m L w hb _ hI _ _ o ho
    obtain ⟨a, ha, haw⟩ := hI o
    have hab : a < 2 ^ N := by
      rcases ha with ha | ha
      · rw [ha]; exact Nat.two_pow_pos N
      · exact hb a ha
    have hEq : a = F := eq_of_bits N a F hab hF (fun j hj => by
      rw [haw j hj]; exact ho j hj)
    exact can_of_c0 M F k L (by rw [c0_iff, ← hEq]; tauto)
  | cons g gs ih =>
    intro k m L w hb hw hI hg hk o ho
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : gs.length ≤ k := by simp at hk; omega
    obtain ⟨t, htm, htb, htv⟩ :=
      gate_tab N M hM hMb L hb w hI g (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2
    have hw' : ∀ j, (stp (w j) g).length = m + 1 := by
      intro j; simp [stp, hw j]
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    have ho' : ∀ j < N, (gs.foldl stp (stp (w j) g)).getD o false = F.testBit j := ho
    by_cases hold : t = 0 ∨ t ∈ L
    · have hI' : Inv N L (fun j => stp (w j) g) :=
        inv_snoc N m L L w _ t hw hI (fun a h => h) hold htv
      exact mono M F k L (ih k (m + 1) L _ hb hw' hI' hg' hk' o ho')
    · push_neg at hold
      have htp : t ∈ prs M L := by
        rcases htm with h | h | h
        · exact absurd h hold.1
        · exact absurd h hold.2
        · exact h
      have hI' : Inv N (t :: L) (fun j => stp (w j) g) :=
        inv_snoc N m L (t :: L) w _ t hw hI (fun a h => List.mem_cons_of_mem _ h)
          (Or.inr List.mem_cons_self) htv
      have hb' : ∀ a ∈ t :: L, a < 2 ^ N := by
        intro a h
        rcases List.mem_cons.1 h with h | h
        · rw [h]; exact htb
        · exact hb a h
      exact can_step M F k t L htp hold.1 hold.2 (ih k (m + 1) (t :: L) _ hb' hw' hI' hg' hk' o ho')

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

-- the generic statement: n inputs, rows j < N (row j sets input i to bit i of j),
-- all-true table M, target table F, input tables L0 (any order), K gates are too few
theorem main_gen (n N M F K : ℕ) (L0 : List ℕ) (f : (Fin n → Bool) → Bool)
    (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N) (hF : F < 2 ^ N)
    (hL0 : ∀ a ∈ L0, a < 2 ^ N)
    (hin : ∀ i < n, ∃ a ∈ L0, ∀ j < N, a.testBit j = j.testBit i)
    (hf : ∀ j < N, f (fun i => j.testBit i) = F.testBit j)
    (hs : can M F K L0 = false) :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → K + 1 ≤ t := by
  intro t ⟨C, hfan, hsize, heval⟩
  by_contra hlt
  have hk : C.gates.length ≤ K := by
    have : C.size = C.gates.length := rfl
    omega
  have hI : Inv N L0 (fun j => List.ofFn (fun i : Fin n => j.testBit i)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨a, ha, haj⟩ := hin i hi
      refine ⟨a, Or.inr ha, fun j hj => ?_⟩
      rw [ofFn_getD, dif_pos hi]
      exact haj j hj
    · refine ⟨0, Or.inl rfl, fun j _ => ?_⟩
      rw [ofFn_getD, dif_neg hi, Nat.zero_testBit]
  have ho : ∀ j < N, (C.gates.foldl stp (List.ofFn (fun i : Fin n => j.testBit i))).getD
      C.output false = F.testBit j := by
    intro j hj
    rw [← hf j hj, ← heval]
    rfl
  have := sound N M F hM hMb hF C.gates K n L0 _ hL0 (fun j => by simp) hI hfan hk C.output ho
  rw [hs] at this
  exact absurd this (by decide)

theorem search : can 0xFFFF 0xEEE8 4 [0xFF00, 0xF0F0, 0xCCCC, 0xAAAA] = false := by
  decide +kernel

theorem final : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)) t → 5 ≤ t :=
  main_gen 4 16 0xFFFF 0xEEE8 4 [0xFF00, 0xF0F0, 0xCCCC, 0xAAAA] _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) search

end PEqualNP.Outside.L_meta_5445_aux

theorem PEqualNP.Outside.L_meta_5445 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)) t → 5 ≤ t := by
  intro t h
  exact PEqualNP.Outside.L_meta_5445_aux.final t h
