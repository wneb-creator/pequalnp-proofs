import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.AndEquality

open PEqualNP.AndCount AndCountCircuit
variable {n : ℕ}

def left (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def right (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

private theorem side_congr {k : Nat} (I B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) {a b : Fin k → Bool} (h : ∀ j, j < i → a j = b j) :
    sideTrue I B F i a = sideTrue I B F i b := by
  unfold sideTrue
  congr 1
  apply propext
  constructor <;> rintro (raw | ⟨j, hj, lt, val⟩)
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt) ▸ val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt).symm ▸ val⟩

private theorem stable (C : AndCountCircuit n) (I : Finset (Fin n)) (m : Nat) :
    ∀ i : Fin C.size, i.val < m → ∀ a b : Nat, i.val < a → i.val < b →
    C.gateValFuel I a i = C.gateValFuel I b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi a b ha hb
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [gateValFuel]
        have eq (j : Fin C.size) (lt : j < i) :
            C.gateValFuel I a j = C.gateValFuel I b j :=
          ih j (by change j.val < i.val at lt; omega) a b
            (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
        rw [side_congr I _ _ i eq, side_congr I _ _ i eq]

theorem gate_eq (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal I i = (left C I i && right C I i) := by
  have h := stable C I C.size i i.isLt C.size (C.size + 1) i.isLt (by omega)
  exact h

def vars (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightVars i else C.leftVars i

def parents (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightGates i else C.leftGates i

def support (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => vars C q i ∪ ((parents C q i).filter (· < i)).biUnion (support C q d)

def hits (I S : Finset (Fin n)) := ∃ v ∈ S, v ∈ I

theorem hit_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i : Fin C.size) (I : Finset (Fin n)) :
    hits I (support C q (d+1) i) ↔ hits I (vars C q i) ∨
      ∃ j ∈ parents C q i, j < i ∧ hits I (support C q d j) := by
  simp only [hits, support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv | ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩
    · exact Or.inl ⟨v, hv, hI⟩
    · exact Or.inr ⟨j, hj, lt, v, hv, hI⟩
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, lt, v, hv, hI⟩)
    · exact ⟨v, Or.inl hv, hI⟩
    · exact ⟨v, Or.inr ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩

def clause (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outVars ∪ C.outGates.biUnion (support C q C.size)

theorem clause_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n)) :
    hits I (clause C q) ↔ hits I C.outVars ∨ ∃ j ∈ C.outGates, hits I (support C q C.size j) := by
  simp only [hits, clause, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv | ⟨j, hj, hv⟩, hi⟩
    · exact Or.inl ⟨v, hv, hi⟩
    · exact Or.inr ⟨j, hj, v, hv, hi⟩
  · rintro (⟨v, hv, hi⟩ | ⟨j, hj, v, hv, hi⟩)
    · exact ⟨v, Or.inl hv, hi⟩
    · exact ⟨v, Or.inr ⟨j, hj, hv⟩, hi⟩

theorem dominates (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (d : Nat) (i : Fin C.size) (hd : i.val < d) :
    C.gateVal I i = true → hits I (support C q d i) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    rw [gate_eq, Bool.and_eq_true] at h
    apply (hit_step C q d i I).2
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      cases e : q i <;> simp [vars, parents, e]
      · exact h.1
      · exact h.2
    rw [sideTrue, decide_eq_true_eq] at hs
    rcases hs with raw | ⟨j, hj, lt, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩

theorem chosen (C : AndCountCircuit n) (I : Finset (Fin n)) (d : Nat)
    (i : Fin C.size) (hd : i.val < d) :
    hits I (support C (left C I) d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step _ _ _ _ _).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    rw [gate_eq, Bool.and_eq_true]
    cases hl : left C I i with
    | false =>
      simp [vars, parents, hl] at hs
      change left C I i = true at hs
      simp [hl] at hs
    | true =>
      exact ⟨rfl, by simpa [vars, parents, hl, right] using hs⟩

theorem gives_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (h : C.eval I = true) : hits I (clause C q) := by
  rw [eval, decide_eq_true_eq] at h
  apply (clause_hit _ _ _).2
  rcases h with raw | ⟨j, hj, val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, dominates C q I C.size j j.isLt val⟩

theorem avoids (C : AndCountCircuit n) (I : Finset (Fin n)) (h : C.eval I = false) :
    ¬ hits I (clause C (left C I)) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit _ _ _).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen C I C.size j j.isLt val⟩
  simp [h] at ht

theorem complement_clause (C : AndCountCircuit n) (I : Finset (Fin n))
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C (left C I) := by
  intro u
  constructor
  · intro hu hc
    exact avoids C I h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C (left C I) _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids C I h ⟨v, hv, inside⟩


lemma chosen_of (C : AndCountCircuit n) (I : Finset (Fin n))
    (q : Fin C.size → Bool)
    (hq : ∀ i, C.gateVal I i = false →
      sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = false)
    (d : ℕ) (i : Fin C.size) (hd : i.val < d) :
    hits I (support C q d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step C q d i I).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    cases hv : C.gateVal I i with
    | true => rfl
    | false => rw [hq i hv] at hs; cases hs

lemma avoids_of (C : AndCountCircuit n) (I : Finset (Fin n))
    (q : Fin C.size → Bool)
    (hq : ∀ i, C.gateVal I i = false →
      sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = false)
    (h : C.eval I = false) : ¬ hits I (clause C q) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit C q I).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen_of C I q hq C.size j j.isLt val⟩
  simp [h] at ht

lemma complement_clause_of (C : AndCountCircuit n) (I : Finset (Fin n))
    (q : Fin C.size → Bool)
    (hq : ∀ i, C.gateVal I i = false →
      sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = false)
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C q := by
  intro u
  constructor
  · intro hu hc
    exact avoids_of C I q hq h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C q _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids_of C I q hq h ⟨v, hv, inside⟩

lemma canonical_choice_false (C : AndCountCircuit n) (I : Finset (Fin n))
    (i : Fin C.size) (hi : C.gateVal I i = false) :
    sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = false := by
  rw [gate_eq] at hi
  cases hl : left C I i with
  | false =>
    simp only [vars, parents, hl, Bool.false_eq_true, ite_false]
    exact hl
  | true =>
    have hr : right C I i = false := by simpa [hl] using hi
    simp only [vars, parents, hl, ite_true]
    exact hr

lemma saturated_false_rows_clean (C : AndCountCircuit n)
    (M : Finset (Finset (Fin n)))
    (hmax : ∀ I ∈ M, C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true)
    (hcard : M.card = 2 ^ C.size) :
    ∀ I ∈ M, ∀ i : Fin C.size, C.gateVal I i = false := by
  classical
  let code : M → (Fin C.size → Bool) := fun I => left C I.val
  have hinj : Function.Injective code := by
    intro I J hcode
    apply Subtype.ext
    apply Finset.ext
    intro u
    have hI := complement_clause C I.val (hmax I.val I.property).1
      (hmax I.val I.property).2 u
    have hJ := complement_clause C J.val (hmax J.val J.property).1
      (hmax J.val J.property).2 u
    change left C I.val = left C J.val at hcode
    rw [hcode] at hI
    exact hI.trans hJ.symm
  have hsurj : Function.Surjective code := by
    apply ((Fintype.bijective_iff_injective_and_card code).mpr ⟨hinj, ?_⟩).2
    simp [hcard]
  intro I hI i
  by_contra hbad
  have htrue : C.gateVal I i = true := by
    cases hv : C.gateVal I i <;> simp_all
  let q : Fin C.size → Bool := Function.update (left C I) i (!(left C I i))
  have hq : ∀ j, C.gateVal I j = false →
      sideTrue I (vars C q j) (parents C q j) j (C.gateVal I) = false := by
    intro j hj
    by_cases hji : j = i
    · subst j; rw [htrue] at hj; cases hj
    · have he : q j = left C I j := Function.update_of_ne hji _ _
      simpa only [vars, parents, he] using canonical_choice_false C I j hj
  obtain ⟨J, hJ⟩ := hsurj q
  have heq : I = J.val := by
    apply Finset.ext
    intro u
    have ha := complement_clause_of C I q hq (hmax I hI).1 (hmax I hI).2 u
    have hb := complement_clause C J.val (hmax J.val J.property).1
      (hmax J.val J.property).2 u
    change left C J.val = q at hJ
    rw [hJ] at hb
    exact ha.trans hb.symm
  have hqi : q i = left C I i := by
    change left C J.val = q at hJ
    rw [← hJ, ← heq]
  have hflip : q i = !(left C I i) := Function.update_self _ _ _
  rw [hflip] at hqi
  cases hb : left C I i <;> simp [hb] at hqi

end PEqualNP.Outside.L_meta_2583_aux.AndEquality
