import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_118.Bridge

open Relation Classical

abbrev Walk (E : ℕ → ℕ → Prop) := Relation.ReflTransGen E

theorem walk_le {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {i j : ℕ} (w : Walk E i j) : j ≤ i := by
  induction w with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (Nat.le_of_lt (dec e)).trans ih

theorem walk_sub {E E' : ℕ → ℕ → Prop} (sub : ∀ {i j}, E i j → E' i j)
    {i j : ℕ} (w : Walk E i j) : Walk E' i j := by
  induction w with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (sub e)

theorem clash {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ A m ∧ Walk E c m ∧ Walk E d m := by
  induction wc with
  | refl =>
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · exact False.elim (ne e)
    · have lt : q < r := (walk_le dec wq).trans_lt (dec rd)
      exact ⟨r, q, c, Or.inl rfl, Or.inr wq, rc, eq, (Ne.symm (ne_of_lt lt)),
        ac, .refl, wd⟩
  | @tail u v wu he ih =>
    have wcu : Walk E c u := walk_sub (fun h => h.1) wu
    have lu : u < r := (walk_le dec wcu).trans_lt (dec rc)
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · subst v
      exact ⟨u, r, d, Or.inr wcu, Or.inl rfl, he.1, rd, ne_of_lt lu, he.2,
        .tail wcu he.1, .refl⟩
    · by_cases hp : u = q
      · subst q
        exact ih wq
      · exact ⟨u, q, v, Or.inr wcu, Or.inr wq, he.1, eq, hp, he.2,
          .tail wcu he.1, wd⟩

theorem same_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) : A z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, am, _, _⟩ := clash dec rc rd ne ac wc wd
  exact unique p q m hp hq ep eq neq ▸ am

theorem swap_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ad : A d) {x : ℕ}
    (wd : Walk (fun i j => E i j ∧ A j) d x) (wc : Walk E c x) : A z :=
  same_entry dec rd rc ne.symm
    (fun p q m hp hq ep eq hne => unique q p m hq hp eq ep hne.symm) ad wd wc

section semantic

variable {α κ : Type}
variable {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
variable {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
variable (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
variable (B : α → ℕ → Prop) (side : α → Bool)
variable (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
variable (branch : ∀ a, B a (if side a then c else d))
variable (route : ∀ a i, B a i →
  ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
variable (points : ∀ k, ∃ a, point k a)

def Common (E : ℕ → ℕ → Prop) (c d : ℕ) (u : ℕ) : Prop :=
  Walk E c u ∧ Walk E d u

def Forced (bad : α → κ → Prop) (point : κ → α → Prop) (side : α → Bool) (a : α) : Prop :=
  (∃ k, point k a ∧ ∃ b, point k b ∧ side b ≠ side a) ∨
  (∀ k, bad a k → ∀ b, point k b → side b ≠ side a)

include branch route one in
theorem criticalSide {a k} (ha : point k a) :
    Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  obtain ⟨j, hj, w⟩ := route a _ (branch a)
  have eq := (one ha j).1 hj
  simpa [eq] using w

include branch route one points in
theorem forced_common {a} (ha : Forced bad point side a) :
    ∃ k, bad a k ∧ Common E c d (leaf k) ∧
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  have mk : ∀ {k b}, bad a k →
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) →
      point k b → side b ≠ side a →
      ∃ k, bad a k ∧ Common E c d (leaf k) ∧
        Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
    intro k b bk wa pb hn
    have wb := criticalSide bad point leaf B side one branch route pb
    refine ⟨k, bk, ?_, wa⟩
    have ua := walk_sub (fun h => h.1) wa
    have ub := walk_sub (fun h => h.1) wb
    cases ea : side a <;> cases eb : side b <;> simp_all [Common]
  rcases ha with ⟨k, ka, b, kb, hn⟩ | ha
  · exact mk ((one ka k).2 rfl) (criticalSide bad point leaf B side one branch route ka) kb hn
  · obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    obtain ⟨b, kb⟩ := points k
    exact mk bk wa kb (ha k bk b kb)

include dec rc rd ne branch route one points in
theorem entry_exists {a} (ha : Forced bad point side a) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ B a m ∧ Common E c d m := by
  obtain ⟨k, _, ⟨wc, wd⟩, w⟩ := forced_common bad point leaf B side one branch route points ha
  cases h : side a
  · simp [h] at w
    obtain ⟨q, p, m, hq, hp, eq, ep, neq, b, rd', rc'⟩ :=
      clash dec rd rc ne.symm (by simpa [h] using branch a) w wc
    exact ⟨p, q, m, hp, hq, ep, eq, neq.symm, b, rc', rd'⟩
  · simp [h] at w
    exact clash dec rc rd ne (by simpa [h] using branch a) w wd

variable {z : ℕ}
variable (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)

include dec rc rd ne unique branch route one in
theorem false_on_common {k a}
    (hc : Common E c d (leaf k)) (ha : point k a) : B a z := by
  have w := criticalSide bad point leaf B side one branch route ha
  cases h : side a
  · simp [h] at w
    exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.1
  · simp [h] at w
    exact same_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.2

include dec rc rd ne unique branch route one points in
theorem false_on_forced {a}
    (ha : Forced bad point side a) : B a z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, hm, _⟩ :=
    entry_exists dec rc rd ne bad point leaf B side one branch route points ha
  exact unique p q m hp hq ep eq neq ▸ hm

include dec rc rd ne unique branch route one points in
theorem one_entry_characterization (fz : Common E c d z) :
    (∀ a, Forced bad point side a → B a z) ∧
    (∀ a, B a z → ∃ k, bad a k ∧ ∀ b, point k b → B b z) ∧
    (∀ a, ¬ B a z → ∃ k, bad a k ∧ ∃ b, point k b ∧ ¬ B b z) := by
  refine ⟨fun a ha => false_on_forced dec rc rd ne bad point leaf B side one branch route points unique ha, ?_, ?_⟩
  · intro a ba
    obtain ⟨k, bk, w⟩ := route a z ba
    have w' := walk_sub (fun h => h.1) w
    have common : Common E c d (leaf k) := ⟨fz.1.trans w', fz.2.trans w'⟩
    exact ⟨k, bk, fun b hb => false_on_common dec rc rd ne bad point leaf B side one branch route unique common hb⟩
  · intro a ba
    obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    by_contra! hall
    have hpk := hall k bk
    -- If every critical point of the routed leaf lies below z, following any such
    -- point from z proves z reaches that leaf. Then both root sides can reach it.
    obtain ⟨b, hb⟩ := points k
    obtain ⟨j, bj, w⟩ := route b z (hpk b hb)
    rcases (one hb j).1 bj with rfl
    have w' := walk_sub (fun h => h.1) w
    have cl : Common E c d (leaf j) := ⟨fz.1.trans w', fz.2.trans w'⟩
    apply ba
    cases h : side a
    · simp [h] at wa
      exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) wa cl.1
    · simp [h] at wa
      exact same_entry dec rc rd ne unique (by simpa [h] using branch a) wa cl.2

end semantic

end PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_118.Graph

abbrev ClauseMap (V : Type) := Nat → LinClause V
abbrev Parents := Nat → List Nat

def Rule {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (i : Nat) : Prop :=
    (P i = [] ∧ C i ∈ F) ∨
    (∃ j < i, P i = [j] ∧ (∀ a, LinClauseSat a (C j) → LinClauseSat a (C i))) ∨
    (∃ j < i, ∃ k < i, P i = [j, k] ∧ IsLinResolvent (C j) (C k) (C i))

def Encoded {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (lines : List (LinClause V)) : Prop :=
  (∀ i < lines.length, Rule F C P i) ∧
  (∀ D, D ∈ lines ↔ ∃ i < lines.length, C i = D)

theorem rule_congr {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C D : ClauseMap V} {P Q : Parents} {i : Nat}
    (same : ∀ j ≤ i, D j = C j) (parents : Q i = P i)
    (h : Rule F C P i) : Rule F D Q i := by
  rw [Rule, parents, same i le_rfl]
  rcases h with h | ⟨j, ji, e, weak⟩ | ⟨j, ji, k, ki, e, res⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, ji, e, by simpa only [same _ ji.le] using weak⟩)
  · exact Or.inr (Or.inr ⟨j, ji, k, ki, e, by simpa only [same _ ji.le, same _ ki.le] using res⟩)

theorem extend {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents} (enc : Encoded F C P π)
    (D : LinClause V) (q : List Nat)
    (hr : Rule F (Function.update C π.length D) (Function.update P π.length q) π.length) :
    Encoded F (Function.update C π.length D) (Function.update P π.length q) (D :: π) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have ib : i ≤ π.length := Nat.lt_succ_iff.1 (by simpa only [List.length_cons] using hi)
    rcases eq_or_lt_of_le ib with rfl | lt
    · exact hr
    · refine rule_congr (fun j ji => Function.update_of_ne (ne_of_lt (ji.trans_lt lt)) _ _) ?_ (enc.1 i lt)
      exact Function.update_of_ne (ne_of_lt lt) _ _
  · intro A
    simp only [List.mem_cons, List.length_cons]
    constructor
    · intro h
      rcases h with rfl | h
      · exact ⟨π.length, Nat.lt_succ_self _, by simp⟩
      · obtain ⟨i, hi, eq⟩ := (enc.2 _).1 h
        exact ⟨i, by omega, by simpa [Function.update_of_ne (ne_of_lt hi)] using eq⟩
    · rintro ⟨i, hi, eq⟩
      have ib : i ≤ π.length := by omega
      rcases eq_or_lt_of_le ib with rfl | lt
      · exact Or.inl (by simpa using eq.symm)
      · exact Or.inr ((enc.2 _).2 ⟨i, lt, by simpa [Function.update_of_ne (ne_of_lt lt)] using eq⟩)

theorem build_graph {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) : ∃ C P, Encoded F C P π := by
  induction der with
  | nil => exact ⟨fun _ => ∅, fun _ => [], by simp [Encoded]⟩
  | @ax π D _ hD ih =>
    obtain ⟨C, P, enc⟩ := ih
    refine ⟨_, _, extend enc D [] ?_⟩
    exact Or.inl (by simpa using hD)
  | @res π D H R _ d h res ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, di⟩ := (enc.2 _).1 d
    obtain ⟨j, hj, ej⟩ := (enc.2 _).1 h
    refine ⟨_, _, extend enc R [i, j] (Or.inr (Or.inr ⟨i, hi, j, hj, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), Function.update_of_ne (ne_of_lt hj), di, ej] using res
  | @weak π D R _ hD hw ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, eq⟩ := (enc.2 _).1 hD
    refine ⟨_, _, extend enc R [i] (Or.inr (Or.inl ⟨i, hi, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), eq] using hw

def Edge (P : Parents) (i j : Nat) : Prop := j ∈ P i

theorem edge_desc {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i j : Nat} (h : Rule F C P i)
    (e : Edge P i j) : j < i := by
  rcases h with ⟨r, _⟩ | ⟨k, ki, r, _⟩ | ⟨k, ki, m, mi, r, _⟩
  · simp [Edge, r] at e
  · have eq : j = k := by simpa [Edge, r] using e
    simpa [eq] using ki
  · simp only [Edge, r, List.mem_cons, List.mem_nil_iff, or_false] at e
    rcases e with rfl | rfl <;> assumption

def FalseAt {V : Type} (C : ClauseMap V) (a : V → Bool) (i : Nat) : Prop :=
  ¬ LinClauseSat a (C i)

theorem resolve_branch {V : Type} [DecidableEq V] {D H R : LinClause V}
    (a : V → Bool) {f : Finset V}
    (rr : R = D.erase (f, false) ∪ H.erase (f, true))
    (fr : ¬ LinClauseSat a R) :
    if Odd (f.filter (fun x => a x = true)).card
    then ¬ LinClauseSat a D else ¬ LinClauseSat a H := by
  subst R
  by_cases h : Odd (f.filter (fun x => a x = true)).card
  · rw [ite_eq_left h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat
  · rw [ite_eq_right h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat

theorem follow {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {n : Nat} (rule : ∀ i < n, Rule F C P i) (a : V → Bool)
    {i : Nat} (hi : i < n) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have visit : ∀ j < i, Edge P i j → FalseAt C a j →
        ∃ k, P k = [] ∧ C k ∈ F ∧ FalseAt C a k ∧
          Walk (fun u v => Edge P u v ∧ FalseAt C a v) i k := by
      intro j lt ej fj
      obtain ⟨k, p0, fm, fk, w⟩ := ih j lt (lt.trans hi) fj
      exact ⟨k, p0, fm, fk, Relation.ReflTransGen.head ⟨ej, fj⟩ w⟩
    rcases rule i hi with ⟨p0, hF⟩ | ⟨j, ji, pp, hw⟩ | ⟨j, ji, k, ki, pp, f, h1, h2, rr⟩
    · exact ⟨i, p0, hF, fi, .refl⟩
    · exact visit j ji (by simp [Edge, pp]) (fun h => fi (hw a h))
    · have br := resolve_branch a rr fi
      split at br
      · exact visit j ji (by simp [Edge, pp]) br
      · exact visit k ki (by simp [Edge, pp]) br

theorem first_false {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {π : List (LinClause V)}
    (graph : Encoded F C P π) (empty : ∅ ∈ π)
    (axsat : ∀ D ∈ F, ∃ a, LinClauseSat a D) :
    ∃ r < π.length, (∀ a, FalseAt C a r) ∧
      (∀ j < r, ∃ a, LinClauseSat a (C j)) ∧
      ∃ j < r, ∃ k < r, j ≠ k ∧ P r = [j, k] ∧ ∃ f : Finset V,
          f ≠ ∅ ∧ ∀ a, if Odd (f.filter (fun x => a x = true)).card
            then FalseAt C a j else FalseAt C a k := by
  classical
  have existsFalse : ∃ j, j < π.length ∧ ∀ a, FalseAt C a j := by
    obtain ⟨j, hj, he⟩ := (graph.2 _).1 empty
    exact ⟨j, hj, by simp [FalseAt, he, LinClauseSat]⟩
  let r := Nat.find existsFalse
  obtain ⟨ri, fr⟩ := Nat.find_spec existsFalse
  have prev : ∀ j < r, ∃ a, LinClauseSat a (C j) := by
    intro j hj
    by_contra! h
    exact Nat.find_min existsFalse hj ⟨hj.trans ri, h⟩
  refine ⟨r, ri, fr, prev, ?_⟩
  rcases graph.1 r ri with ⟨_, hF⟩ | ⟨j, jr, _, hw⟩ | ⟨j, jr, k, kr, p, f, df, dk, rr⟩
  · obtain ⟨a, ha⟩ := axsat _ hF
    exact (fr a ha).elim
  · obtain ⟨a, ha⟩ := prev j jr
    exact (fr a (hw a ha)).elim
  · have br : ∀ a, if Odd (f.filter (fun x => a x = true)).card
      then FalseAt C a j else FalseAt C a k := fun a => resolve_branch a rr (fr a)
    have ne : j ≠ k := by
      intro eq
      obtain ⟨a, sat⟩ := prev j jr
      have no := br a
      rw [eq] at no sat
      split at no <;> exact no sat
    have nz : f ≠ ∅ := by
      intro eq
      obtain ⟨a, sat⟩ := prev k kr
      exact (by simpa [eq] using br a : FalseAt C a k) sat
    exact ⟨j, jr, k, kr, ne, p, f, nz, br⟩

open scoped BigOperators

def LocalEdge (P : Parents) (r i j : Nat) : Prop := i ≤ r ∧ Edge P i j

noncomputable def Live (P : Parents) (r : Nat) : Finset Nat := by
  classical
  exact (Finset.range (r+1)).filter (fun v => Walk (LocalEdge P r) r v)

theorem bounded_edge {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {i j : Nat} (e : LocalEdge P r i j) : j < i := edge_desc (rules i e.1) e.2

theorem live_iff {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    i ∈ Live P r ↔ Walk (LocalEdge P r) r i := by
  classical
  simp only [Live, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun w => ⟨walk_le (bounded_edge rules) w, w⟩⟩

theorem live_closed {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hi : i ∈ Live P r) (e : Edge P i j) :
    j ∈ Live P r := by
  have w := (live_iff rules).1 hi
  exact (live_iff rules).2 (.tail w ⟨walk_le (bounded_edge rules) w, e⟩)

def InDegree (P : Parents) (s : Finset Nat) (j : Nat) : Nat :=
  ∑ i ∈ s, (P i).count j

theorem count_edges {P : Parents} {s : Finset Nat}
    (hs : ∀ i ∈ s, ∀ j ∈ P i, j ∈ s) :
    ∑ j ∈ s, InDegree P s j = ∑ i ∈ s, (P i).length := by
  unfold InDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j ∈ s, List.count j (P i)) = ∑ j ∈ (P i).toFinset, List.count j (P i) := by
      symm
      apply Finset.sum_subset
      · intro j hj
        exact hs i hi j (List.mem_toFinset.1 hj)
      · intro j hj hnot
        exact List.count_eq_zero_of_not_mem (fun h => hnot (List.mem_toFinset.2 h))
    _ = (P i).length := by
      simpa only [List.toFinset_coe, Multiset.coe_count, Multiset.coe_card] using
        Multiset.toFinset_sum_count_eq ((P i : List Nat) : Multiset Nat)

theorem inDegree_root {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    InDegree P (Live P r) r = 0 := by
  unfold InDegree
  apply Finset.sum_eq_zero
  intro i hi
  have il := walk_le (bounded_edge rules) ((live_iff rules).1 hi)
  apply List.count_eq_zero_of_not_mem
  intro ei
  exact (Nat.not_lt_of_le il) (edge_desc (rules i il) ei)

theorem inDegree_pos {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (hj : j ∈ Live P r) (ne : j ≠ r) : 1 ≤ InDegree P (Live P r) j := by
  obtain ⟨i, wi, ei⟩ := ((live_iff rules).1 hj).cases_tail.resolve_left ne
  have im : i ∈ Live P r := (live_iff rules).2 wi
  have h := Finset.single_le_sum (f := fun u => (P u).count j) (fun _ _ => Nat.zero_le _) im
  exact (Nat.succ_le_of_lt (List.count_pos_iff.2 ei.2)).trans h

noncomputable def Surplus (P : Parents) (r : Nat) : Nat :=
  ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1)

theorem surplus_identity {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (∑ i ∈ Live P r, (P i).length) + 1 = (Live P r).card + Surplus P r := by
  have h1 := count_edges (fun i hi j hj => live_closed rules hi hj)
  have root : r ∈ Live P r := (live_iff rules).2 .refl
  have hsum := Finset.sum_erase_add (Live P r) (InDegree P (Live P r)) root
  rw [inDegree_root rules, Nat.add_zero, h1] at hsum
  have hc := Finset.card_erase_of_mem root
  have hp := Finset.card_pos.2 ⟨_, root⟩
  have eq : ∑ j ∈ (Live P r).erase r, InDegree P (Live P r) j =
      ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1 + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨ne, hm⟩ := Finset.mem_erase.1 hj
    have lb := inDegree_pos rules hm ne
    omega
  have hone : (∑ _ ∈ (Live P r).erase r, (1 : Nat)) = ((Live P r).erase r).card := by simp
  rw [Finset.sum_add_distrib, hone] at eq
  unfold Surplus
  omega

noncomputable def WithArity (P : Parents) (r n : Nat) : Finset Nat :=
  (Live P r).filter (fun j => (P j).length = n)

theorem length_le_two {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i : Nat} (h : Rule F C P i) :
    (P i).length ≤ 2 := by
  rcases h with ⟨r, _⟩ | ⟨j, _, r, _⟩ | ⟨j, _, k, _, r, _⟩ <;> simp [r]

theorem arity_sum (P : Parents) (r n k : Nat) :
    (∑ i ∈ Live P r, if (P i).length = n then k else 0) = k * (WithArity P r n).card := by
  rw [← Finset.sum_filter]
  simp [WithArity, Nat.mul_comm]
theorem arity_count {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (Live P r).card + 1 =
      2 * (WithArity P r 0).card + (WithArity P r 1).card + Surplus P r := by
  have hk : ∀ i ∈ Live P r, (P i).length ≤ 2 := by
    intro i hi
    exact length_le_two (rules i (walk_le (bounded_edge rules) ((live_iff rules).1 hi)))
  have decomp :
      (Live P r).card = (WithArity P r 0).card + (WithArity P r 1).card + (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (1 : Nat) = ∑ i ∈ Live P r,
        ((if (P i).length = 0 then 1 else 0) + (if (P i).length = 1 then 1 else 0) +
          (if (P i).length = 2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    have countOnes : (∑ _ ∈ Live P r, (1 : Nat)) = (Live P r).card := by simp
    rw [countOnes] at h
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have edges :
      (∑ i ∈ Live P r, (P i).length) = (WithArity P r 1).card + 2 * (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (P i).length = ∑ i ∈ Live P r,
        ((if (P i).length = 1 then 1 else 0) + (if (P i).length = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have hs := surplus_identity rules
  omega

theorem shared_degree {P : Parents} {s : Finset Nat} {p q m : Nat}
    (hp : p ∈ s) (hq : q ∈ s) (ep : Edge P p m) (eq : Edge P q m) (ne : p ≠ q) :
    2 ≤ InDegree P s m := by
  have tm : ({p, q} : Finset Nat) ⊆ s := by
    intro i hi
    rcases (by simpa using hi : i = p ∨ i = q) with rfl | rfl <;> assumption
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u => (P u).count m) tm
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 ne), Finset.sum_singleton] at hs
  have lp := List.count_pos_iff.2 ep
  have lq := List.count_pos_iff.2 eq
  unfold InDegree
  omega

theorem only_one_share {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r m z : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (budget : Surplus P r ≤ 1)
    (hm : m ∈ Live P r) (hz : z ∈ Live P r)
    (sm : 2 ≤ InDegree P (Live P r) m) (sz : 2 ≤ InDegree P (Live P r) z) :
    m = z := by
  by_contra hne
  have nr := inDegree_root rules
  have mn : m ≠ r := by
    rintro rfl
    omega
  have zn : z ≠ r := by
    rintro rfl
    omega
  have both : ({m,z} : Finset Nat) ⊆ (Live P r).erase r := by
    intro j hj
    rcases (by simpa using hj : j = m ∨ j = z) with rfl | rfl
    · exact Finset.mem_erase.2 ⟨mn,hm⟩
    · exact Finset.mem_erase.2 ⟨zn,hz⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j => InDegree P (Live P r) j - 1) both (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 hne), Finset.sum_singleton] at hh
  unfold Surplus at budget
  omega

theorem walk_localize {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ≤ r)
    (w : Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j ∧ j ≤ r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have next := (edge_desc (rules _ ih.2) e.1).le.trans ih.2
    exact ⟨.tail ih.1 ⟨⟨ih.2, e.1⟩, next, e.2⟩, next⟩

theorem localized_route {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (a : V → Bool) {i : Nat} (hi : i ≤ r) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j := by
  obtain ⟨j, h0, ha, ff, w⟩ := follow (n := r+1)
    (fun i hi => rules i (Nat.lt_succ_iff.1 hi)) a (Nat.lt_succ_iff.2 hi) fi
  exact ⟨j, h0, ha, ff, (walk_localize rules hi w).1⟩

theorem live_card_le (P : Parents) (r : Nat) : (Live P r).card ≤ r + 1 := by
  classical
  unfold Live
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem unique_leaves {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (ax : κ → LinClause V) (exh : F = Set.range ax)
    (critical : ∀ k, ∃ a : V → Bool, ∀ j, ¬ LinClauseSat a (ax j) ↔ j = k) :
    ∃ leaf : κ → Nat, Function.Injective leaf ∧
      (∀ k, leaf k ∈ WithArity P r 0 ∧ C (leaf k) = ax k) ∧
      Fintype.card κ ≤ (WithArity P r 0).card ∧
      ((WithArity P r 0).card = Fintype.card κ →
        ∀ j ∈ WithArity P r 0, ∃ k, leaf k = j) := by
  classical
  have located : ∀ k, ∃ j, j ∈ WithArity P r 0 ∧ C j = ax k := by
    intro k
    obtain ⟨a, cert⟩ := critical k
    obtain ⟨j, hj, hc, ff, w⟩ := localized_route rules a le_rfl (fr a)
    rw [exh] at hc
    obtain ⟨k', hk'⟩ := hc
    have h : ¬ LinClauseSat a (ax k') := by simpa [FalseAt, hk'] using ff
    have eq := (cert k').1 h
    subst k'
    refine ⟨j, ?_, hk'.symm⟩
    simp only [WithArity, Finset.mem_filter, hj, List.length_nil, and_true]
    exact (live_iff rules).2 (walk_sub (fun e => e.1) w)
  choose leaf spec using located
  have inj : Function.Injective leaf := by
    intro u v h
    obtain ⟨a, cert⟩ := critical u
    have hEq := (spec u).2.symm.trans ((congrArg C h).trans (spec v).2)
    have no := (cert u).2 rfl
    rw [hEq] at no
    exact ((cert v).1 no).symm
  have ss : Finset.univ.image leaf ⊆ WithArity P r 0 := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hj
    exact (spec k).1
  have card : (Finset.univ.image leaf).card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
  refine ⟨leaf, inj, spec, by simpa [card] using Finset.card_le_card ss, ?_⟩
  intro eq j hj
  have e : Finset.univ.image leaf = WithArity P r 0 :=
    Finset.eq_of_subset_of_card_le ss (by rw [eq, card])
  rw [← e] at hj
  obtain ⟨k, _, e⟩ := Finset.mem_image.1 hj
  exact ⟨k, e⟩

noncomputable def useful {V : Type} (R : LinClause V) : Bool := by
  classical
  exact decide (∃ a, ¬ LinClauseSat a R)

theorem useful_spec {V : Type} (R : LinClause V) :
    useful R = true ↔ ∃ a, ¬ LinClauseSat a R := by
  classical
  simp [useful]

theorem prune_taut {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) :
    IsLinDerivation F (π.filter useful) := by
  induction der with
  | nil => exact .nil
  | @ax π D _ hD ih =>
    simp only [List.filter_cons]
    split
    · exact .ax ih hD
    · exact ih
  | @res π D H R _ d h resolvent ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨f, df, hf, rr⟩ := resolvent
      by_cases ud : useful D = true
      · have md := List.mem_filter.2 ⟨d, ud⟩
        by_cases uh : useful H = true
        · exact .res ih md (List.mem_filter.2 ⟨h, uh⟩) ⟨f, df, hf, rr⟩
        · exact .weak ih md (by
            intro a sat
            by_contra no
            have b := resolve_branch a rr no
            split at b
            · exact b sat
            · exact uh ((useful_spec _).2 ⟨a, b⟩))
      · have weak : ∀ a, LinClauseSat a H → LinClauseSat a R := by
          intro a sat
          by_contra no
          have b := resolve_branch a rr no
          split at b
          · exact ud ((useful_spec _).2 ⟨a, b⟩)
          · exact b sat
        obtain ⟨a, ff⟩ := (useful_spec _).1 ur
        have hu : useful H = true := (useful_spec _).2 ⟨a, fun s => ff (weak a s)⟩
        exact .weak ih (List.mem_filter.2 ⟨h, hu⟩) weak
    · rw [ite_eq_right ur]
      exact ih
  | @weak π D R _ hD hw ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨a, no⟩ := (useful_spec _).1 ur
      exact .weak ih (List.mem_filter.2 ⟨hD, (useful_spec _).2 ⟨a, fun h => no (hw a h)⟩⟩) hw
    · rw [ite_eq_right ur]
      exact ih

theorem encoded_useful {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents}
    (h : Encoded F C P (π.filter useful)) {i : Nat} (hi : i < (π.filter useful).length) :
    ∃ a, FalseAt C a i := by
  have mm := (h.2 _).2 ⟨i, hi, rfl⟩
  exact (useful_spec _).1 (List.mem_filter.1 mm).2

theorem walk_keep_live {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ∈ Live P r)
    (w : Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ∈ Live P r ∧ FalseAt C a v)) i j ∧ j ∈ Live P r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have hm := live_closed rules ih.2 e.1.2
    exact ⟨.tail ih.1 ⟨e.1, hm, e.2.2⟩, hm⟩

theorem high_weak_shared {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (rc : LocalEdge P r r c) (rd : LocalEdge P r r d) (ne : c ≠ d)
    (size : (Live P r).card ≤ 47) (wcount : 3 ≤ (WithArity P r 1).card)
    (labels : Fintype.card κ = 22)
    (ax : κ → LinClause V) (exh : F = Set.range ax) (point : κ → (V → Bool) → Prop)
    (point_exists : ∀ k, ∃ a, point k a)
    (one : ∀ {a k}, point k a → ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k)
    (side : (V → Bool) → Bool)
    (side_choose : ∀ a, FalseAt C a (if side a then c else d))
    (force_exists : ∃ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a) :
    ∃ z < r,
      (∀ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a → FalseAt C a z) ∧
      (∀ a, FalseAt C a z → ∃ k, (¬ LinClauseSat a (ax k)) ∧ ∀ b, point k b → FalseAt C b z) ∧
      (∀ a, ¬ FalseAt C a z → ∃ k, (¬ LinClauseSat a (ax k)) ∧ ∃ b, point k b ∧ ¬ FalseAt C b z) := by
  have crit : ∀ k, ∃ a : V → Bool, ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k := by
    intro k
    obtain ⟨a, ha⟩ := point_exists k
    exact ⟨a, one ha⟩
  obtain ⟨leaf, _, atLeaf, lb, covers⟩ := unique_leaves rules fr ax exh crit
  have card := arity_count rules
  have ex : (WithArity P r 0).card = Fintype.card κ := by omega
  have su : Surplus P r ≤ 1 := by omega
  let E := LocalEdge P r
  let B := fun a i => i ∈ Live P r ∧ FalseAt C a i
  let bad := fun a k => ¬ LinClauseSat a (ax k)
  have branch : ∀ a, B a (if side a then c else d) := by
    intro a
    refine ⟨?_, side_choose a⟩
    cases h : side a
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rd))
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rc))
  have route : ∀ a i, B a i →
      ∃ k, bad a k ∧ Walk (fun u v => E u v ∧ B a v) i (leaf k) := by
    intro a i bi
    have ir := walk_le (bounded_edge rules) ((live_iff rules).1 bi.1)
    obtain ⟨j, j0, _, jf, w⟩ := localized_route rules a ir bi.2
    obtain ⟨wm, jm⟩ := walk_keep_live rules bi.1 w
    have jax : j ∈ WithArity P r 0 := by simpa [WithArity, j0] using jm
    obtain ⟨k, hk⟩ := covers ex j jax
    have ceq : C j = ax k := hk ▸ (atLeaf k).2
    exact ⟨k, by simpa [bad, FalseAt, ceq] using jf, hk ▸ wm⟩
  have desc : ∀ {i j}, E i j → j < i := bounded_edge rules
  obtain ⟨a, ha⟩ := force_exists
  obtain ⟨p, q, z, hp, hq, ep, eq, pq, _, common⟩ :=
    entry_exists desc rc rd ne bad point leaf B side one branch route point_exists ha
  have from_left : ∀ {p}, p = r ∨ Walk E c p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rc hp)
  have from_right : ∀ {p}, p = r ∨ Walk E d p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rd hp)
  have zl : z ∈ Live P r := live_closed rules (from_left hp) ep.2
  have zd : 2 ≤ InDegree P (Live P r) z := shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq
  have one_merge : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z := by
    intro p q m hp hq ep eq pq
    have ml := live_closed rules (from_left hp) ep.2
    exact only_one_share rules su ml zl
      (shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq) zd
  have lem := one_entry_characterization desc rc rd ne bad point leaf B side one branch route
    point_exists one_merge common
  have zr : z < r := (desc ep).trans_le ep.1
  exact ⟨z, zr, by simpa [B, zl] using lem⟩

end PEqualNP.Outside.L_pcx_118.Graph
namespace PEqualNP.Outside.L_pcx_118.Linear

def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (a &&& q))))).testBit 0

theorem smear_xor (s a b : Nat) :
    smear s (a ^^^ b) = smear s a ^^^ smear s b := by
  simp only [smear, Nat.shiftRight_xor_distrib]
  ac_rfl

theorem parity_left (a b q : Nat) :
    parity (a ^^^ b) q = (parity a q ^^ parity b q) := by
  simp only [parity, Nat.and_xor_distrib_right, smear_xor, Nat.testBit_xor]

theorem parity_right (a b q : Nat) :
    parity q (a ^^^ b) = (parity q a ^^ parity q b) := by
  simp only [parity, Nat.and_xor_distrib_left, smear_xor, Nat.testBit_xor]

def span : List Nat -> List Nat
  | [] => [0]
  | b :: bs => let xs := span bs; xs ++ xs.map (fun x => x ^^^ b)

theorem span_map (g : Nat -> Nat) (g0 : g 0 = 0)
    (gxor : ∀ x y, g (x ^^^ y) = g x ^^^ g y)
    (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    g x ∈ span (bs.map g) := by
  induction bs generalizing x with
  | nil =>
    simp [span] at hx
    subst x
    simp [span, g0]
  | cons b bs ih =>
    simp only [span, List.map_cons, List.mem_append, List.mem_map] at hx ⊢
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl (ih x hx)
    · exact Or.inr ⟨g y, ih y hy, (gxor y b).symm⟩

theorem span_filter (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    x ∈ span (bs.filter (fun b => b != 0)) := by
  induction bs generalizing x with
  | nil => simpa using hx
  | cons b bs ih =>
    simp only [span, List.mem_append, List.mem_map] at hx
    by_cases hb : b = 0
    · subst b
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact ih x hx
      · simpa using ih y hy
    · have hb' : (b != 0) = true := by simpa using hb
      simp only [List.filter_cons, hb', ite_true, span, List.mem_append, List.mem_map]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact Or.inl (ih x hx)
      · exact Or.inr ⟨y, ih y hy, rfl⟩

def correct (a b x : Nat) : Nat := if parity a x then x ^^^ b else x

theorem correct_zero (a b : Nat) : correct a b 0 = 0 := by
  simp [correct, parity, smear]

theorem correct_xor (a b x y : Nat) :
    correct a b (x ^^^ y) = correct a b x ^^^ correct a b y := by
  cases hx : parity a x <;> cases hy : parity a y <;>
    simp [correct, parity_right, hx, hy] <;> try ac_rfl
  calc
    x ^^^ y = (x ^^^ y) ^^^ (b ^^^ b) := by simp
    _ = _ := by ac_rfl

def basisStep (a : Nat) (bs : List Nat) : List Nat :=
  match bs.find? (parity a) with
  | none => bs
  | some b => (bs.map (correct a b)).filter (fun v => v != 0)

theorem step_sound (a : Nat) (bs : List Nat) (q : Nat)
    (hmem : q ∈ span bs) (heven : parity a q = false) :
    q ∈ span (basisStep a bs) := by
  unfold basisStep
  split
  next => exact hmem
  next b _ =>
    have h := span_map (correct a b) (correct_zero a b) (correct_xor a b) bs q hmem
    exact span_filter _ _ (by simpa [correct, heven] using h)

open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3

def idx (v : V) : Nat := 3 * v.1.val + v.2.val
def assignment (a : Nat) (v : V) : Bool := a.testBit (idx v)
def formMask (S : Finset V) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : V) : idx v < 12 := by
  have h₁ := v.1.isLt
  have h₂ := v.2.isLt
  unfold idx
  omega

theorem idx_inj : Function.Injective idx := by
  intro v w h
  have hv := v.2.isLt
  have hw := w.2.isLt
  unfold idx at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem mask_insert (S : Finset V) {v : V} (h : v ∉ S) :
    formMask (insert v S) = 2 ^ idx v ^^^ formMask S := by
  simp [formMask, Finset.fold_insert h]

theorem mask_lt (S : Finset V) : formMask S < 4096 := by
  change formMask S < 2 ^ 12
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert v S h ih =>
    rw [mask_insert S h]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by decide : 1 < 2) (idx_lt v)) ih

theorem bit_mask (S : Finset V) (v : V) :
    (formMask S).testBit (idx v) = decide (v ∈ S) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert w S h ih =>
    rw [mask_insert S h, Nat.testBit_xor, Nat.testBit_two_pow, ih]
    by_cases hw : v = w
    · subst w
      simp [h]
    · have hidx : idx w ≠ idx v := fun e => hw (idx_inj e.symm)
      simp [hidx, hw]

theorem mask_nz {S : Finset V} (h : S.Nonempty) : formMask S ≠ 0 := by
  obtain ⟨v,hv⟩ := h
  intro hz
  have h' := bit_mask S v
  simp [hz,hv] at h'

theorem parity_unit (a j : Nat) (hj : j < 12) : parity a (2 ^ j) = a.testBit j := by
  have hb : a &&& (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases h : j = i
    · subst i
      cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow]
    · cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow, h]
  have hp : ∀ k : Fin 12, parity (2 ^ k.val) (2 ^ k.val) = true := by decide +kernel
  have hs := hp ⟨j,hj⟩
  unfold parity at hs ⊢
  rw [hb]
  cases ht : a.testBit j
  · simp [smear]
  · simpa only [ht, ite_true, Nat.and_self] using hs

theorem parity_form (a : Nat) (S : Finset V) :
    parity a (formMask S) = decide (Odd (S.filter (fun v => assignment a v = true)).card) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask,parity,smear]
  | @insert v S h ih =>
    rw [mask_insert S h, parity_right, parity_unit _ _ (idx_lt v), ih]
    change (assignment a v ^^ _) = _
    cases hv : assignment a v with
    | false => simp [Finset.filter_insert,hv]
    | true =>
      have hv' : v ∉ S.filter (fun w => assignment a w = true) := by
        intro hh
        exact h (Finset.mem_filter.mp hh).1
      rw [Finset.filter_insert, if_pos hv, Finset.card_insert_of_notMem hv']
      cases hd : decide (Odd (S.filter (fun w => assignment a w = true)).card) with
      | false =>
        have ho : ¬ Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_false hd
        have he : Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]
      | true =>
        have ho : Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_true hd
        have he : ¬ Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]

theorem linEqSat_iff (a : Nat) (e : LinEq V) :
    LinEqSat (assignment a) e ↔ parity a (formMask e.1) = e.2 := by
  rw [parity_form]
  unfold LinEqSat
  cases he : e.2 <;> simp [he]
def axioms : List (Nat × Bool) := [(7, false), (56, false), (448, false), (3584, false), (9, true), (18, true), (36, true), (65, true), (130, true), (260, true), (513, true), (1026, true), (2052, true), (72, true), (144, true), (288, true), (520, true), (1040, true), (2080, true), (576, true), (1152, true), (2304, true)]

def support (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit (idx v))

def clauseOf (row : Nat × Bool) : Clause V := (support row.1).image (fun v => (v,!row.2))

def linearOf (row : Nat × Bool) : LinClause V := linOfClause (clauseOf row)

theorem idx_cover (n : Nat) (h : n < 12) : ∃ v : V, idx v = n := by
  let v : V := (⟨n/3, by omega⟩, ⟨n%3, by omega⟩)
  exact ⟨v, by change 3 * (n/3) + n%3 = n; omega⟩

theorem singleton_sat (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem linear_iff (a : V → Bool) (C : Clause V) :
    LinClauseSat a (linOfClause C) ↔ ClauseSat a C := by
  simp only [LinClauseSat, linOfClause, Finset.mem_image, ClauseSat]
  constructor
  · rintro ⟨q, ⟨⟨v,s⟩, hs, rfl⟩, hq⟩
    exact ⟨(v,s), hs, (singleton_sat _ _ _).1 hq⟩
  · rintro ⟨⟨v,s⟩, hs, hv⟩
    exact ⟨({v},s), ⟨(v,s), hs, rfl⟩, (singleton_sat _ _ _).2 hv⟩

theorem false_on_spec (a : Nat) (row : Nat × Bool) (hh : row.1 < 4096) :
    (a &&& row.1 = if row.2 then row.1 else 0) ↔
      ¬ LinClauseSat (assignment a) (linearOf row) := by
  rw [linearOf, linear_iff]
  have ht : ClauseSat (assignment a) (clauseOf row) ↔
      ∃ v ∈ support row.1, assignment a v = !row.2 := by
    constructor
    · rintro ⟨l, hl, h⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
      exact ⟨v,hv,h⟩
    · rintro ⟨v,hv,h⟩
      exact ⟨(v,!row.2), Finset.mem_image.mpr ⟨v,hv,rfl⟩, h⟩
  rw [ht]
  push_neg
  have he : ∀ v : V, assignment a v ≠ !row.2 ↔ assignment a v = row.2 := by
    intro v
    cases h₁ : assignment a v <;> cases row.2 <;> simp
  simp only [he]
  constructor
  · intro h v hv
    have hm : row.1.testBit (idx v) = true := (Finset.mem_filter.mp hv).2
    have eq := congrArg (fun k : Nat => k.testBit (idx v)) h
    cases hs : row.2 <;> simpa [Nat.testBit_and, hm, hs, assignment] using eq
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hm : row.1.testBit i = true
    · have hi : i < 12 := by
        by_contra hn
        have hp : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have hw : row.1 < 2 ^ i := lt_of_lt_of_le hh hp
        simp [Nat.testBit_lt_two_pow hw] at hm
      obtain ⟨v,rfl⟩ := idx_cover i hi
      have hv : v ∈ support row.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
      have hs := h v hv
      cases hr : row.2 <;> simp_all [Nat.testBit_and, assignment]
    · have hn : row.1.testBit i = false := by
        cases ht : row.1.testBit i <;> simp_all
      cases hr : row.2 <;> simp [Nat.testBit_and, hn, hr]

def pigeon (i : Fin 4) : Clause V := Finset.univ.image (fun j : Fin 3 => ((i,j),true))
def collision (i k : Fin 4) (j : Fin 3) : Clause V := {((i,j),false),((k,j),false)}

def axHas (C : Clause V) : Bool := axioms.any (fun row => clauseOf row == C)

theorem all_rows_small : axioms.all (fun row => decide (row.1 < 4096)) = true := by decide +kernel
theorem all_pigeon : ∀ i, axHas (pigeon i) = true := by decide +kernel
theorem all_collision : ∀ i k j, i ≠ k → axHas (collision i k j) = true := by decide +kernel
theorem label_distinct : (axioms.map clauseOf).Nodup := by decide +kernel

theorem php_covered {C : Clause V} (h : C ∈ PHP 4 3) : ∃ row ∈ axioms, clauseOf row = C := by
  have hc : axHas C = true := by
    rcases h with ⟨i,rfl⟩ | ⟨i,k,j,hne,rfl⟩
    · exact all_pigeon i
    · exact all_collision i k j hne
  exact ⟨_, (List.any_eq_true.mp hc).choose_spec.1, beq_iff_eq.mp (List.any_eq_true.mp hc).choose_spec.2⟩

def codeAssignment (a : V → Bool) : Nat :=
  formMask (Finset.univ.filter (fun v => a v = true))

theorem assignment_code (a : V → Bool) : assignment (codeAssignment a) = a := by
  funext v
  simp [assignment, codeAssignment, bit_mask]

theorem code_lt (a : V → Bool) : codeAssignment a < 4096 := mask_lt _

noncomputable def forms (C : LinClause V) : List Nat :=
  ((C.toList.map (fun e => formMask e.1)).filter (fun f => f != 0))

theorem forms_mem (C : LinClause V) (f : Nat) :
    f ∈ forms C ↔ (∃ e ∈ C, formMask e.1 = f) ∧ f ≠ 0 := by
  simp [forms]

theorem forms_lt (C : LinClause V) (f : Nat) (h : f ∈ forms C) : f < 4096 ∧ f ≠ 0 := by
  obtain ⟨⟨e, _, rfl⟩, hz⟩ := (forms_mem _ _).1 h
  exact ⟨mask_lt _,hz⟩

def possible (p : Nat) (xs : List Nat) (a : Nat) : Bool :=
  xs.all (fun q => parity p q == parity a q)

theorem possible_clause {C : LinClause V} {p : Nat}
    (hp : ¬ LinClauseSat (assignment p) C) (a : Nat) :
    possible p (forms C) a = true ↔ ¬ LinClauseSat (assignment a) C := by
  have hp' : ∀ e ∈ C, parity p (formMask e.1) ≠ e.2 := by
    intro e he h
    exact hp ⟨e, he, (linEqSat_iff _ _).2 h⟩
  constructor
  · intro ha he
    obtain ⟨e, he, hs⟩ := he
    have hh := (linEqSat_iff _ _).1 hs
    apply hp' e he
    by_cases hz : formMask e.1 = 0
    · have hpar : parity p (formMask e.1) = parity a (formMask e.1) := by
        simp [hz, parity, smear]
      exact hpar.trans hh
    · have hf : formMask e.1 ∈ forms C := (forms_mem _ _).2 ⟨⟨e,he,rfl⟩,hz⟩
      have hpar := beq_iff_eq.1 (List.all_eq_true.1 ha _ hf)
      exact hpar.trans hh
  · intro ha
    apply List.all_eq_true.mpr
    intro f hf
    obtain ⟨⟨e, he, rfl⟩, _⟩ := (forms_mem _ _).1 hf
    apply beq_iff_eq.mpr
    have hn : parity a (formMask e.1) ≠ e.2 := by
      intro hi
      exact ha ⟨e, he, (linEqSat_iff _ _).2 hi⟩
    have hm := hp' e he
    have eq_of_ne : ∀ x y z : Bool, x ≠ z → y ≠ z → x = y := by decide
    exact eq_of_ne _ _ _ hm hn

theorem possible_nonempty {C : LinClause V} {p : Nat}
    (hp : ¬ LinClauseSat (assignment p) C)
    (hs : ∃ a : V → Bool, LinClauseSat a C) :
    forms C ≠ [] := by
  obtain ⟨a,ha⟩ := hs
  intro h
  have hh : possible p (forms C) (codeAssignment a) = true := by simp [possible,h]
  have contra := (possible_clause hp _).1 hh
  rw [assignment_code] at contra
  exact contra ha
end PEqualNP.Outside.L_pcx_118.Linear
namespace PEqualNP.Outside.L_pcx_118.Finite

def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (a &&& q))))).testBit 0

theorem smear_xor (s a b : Nat) :
    smear s (a ^^^ b) = smear s a ^^^ smear s b := by
  simp only [smear, Nat.shiftRight_xor_distrib]
  ac_rfl

theorem parity_left (a b q : Nat) :
    parity (a ^^^ b) q = (parity a q ^^ parity b q) := by
  simp only [parity, Nat.and_xor_distrib_right, smear_xor, Nat.testBit_xor]

theorem parity_right (a b q : Nat) :
    parity q (a ^^^ b) = (parity q a ^^ parity q b) := by
  simp only [parity, Nat.and_xor_distrib_left, smear_xor, Nat.testBit_xor]

def span : List Nat -> List Nat
  | [] => [0]
  | b :: bs => let xs := span bs; xs ++ xs.map (fun x => x ^^^ b)

theorem span_map (g : Nat -> Nat) (g0 : g 0 = 0)
    (gxor : ∀ x y, g (x ^^^ y) = g x ^^^ g y)
    (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    g x ∈ span (bs.map g) := by
  induction bs generalizing x with
  | nil =>
    simp [span] at hx
    subst x
    simp [span, g0]
  | cons b bs ih =>
    simp only [span, List.map_cons, List.mem_append, List.mem_map] at hx ⊢
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl (ih x hx)
    · exact Or.inr ⟨g y, ih y hy, (gxor y b).symm⟩

theorem span_filter (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    x ∈ span (bs.filter (fun b => b != 0)) := by
  induction bs generalizing x with
  | nil => simpa using hx
  | cons b bs ih =>
    simp only [span, List.mem_append, List.mem_map] at hx
    by_cases hb : b = 0
    · subst b
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact ih x hx
      · simpa using ih y hy
    · have hb' : (b != 0) = true := by simpa using hb
      simp only [List.filter_cons, hb', ite_true, span, List.mem_append, List.mem_map]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact Or.inl (ih x hx)
      · exact Or.inr ⟨y, ih y hy, rfl⟩

def correct (a b x : Nat) : Nat := if parity a x then x ^^^ b else x

theorem correct_zero (a b : Nat) : correct a b 0 = 0 := by
  simp [correct, parity, smear]

theorem correct_xor (a b x y : Nat) :
    correct a b (x ^^^ y) = correct a b x ^^^ correct a b y := by
  cases hx : parity a x <;> cases hy : parity a y <;>
    simp [correct, parity_right, hx, hy] <;> try ac_rfl
  calc
    x ^^^ y = (x ^^^ y) ^^^ (b ^^^ b) := by simp
    _ = _ := by ac_rfl

def basisStep (a : Nat) (bs : List Nat) : List Nat :=
  match bs.find? (parity a) with
  | none => bs
  | some b => (bs.map (correct a b)).filter (fun v => v != 0)

theorem step_sound (a : Nat) (bs : List Nat) (q : Nat)
    (hmem : q ∈ span bs) (heven : parity a q = false) :
    q ∈ span (basisStep a bs) := by
  unfold basisStep
  split
  next => exact hmem
  next b _ =>
    have h := span_map (correct a b) (correct_zero a b) (correct_xor a b) bs q hmem
    exact span_filter _ _ (by simpa [correct, heven] using h)

def falseAxiom (a : Nat) (data : Nat × Bool) : Bool :=
  decide (a &&& data.1 = if data.2 then data.1 else 0)

def axioms : List (Nat × Bool) := [(7, false), (56, false), (448, false), (3584, false), (9, true), (18, true), (36, true), (65, true), (130, true), (260, true), (513, true), (1026, true), (2052, true), (72, true), (144, true), (288, true), (520, true), (1040, true), (2080, true), (576, true), (1152, true), (2304, true)]

def critical : List (List Nat) := [[672, 784, 1120, 1288, 2128, 2184], [644, 770, 1092, 1281, 2114, 2177], [532, 546, 1036, 1057, 2058, 2065], [84, 98, 140, 161, 266, 273], [1289, 2185], [786, 2130], [676, 1124], [1121, 2129], [674, 2186], [788, 1292], [673, 785], [1122, 1290], [2132, 2188], [1100, 2122], [660, 2193], [802, 1313], [652, 778], [1108, 1297], [2146, 2209], [596, 610], [1164, 1185], [2314, 2321]]

def shared (q a : Nat) : Bool :=
  let side := parity a q
  critical.any (fun g => g.any (fun b => parity b q != side) &&
    g.any (fun b => parity b q == side) && g.contains a) ||
  (axioms.zip critical).all (fun (ax,g) =>
    !falseAxiom a ax || g.all (fun b => parity b q != side))

def possible (a : Nat) (qs : List Nat) (b : Nat) : Bool :=
  qs.all (fun f => parity a f == parity b f)

def invalid (p : Nat) (qs : List Nat) (a : Nat) (mode : Bool) : Bool :=
  let inside := possible p qs a
  let avoids := (axioms.zip critical).all fun (ax,g) =>
    !falseAxiom a ax || (g.all (possible p qs)) != mode
  inside == mode && avoids

def initBasis : List Nat := (List.range 12).map (fun i => 1 <<< i)

def nullForms (ps : List Nat) : List Nat :=
  let p := ps.headD 0
  let basis := ps.foldl (fun b a => basisStep (a ^^^ p) b) initBasis
  (span basis).erase 0

def sublists : List Nat -> List (List Nat)
  | [] => [[]]
  | a :: as =>
    let bs := sublists as
    bs ++ bs.map (fun b => a :: b)

def cert (r : Nat × Nat × List Nat × List Nat × List (List Nat × Nat × Bool)) : Bool :=
  let (q, w, ps, fs, cases) := r
  let p := ps.headD 0
  shared q w && ps.all (shared q) &&
  (nullForms ps).all fs.contains &&
  (sublists fs).all (fun ks => ks.isEmpty || cases.any (fun c => c.1 == ks)) &&
  cases.all (fun (forms,a,mode) => invalid p forms a mode)


def unpack (k a : Nat) : List Nat :=
  (List.range k).map (fun i => (a >>> (12*i)) &&& 4095)

abbrev Row := Nat × Nat × Nat × List Nat × List (List Nat × Nat × Bool)

def packedCert (r : Row) : Bool :=
  let (q,k,d,fs,cs) := r
  let xs := unpack k d
  cert (q, xs.headD 0, xs, fs, cs)

def initial : List Nat := (List.range 12).map (fun i => 1 <<< i)

theorem fold_insert_testBit (xs : List Nat) (acc q : Nat) :
    (xs.foldl (fun a i => a ||| (1 <<< i)) acc).testBit q =
      (acc.testBit q || xs.contains q) := by
  induction xs generalizing acc with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons, ih]
    simp only [List.contains_cons, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.testBit_two_pow, Bool.or_assoc]
    have e : decide (i = q) = (q == i) := by
      by_cases h : q = i
      · simp [h]
      · have hn : i ≠ q := Ne.symm h
        simp [h, hn]
    simp only [e]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem initial_bits : (span initial).foldl (fun a i => a ||| (1 <<< i)) 0 = 2 ^ 4096 - 1 := by
  decide +kernel

theorem in_initial (q : Nat) (hq : q < 4096) : q ∈ span initial := by
  have h := congrArg (fun n : Nat => n.testBit q) initial_bits
  rw [fold_insert_testBit] at h
  simpa [Nat.testBit_two_pow_sub_one, hq] using h

theorem fold_sound (p q : Nat) (ps bs : List Nat) (hmem : q ∈ span bs)
    (hpar : ∀ a ∈ ps, parity a q = parity p q) :
    q ∈ span (ps.foldl (fun b a => basisStep (a ^^^ p) b) bs) := by
  induction ps generalizing bs with
  | nil => exact hmem
  | cons a ps ih =>
    simp only [List.foldl_cons]
    apply ih
    · apply step_sound _ _ _ hmem
      rw [parity_left, hpar a (by simp)]
      simp
    · exact fun y hy => hpar y (by simp [hy])

theorem null_complete (p q : Nat) (ps : List Nat) (hq : q < 4096) (hnz : q ≠ 0)
    (hpar : ∀ a ∈ ps, parity a q = parity p q) :
    q ∈ (span (ps.foldl (fun b a => basisStep (a ^^^ p) b) initial)).erase 0 := by
  exact (List.mem_erase_of_ne hnz).2 (fold_sound p q ps initial (in_initial q hq) hpar)

theorem in_sublists (keep : Nat → Bool) (fs : List Nat) :
    fs.filter keep ∈ sublists fs := by
  induction fs with
  | nil => simp [sublists]
  | cons f fs ih =>
    by_cases h : keep f
    · simp only [List.filter_cons, h, ite_true, sublists, List.mem_append, List.mem_map]
      exact Or.inr ⟨fs.filter keep, ih, rfl⟩
    · simp only [List.filter_cons, h,
        sublists, List.mem_append]
      exact Or.inl ih

theorem possible_congr (p p' : Nat) {a b : List Nat}
    (he : ∀ f, f ∈ a ↔ f ∈ b)
    (hp : ∀ f ∈ a, parity p f = parity p' f) :
    possible p a = possible p' b := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [possible, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h f hf
    rw [← hp f ((he f).2 hf), h f ((he f).2 hf)]
  · intro h f hf
    rw [hp f hf, h f ((he f).1 hf)]

theorem reflected (q w : Nat) (ps fs gs : List Nat)
    (cs : List (List Nat × Nat × Bool))
    (hcert : cert (q, w, ps, fs, cs) = true)
    (hp : ∀ a ∈ ps, possible (ps.headD 0) gs a = true)
    (hg : gs ≠ [])
    (hsize : ∀ g ∈ gs, g < 4096 ∧ g ≠ 0) :
    ∃ a, ∃ m, invalid (ps.headD 0) gs a m = true := by
  have hsub : ∀ g ∈ gs, g ∈ fs := by
    intro g hm
    have hpar : ∀ a ∈ ps, parity a g = parity (ps.headD 0) g := by
      intro a ha
      have he := List.all_eq_true.mp (hp a ha) g hm
      exact (beq_iff_eq.mp he).symm
    obtain ⟨hlt, hnz⟩ := hsize g hm
    have hu : g ∈ nullForms ps := null_complete _ _ _ hlt hnz hpar
    simp only [cert, Bool.and_eq_true] at hcert
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hcert.1.1.2 _ hu)
  let bs := fs.filter gs.contains
  have hmem (g : Nat) : g ∈ bs ↔ g ∈ gs := by
    change g ∈ fs.filter gs.contains ↔ g ∈ gs
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨And.right, fun h => ⟨hsub g h, h⟩⟩
  have hn : bs.isEmpty = false := by
    cases gs with
    | nil => exact (hg rfl).elim
    | cons g rest =>
      have h := (hmem g).2 (by simp)
      cases hh : bs with
      | nil => simp [hh] at h
      | cons b bs => rfl
  have hb : bs ∈ sublists fs := in_sublists _ _
  simp only [cert, Bool.and_eq_true] at hcert
  have hcases := List.all_eq_true.mp hcert.1.2 bs hb
  simp only [hn, Bool.false_or, List.any_eq_true, beq_iff_eq] at hcases
  obtain ⟨⟨us,a,m⟩, hu, rfl⟩ := hcases
  have hit := List.all_eq_true.mp hcert.2 _ hu
  have equ := possible_congr (ps.headD 0) (ps.headD 0) hmem (by intros; rfl)
  exact ⟨a, m, by simpa only [invalid, equ] using hit⟩

abbrev Label := { x : (Nat × Bool) × List Nat // x ∈ axioms.zip critical }

def bad (a : Nat) (k : Label) : Prop := falseAxiom a k.val.1 = true

def point (k : Label) (a : Nat) : Prop := a ∈ k.val.2

def forced (q a : Nat) : Prop :=
  (∃ k, point k a ∧ ∃ b, point k b ∧ parity b q ≠ parity a q) ∨
  (∀ k, bad a k → ∀ b, point k b → parity b q ≠ parity a q)

theorem forced_of_shared {q a : Nat} (h : shared q a = true) : forced q a := by
  simp only [shared, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨g, hg, hs⟩ := List.any_eq_true.mp h
    have eq : (axioms.zip critical).map Prod.snd = critical := by decide +kernel
    have hg' : g ∈ (axioms.zip critical).map Prod.snd := by simpa only [eq] using hg
    obtain ⟨⟨ax, g'⟩, hax, hgg⟩ := List.mem_map.mp hg'
    change g' = g at hgg
    subst g'
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hs
    obtain ⟨⟨hopp, _⟩, hsa⟩ := hs
    obtain ⟨b, hb, hbne⟩ := List.any_eq_true.mp hopp
    exact Or.inl ⟨⟨(ax,g), hax⟩, hsa, b, hb, bne_iff_ne.mp hbne⟩
  · refine Or.inr ?_
    intro k hk b hb
    have h1 := List.all_eq_true.mp h k.val k.property
    have h2 : k.val.2.all (fun x => parity x q != parity a q) = true := by
      change falseAxiom a k.val.1 = true at hk
      simpa [hk] using h1
    exact bne_iff_ne.mp (List.all_eq_true.mp h2 b hb)

theorem invalid_contradiction {p : Nat} {forms : List Nat} {a : Nat} {m : Bool}
    (hi : invalid p forms a m = true)
    (hpos : possible p forms a = true → ∃ k, bad a k ∧ ∀ b, point k b →
      possible p forms b = true)
    (hneg : possible p forms a = false → ∃ k, bad a k ∧ ∃ b, point k b ∧
      possible p forms b = false) : False := by
  have both := hi
  simp only [invalid, Bool.and_eq_true, beq_iff_eq] at both
  obtain ⟨hav, hchecks⟩ := both
  cases m with
  | true =>
    obtain ⟨k, hk, hs⟩ := hpos hav
    have test := List.all_eq_true.mp hchecks k.val k.property
    change falseAxiom a k.val.1 = true at hk
    have pt : k.val.2.all (possible p forms) = true := List.all_eq_true.mpr hs
    simp [hk, pt] at test
  | false =>
    obtain ⟨k, hk, b, hb, hfb⟩ := hneg hav
    have test := List.all_eq_true.mp hchecks k.val k.property
    change falseAxiom a k.val.1 = true at hk
    have hx : k.val.2.all (possible p forms) = true := by
      simpa [hk] using test
    have hfb' := List.all_eq_true.mp hx b hb
    rw [hfb] at hfb'
    contradiction


theorem lookup_pivot (rows : List Row)
    (hvalid : rows.all packedCert = true)
    (hids : rows.map Prod.fst = (List.range 4095).map (1 + ·))
    (q : Nat) (hpos : 0 < q) (hlt : q < 4096) :
    ∃ k data fs cs, let xs := unpack k data; cert (q, xs.headD 0, xs, fs, cs) = true := by
  have hq : q ∈ rows.map Prod.fst := by
    rw [hids]
    exact List.mem_map.mpr ⟨q-1, List.mem_range.mpr (by omega), by omega⟩
  obtain ⟨⟨q',k,d,fs,cs⟩, hr, hh⟩ := List.mem_map.mp hq
  change q' = q at hh
  subst q'
  exact ⟨k,d,fs,cs,List.all_eq_true.mp hvalid _ hr⟩

theorem points_data : (axioms.zip critical).all (fun k => !k.2.isEmpty) = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem one_data : (axioms.zip critical).all (fun k => k.2.all (fun a =>
    ((axioms.zip critical).filter (fun j => falseAxiom a j.1)) == [k])) = true := by
  decide +kernel

theorem label_has_point (k : Label) : ∃ a, point k a := by
  have hh := List.all_eq_true.mp points_data k.val k.property
  change ∃ a, a ∈ k.val.2
  cases hk : k.val.2 with
  | nil => simp [hk] at hh
  | cons a as => exact ⟨a,by simp [hk]⟩

theorem label_point_unique {a : Nat} {k : Label} (ha : point k a)
    (j : Label) : bad a j ↔ j = k := by
  have chk := List.all_eq_true.mp one_data k.val k.property
  have equal := beq_iff_eq.mp (List.all_eq_true.mp chk a ha)
  have hj : j.val ∈ (axioms.zip critical).filter (fun s => falseAxiom a s.1) ↔ j.val = k.val := by
    simp [equal]
  simpa only [bad, List.mem_filter, j.property, true_and, Subtype.ext_iff] using hj
theorem forced_exists (rows : List Row)
    (valid : rows.all packedCert = true)
    (ids : rows.map Prod.fst = (List.range 4095).map (1 + ·))
    (q : Nat) (hq : 0 < q) (hlt : q < 4096) : ∃ a, forced q a := by
  obtain ⟨k,d,fs,cs,h⟩ := lookup_pivot rows valid ids q hq hlt
  dsimp only at h
  simp only [cert, Bool.and_eq_true] at h
  exact ⟨_, forced_of_shared h.1.1.1.1⟩

theorem no_shared (rows : List Row)
    (valid : rows.all packedCert = true)
    (ids : rows.map Prod.fst = (List.range 4095).map (1 + ·))
    (q p : Nat) (gs : List Nat) (hq : 0 < q) (hlt : q < 4096)
    (hn : gs ≠ []) (hgs : ∀ g ∈ gs, g < 4096 ∧ g ≠ 0)
    (hforced : ∀ a, forced q a → possible p gs a = true)
    (hpos : ∀ a, possible p gs a = true → ∃ k, bad a k ∧
      ∀ b, point k b → possible p gs b = true)
    (hneg : ∀ a, possible p gs a = false → ∃ k, bad a k ∧
      ∃ b, point k b ∧ possible p gs b = false) : False := by
  obtain ⟨k,d,fs,cs,h⟩ := lookup_pivot rows valid ids q hq hlt
  let ps := unpack k d
  change cert (q, ps.headD 0, ps, fs, cs) = true at h
  have hlo := h
  simp only [cert, Bool.and_eq_true] at hlo
  have hc := hforced _ (forced_of_shared hlo.1.1.1.1)
  have he := possible_congr (ps.headD 0) p (a := gs) (b := gs)
    (fun _ => Iff.rfl) (fun g hg => (beq_iff_eq.mp (List.all_eq_true.mp hc g hg)).symm)
  have hp : ∀ a ∈ ps, possible (ps.headD 0) gs a = true := by
    intro a ha
    rw [he]
    exact hforced a (forced_of_shared (List.all_eq_true.mp hlo.1.1.1.2 a ha))
  obtain ⟨a,m,hi⟩ := reflected q _ ps fs gs cs h hp hn hgs
  have hi' : invalid p gs a m = true := by simpa only [invalid, he] using hi
  exact invalid_contradiction hi' (hpos a) (hneg a)
def part0 : List Row := [
  (1, 11, 1066255041540124476318715609801907249796, [7, 585, 590], [([7], 3, false), ([585], 586, true), ([590], 586, true), ([7, 585], 586, true), ([7, 590], 586, true), ([585, 590], 586, true), ([7, 585, 590], 586, true)]),
  (2, 11, 1066397829703734184078500198450960802436, [7, 1170, 1173], [([7], 3, false), ([1170], 658, true), ([1173], 656, true), ([7, 1170], 658, true), ([7, 1173], 658, true), ([1170, 1173], 658, true), ([7, 1170, 1173], 658, true)]),
  (3, 13, 17911174321630290820334716344856493277137871492, [], []),
  (4, 11, 877647454302276130126159595891151872644, [7, 2339, 2340], [([7], 3, false), ([2339], 800, true), ([2340], 804, true), ([7, 2339], 804, true), ([7, 2340], 804, true), ([2339, 2340], 804, true), ([7, 2339, 2340], 804, true)]),
  (5, 13, 15101204392115617415743453998931337571113902724, [], []),
  (6, 13, 13339058960520087837857930102053485874399683204, [], []),
  (7, 12, 11168071437176765488021488908310350246465539, [7], [([7], 3, true)]),
  (8, 11, 1047650392859293071147631731676151874208, [56, 585, 625], [([56], 24, false), ([585], 586, true), ([625], 578, true), ([56, 585], 586, true), ([56, 625], 586, true), ([585, 625], 586, true), ([56, 585, 625], 586, true)]),
  (9, 12, 4291176009110083852190561987608671994053280, [585], [([585], 586, true)]),
  (10, 13, 24535110894392795539541480661900806328572510880, [], []),
  (11, 13, 24535110894392795539541480661900806328572510880, [], []),
  (12, 13, 24535110894392795539541480661900806328572510880, [], []),
  (13, 13, 24535110894392795539541480661900806328572510880, [], []),
  (14, 13, 13340136804730422722490550089031328852570342048, [], []),
  (15, 13, 12982187129042371101592383884676325973343404704, [], []),
  (16, 11, 1047795452652778387894503802417349460640, [56, 1170, 1194], [([56], 24, false), ([1170], 658, true), ([1194], 642, true), ([56, 1170], 658, true), ([56, 1194], 658, true), ([1170, 1194], 658, true), ([56, 1170, 1194], 658, true)]),
  (17, 13, 14722783601204235473123159809937283211255153312, [], []),
  (18, 12, 4291770174024199709585749989364617308078752, [1170], [([1170], 658, true)]),
  (19, 13, 14722783601204235473123159809937283211255153312, [], []),
  (20, 13, 14722783601204235473123159809937283211255153312, [], []),
  (21, 13, 25984659926462200159598697537624705771775263392, [], []),
  (22, 13, 14722783601204235473123159809937283211255153312, [], []),
  (23, 13, 14588205566178975007301105084758245598494261920, [], []),
  (24, 13, 17755031012231488144257906676302124042794631840, [], []),
  (25, 13, 17888868744358320167463874609369394999886676640, [], []),
  (26, 13, 17888868744358320167463874609369394999886676640, [], []),
  (27, 13, 51629896229735152980607416355886365958435046048, [], []),
  (28, 13, 51942106662514581704588916411703443019518771872, [], []),
  (29, 13, 17888868744358320167463874609369394999886676640, [], []),
  (30, 13, 17888868744358320167463874609369394999886676640, [], []),
  (31, 13, 17442820579452059420276406620485046981710906016, [], []),
  (32, 11, 896263461133297978383469797545390178976, [56, 2332, 2340], [([56], 24, false), ([2332], 772, true), ([2340], 804, true), ([56, 2332], 804, true), ([56, 2340], 804, true), ([2332, 2340], 804, true), ([56, 2332, 2340], 804, true)]),
  (33, 13, 17888868744358320167463874609369394999886676640, [], []),
  (34, 13, 17888868744358320167463874609369394999886676640, [], []),
  (35, 13, 51629896229735152980607416355886365958435046048, [], []),
  (36, 12, 3671095136760407952228554705409072090383008, [2340], [([2340], 804, true)]),
  (37, 13, 17888868744358320167463874609369394999886676640, [], []),
  (38, 13, 17888868744358320167463874609369394999886676640, [], []),
  (39, 13, 17443397698346357331910440503819251260597535392, [], []),
  (40, 13, 15257423924778240162102131536711577142163473056, [], []),
  (41, 13, 14722783601204235473123159809937283211255153312, [], []),
  (42, 13, 26609080792021057607561697649258859893942715040, [], []),
  (43, 13, 14722783601204235473123159809937283211255153312, [], []),
  (44, 13, 14722783601204235473123159809937283211255153312, [], []),
  (45, 13, 25984659926462200159598697537624705771775263392, [], []),
  (46, 13, 14722783601204235473123159809937283211255153312, [], []),
  (47, 13, 15212669987880798335387428508342150986992779936, [], []),
  (48, 13, 13963670365599772330529064532383923661010174624, [], []),
  (49, 13, 13964557670289280170453550200665482974737793696, [], []),
  (50, 13, 24535110894392795539541480661900806328572510880, [], []),
  (51, 13, 24535110894392795539541480661900806328572510880, [], []),
  (52, 13, 24535110894392795539541480661900806328572510880, [], []),
  (53, 13, 24535110894392795539541480661900806328572510880, [], []),
  (54, 13, 13340136804730422722490550089031328852570342048, [], []),
  (55, 13, 13941222618418731861971312636280864775636845216, [], []),
  (56, 12, 11282434233066666119516534650438799325237272, [56], [([56], 24, true)]),
  (57, 13, 13918932780860591389692012917079532356469006980, [], []),
  (58, 13, 15368960336480494738858098796033528433053016708, [], []),
  (59, 13, 17911174321630290820334716344856493277137871492, [], []),
  (60, 13, 18224152431429493181489789773787936407306642052, [], []),
  (61, 13, 15101204392115617415743453998931337571113902724, [], []),
  (62, 13, 13339058960520087837857930102053485874399683204, [], []),
  (63, 13, 45922870290646425451894909792672734426312003595, [], []),
  (64, 11, 898813203413726085252523256677699486368, [448, 585, 905], [([448], 192, false), ([585], 586, true), ([905], 522, true), ([448, 585], 586, true), ([448, 905], 586, true), ([585, 905], 586, true), ([448, 585, 905], 586, true)]),
  (65, 12, 3681538881123290036241959917481694757716640, [585], [([585], 586, true)]),
  (66, 13, 24534501257264808745725532059830679351336174240, [], []),
  (67, 13, 24534501257264808745725532059830679351336174240, [], []),
  (68, 13, 24534501257264808745725532059830679351336174240, [], []),
  (69, 13, 24534501257264808745725532059830679351336174240, [], []),
  (70, 13, 14588368898720150824600601710229510119668908704, [], []),
  (71, 13, 11733040356086705599236134582651283866238648992, [], []),
  (72, 12, 3681538881123290036241959917481694757716640, [585], [([585], 586, true)]),
  (73, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (74, 13, 24534501257264808745725532059830679351336174240, [], []),
  (75, 13, 24534501257264808745725532059830679351336174240, [], []),
  (76, 13, 24534501257264808745725532059830679351336174240, [], []),
  (77, 13, 24534501257264808745725532059830679351336174240, [], []),
  (78, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (79, 13, 14744474115109865186591351738138048650210771616, [], []),
  (80, 13, 25002816906433951831697782143556294942961762976, [], []),
  (81, 13, 25002816906433951831697782143556294942961762976, [], []),
  (82, 13, 25002816906433951831697782143556294942961762976, [], []),
  (83, 13, 25002816906433951831697782143556294942961762976, [], []),
  (84, 13, 25002816906433951831697782143556294942961762976, [], []),
  (85, 13, 25002816906433951831697782143556294942961762976, [], []),
  (86, 13, 25002816906433951831697782143556294942961762976, [], []),
  (87, 13, 25002816906433951831697782143556294942961762976, [], []),
  (88, 13, 25002816906433951831697782143556294942961762976, [], []),
  (89, 13, 25002816906433951831697782143556294942961762976, [], []),
  (90, 13, 25002816906433951831697782143556294942961762976, [], []),
  (91, 13, 25002816906433951831697782143556294942961762976, [], []),
  (92, 13, 25002816906433951831697782143556294942961762976, [], []),
  (93, 13, 25002816906433951831697782143556294942961762976, [], []),
  (94, 13, 25002816906433951831697782143556294942961762976, [], []),
  (95, 13, 25002816906433951831697782143556294942961762976, [], []),
  (96, 13, 25002816906433951831697782143556294942961762976, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part0_checked : part0.all packedCert = true := by decide +kernel

def part1 : List Row := [
  (97, 13, 25002816906433951831697782143556294942961762976, [], []),
  (98, 13, 25002816906433951831697782143556294942961762976, [], []),
  (99, 13, 25002816906433951831697782143556294942961762976, [], []),
  (100, 13, 25002816906433951831697782143556294942961762976, [], []),
  (101, 13, 25002816906433951831697782143556294942961762976, [], []),
  (102, 13, 25002816906433951831697782143556294942961762976, [], []),
  (103, 13, 25002816906433951831697782143556294942961762976, [], []),
  (104, 13, 25002816906433951831697782143556294942961762976, [], []),
  (105, 13, 25002816906433951831697782143556294942961762976, [], []),
  (106, 13, 25002816906433951831697782143556294942961762976, [], []),
  (107, 13, 25002816906433951831697782143556294942961762976, [], []),
  (108, 13, 25002816906433951831697782143556294942961762976, [], []),
  (109, 13, 25002816906433951831697782143556294942961762976, [], []),
  (110, 13, 25002816906433951831697782143556294942961762976, [], []),
  (111, 13, 25002816906433951831697782143556294942961762976, [], []),
  (112, 13, 15368894980668722634554351849772202772378223264, [], []),
  (113, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (114, 13, 24534501257264808745725532059830679351336174240, [], []),
  (115, 13, 24534501257264808745725532059830679351336174240, [], []),
  (116, 13, 24534501257264808745725532059830679351336174240, [], []),
  (117, 13, 24534501257264808745725532059830679351336174240, [], []),
  (118, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (119, 13, 14744474115109865186591351738138048650210771616, [], []),
  (120, 13, 12045327012116324613433450434380425643401740960, [], []),
  (121, 13, 15212789764279008272563601821863664241836360352, [], []),
  (122, 13, 24534501257264808745725532059830679351336174240, [], []),
  (123, 13, 24534501257264808745725532059830679351336174240, [], []),
  (124, 13, 24534501257264808745725532059830679351336174240, [], []),
  (125, 13, 24534501257264808745725532059830679351336174240, [], []),
  (126, 13, 14588368898720150824600601710229510119668908704, [], []),
  (127, 13, 11733040356086705599236134582651283866238648992, [], []),
  (128, 11, 898976436246216273896095184156049343136, [448, 1170, 1362], [([448], 192, false), ([1170], 658, true), ([1362], 530, true), ([448, 1170], 658, true), ([448, 1362], 658, true), ([1170, 1362], 658, true), ([448, 1170, 1362], 658, true)]),
  (129, 13, 14722174038513016443262500090480351609718112928, [], []),
  (130, 12, 3682207482805169848926030532433015771038368, [1170], [([1170], 658, true)]),
  (131, 13, 14722174038513016443262500090480351609718112928, [], []),
  (132, 13, 14722174038513016443262500090480351609718112928, [], []),
  (133, 13, 24735208632653266233812037594899465925903319712, [], []),
  (134, 13, 14722174038513016443262500090480351609718112928, [], []),
  (135, 13, 13338753900240721383086464495784801364224311968, [], []),
  (136, 13, 15034384471292445167244000146297428670801838752, [], []),
  (137, 13, 15034384471292445167244000146297428670801838752, [], []),
  (138, 13, 15034384471292445167244000146297428670801838752, [], []),
  (139, 13, 15034384471292445167244000146297428670801838752, [], []),
  (140, 13, 15034384471292445167244000146297428670801838752, [], []),
  (141, 13, 15034384471292445167244000146297428670801838752, [], []),
  (142, 13, 15034384471292445167244000146297428670801838752, [], []),
  (143, 13, 15034384471292445167244000146297428670801838752, [], []),
  (144, 12, 3682207482805169848926030532433015771038368, [1170], [([1170], 658, true)]),
  (145, 13, 14722174038513016443262500090480351609718112928, [], []),
  (146, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (147, 13, 14722174038513016443262500090480351609718112928, [], []),
  (148, 13, 14722174038513016443262500090480351609718112928, [], []),
  (149, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (150, 13, 14722174038513016443262500090480351609718112928, [], []),
  (151, 13, 15056685216490975790385535864570077032307819168, [], []),
  (152, 13, 15034384471292445167244000146297428670801838752, [], []),
  (153, 13, 15034384471292445167244000146297428670801838752, [], []),
  (154, 13, 15034384471292445167244000146297428670801838752, [], []),
  (155, 13, 15034384471292445167244000146297428670801838752, [], []),
  (156, 13, 15034384471292445167244000146297428670801838752, [], []),
  (157, 13, 15034384471292445167244000146297428670801838752, [], []),
  (158, 13, 15034384471292445167244000146297428670801838752, [], []),
  (159, 13, 15034384471292445167244000146297428670801838752, [], []),
  (160, 13, 15034384471292445167244000146297428670801838752, [], []),
  (161, 13, 15034384471292445167244000146297428670801838752, [], []),
  (162, 13, 15034384471292445167244000146297428670801838752, [], []),
  (163, 13, 15034384471292445167244000146297428670801838752, [], []),
  (164, 13, 15034384471292445167244000146297428670801838752, [], []),
  (165, 13, 15034384471292445167244000146297428670801838752, [], []),
  (166, 13, 15034384471292445167244000146297428670801838752, [], []),
  (167, 13, 15034384471292445167244000146297428670801838752, [], []),
  (168, 13, 25203524281822409319784287678625081517528908448, [], []),
  (169, 13, 14722174038513016443262500090480351609718112928, [], []),
  (170, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (171, 13, 14722174038513016443262500090480351609718112928, [], []),
  (172, 13, 14722174038513016443262500090480351609718112928, [], []),
  (173, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (174, 13, 14722174038513016443262500090480351609718112928, [], []),
  (175, 13, 15056685216490975790385535864570077032307819168, [], []),
  (176, 13, 15034384471292445167244000146297428670801838752, [], []),
  (177, 13, 15034384471292445167244000146297428670801838752, [], []),
  (178, 13, 15034384471292445167244000146297428670801838752, [], []),
  (179, 13, 15034384471292445167244000146297428670801838752, [], []),
  (180, 13, 15034384471292445167244000146297428670801838752, [], []),
  (181, 13, 15034384471292445167244000146297428670801838752, [], []),
  (182, 13, 15034384471292445167244000146297428670801838752, [], []),
  (183, 13, 15034384471292445167244000146297428670801838752, [], []),
  (184, 13, 13963327212299959411481096199243084918550495904, [], []),
  (185, 13, 14722174038513016443262500090480351609718112928, [], []),
  (186, 13, 14900580000101261428394785836661538501765956256, [], []),
  (187, 13, 14722174038513016443262500090480351609718112928, [], []),
  (188, 13, 14722174038513016443262500090480351609718112928, [], []),
  (189, 13, 14900580000101261428394785836661538501765956256, [], []),
  (190, 13, 14722174038513016443262500090480351609718112928, [], []),
  (191, 13, 13338753900240721383086464495784801364224311968, [], []),
  (192, 13, 16506494323042589058454211168726237904274260640, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part1_checked : part1.all packedCert = true := by decide +kernel

def part2 : List Row := [
  (193, 13, 17889478753670145781056267624505498855619494560, [], []),
  (194, 13, 17889478753670145781056267624505498855619494560, [], []),
  (195, 13, 47883981045693833906421808701217545081163154080, [], []),
  (196, 13, 50693874940708692422255309203571238630916686496, [], []),
  (197, 13, 17889478753670145781056267624505498855619494560, [], []),
  (198, 13, 17889478753670145781056267624505498855619494560, [], []),
  (199, 13, 16149083502900318236493944137054784208126411424, [], []),
  (200, 13, 17577268320890717057074767568688421794535768736, [], []),
  (201, 13, 17577268320890717057074767568688421794535768736, [], []),
  (202, 13, 17577268320890717057074767568688421794535768736, [], []),
  (203, 13, 17577268320890717057074767568688421794535768736, [], []),
  (204, 13, 17577268320890717057074767568688421794535768736, [], []),
  (205, 13, 17577268320890717057074767568688421794535768736, [], []),
  (206, 13, 17577268320890717057074767568688421794535768736, [], []),
  (207, 13, 17577268320890717057074767568688421794535768736, [], []),
  (208, 13, 17577268320890717057074767568688421794535768736, [], []),
  (209, 13, 17577268320890717057074767568688421794535768736, [], []),
  (210, 13, 17577268320890717057074767568688421794535768736, [], []),
  (211, 13, 17577268320890717057074767568688421794535768736, [], []),
  (212, 13, 17577268320890717057074767568688421794535768736, [], []),
  (213, 13, 17577268320890717057074767568688421794535768736, [], []),
  (214, 13, 17577268320890717057074767568688421794535768736, [], []),
  (215, 13, 17577268320890717057074767568688421794535768736, [], []),
  (216, 13, 47727875829304119544431058673309006550621291168, [], []),
  (217, 13, 17889478753670145781056267624505498855619494560, [], []),
  (218, 13, 17889478753670145781056267624505498855619494560, [], []),
  (219, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (220, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (221, 13, 17889478753670145781056267624505498855619494560, [], []),
  (222, 13, 17889478753670145781056267624505498855619494560, [], []),
  (223, 13, 15101885603853817888364302840424453667371942560, [], []),
  (224, 13, 50225559291539549336283059119845623039291097760, [], []),
  (225, 13, 17889478753670145781056267624505498855619494560, [], []),
  (226, 13, 17889478753670145781056267624505498855619494560, [], []),
  (227, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (228, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (229, 13, 17889478753670145781056267624505498855619494560, [], []),
  (230, 13, 17889478753670145781056267624505498855619494560, [], []),
  (231, 13, 15101885603853817888364302840424453667371942560, [], []),
  (232, 13, 17577268320890717057074767568688421794535768736, [], []),
  (233, 13, 17577268320890717057074767568688421794535768736, [], []),
  (234, 13, 17577268320890717057074767568688421794535768736, [], []),
  (235, 13, 17577268320890717057074767568688421794535768736, [], []),
  (236, 13, 17577268320890717057074767568688421794535768736, [], []),
  (237, 13, 17577268320890717057074767568688421794535768736, [], []),
  (238, 13, 17577268320890717057074767568688421794535768736, [], []),
  (239, 13, 17577268320890717057074767568688421794535768736, [], []),
  (240, 13, 17577268320890717057074767568688421794535768736, [], []),
  (241, 13, 17577268320890717057074767568688421794535768736, [], []),
  (242, 13, 17577268320890717057074767568688421794535768736, [], []),
  (243, 13, 17577268320890717057074767568688421794535768736, [], []),
  (244, 13, 17577268320890717057074767568688421794535768736, [], []),
  (245, 13, 17577268320890717057074767568688421794535768736, [], []),
  (246, 13, 17577268320890717057074767568688421794535768736, [], []),
  (247, 13, 17577268320890717057074767568688421794535768736, [], []),
  (248, 13, 16149159726150508526709759932966848924205777568, [], []),
  (249, 13, 17889478753670145781056267624505498855619494560, [], []),
  (250, 13, 17889478753670145781056267624505498855619494560, [], []),
  (251, 13, 15257990820243532250355052868332992197913805472, [], []),
  (252, 13, 15257990820243532250355052868332992197913805472, [], []),
  (253, 13, 17889478753670145781056267624505498855619494560, [], []),
  (254, 13, 17889478753670145781056267624505498855619494560, [], []),
  (255, 13, 16149083502900318236493944137054784208126411424, [], []),
  (256, 11, 1045191515782557019915513960786887246496, [448, 2276, 2340], [([448], 192, false), ([2276], 548, true), ([2340], 804, true), ([448, 2276], 804, true), ([448, 2340], 804, true), ([2276, 2340], 804, true), ([448, 2276, 2340], 804, true)]),
  (257, 13, 17889478753670145781056267624505498855619494560, [], []),
  (258, 13, 17889478753670145781056267624505498855619494560, [], []),
  (259, 13, 47883981045693833906421808701217545081163154080, [], []),
  (260, 12, 4281104448586021544621569841512927823200928, [2340], [([2340], 804, true)]),
  (261, 13, 17889478753670145781056267624505498855619494560, [], []),
  (262, 13, 17889478753670145781056267624505498855619494560, [], []),
  (263, 13, 13695653081918222649938428631465454311820034720, [], []),
  (264, 13, 17577268320890717057074767568688421794535768736, [], []),
  (265, 13, 17577268320890717057074767568688421794535768736, [], []),
  (266, 13, 17577268320890717057074767568688421794535768736, [], []),
  (267, 13, 17577268320890717057074767568688421794535768736, [], []),
  (268, 13, 17577268320890717057074767568688421794535768736, [], []),
  (269, 13, 17577268320890717057074767568688421794535768736, [], []),
  (270, 13, 17577268320890717057074767568688421794535768736, [], []),
  (271, 13, 17577268320890717057074767568688421794535768736, [], []),
  (272, 13, 17577268320890717057074767568688421794535768736, [], []),
  (273, 13, 17577268320890717057074767568688421794535768736, [], []),
  (274, 13, 17577268320890717057074767568688421794535768736, [], []),
  (275, 13, 17577268320890717057074767568688421794535768736, [], []),
  (276, 13, 17577268320890717057074767568688421794535768736, [], []),
  (277, 13, 17577268320890717057074767568688421794535768736, [], []),
  (278, 13, 17577268320890717057074767568688421794535768736, [], []),
  (279, 13, 17577268320890717057074767568688421794535768736, [], []),
  (280, 13, 47727875829304119544431058673309006550621291168, [], []),
  (281, 13, 17889478753670145781056267624505498855619494560, [], []),
  (282, 13, 17889478753670145781056267624505498855619494560, [], []),
  (283, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (284, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (285, 13, 17889478753670145781056267624505498855619494560, [], []),
  (286, 13, 17889478753670145781056267624505498855619494560, [], []),
  (287, 13, 15101885603853817888364302840424453667371942560, [], []),
  (288, 12, 4281104448586021544621569841512927823200928, [2340], [([2340], 804, true)])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part2_checked : part2.all packedCert = true := by decide +kernel

def part3 : List Row := [
  (289, 13, 17889478753670145781056267624505498855619494560, [], []),
  (290, 13, 17889478753670145781056267624505498855619494560, [], []),
  (291, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (292, 12, 9953623859254884953203086455367051225662112, [2340], [([2340], 804, true)]),
  (293, 13, 17889478753670145781056267624505498855619494560, [], []),
  (294, 13, 17889478753670145781056267624505498855619494560, [], []),
  (295, 13, 15101885603853817888364302840424453667371942560, [], []),
  (296, 13, 17577268320890717057074767568688421794535768736, [], []),
  (297, 13, 17577268320890717057074767568688421794535768736, [], []),
  (298, 13, 17577268320890717057074767568688421794535768736, [], []),
  (299, 13, 17577268320890717057074767568688421794535768736, [], []),
  (300, 13, 17577268320890717057074767568688421794535768736, [], []),
  (301, 13, 17577268320890717057074767568688421794535768736, [], []),
  (302, 13, 17577268320890717057074767568688421794535768736, [], []),
  (303, 13, 17577268320890717057074767568688421794535768736, [], []),
  (304, 13, 17577268320890717057074767568688421794535768736, [], []),
  (305, 13, 17577268320890717057074767568688421794535768736, [], []),
  (306, 13, 17577268320890717057074767568688421794535768736, [], []),
  (307, 13, 17577268320890717057074767568688421794535768736, [], []),
  (308, 13, 17577268320890717057074767568688421794535768736, [], []),
  (309, 13, 17577268320890717057074767568688421794535768736, [], []),
  (310, 13, 17577268320890717057074767568688421794535768736, [], []),
  (311, 13, 17577268320890717057074767568688421794535768736, [], []),
  (312, 13, 14007939737947841664135744483194596088983126688, [], []),
  (313, 13, 17889478753670145781056267624505498855619494560, [], []),
  (314, 13, 17889478753670145781056267624505498855619494560, [], []),
  (315, 13, 15257990820243532250355052868332992197913805472, [], []),
  (316, 13, 15257990820243532250355052868332992197913805472, [], []),
  (317, 13, 17889478753670145781056267624505498855619494560, [], []),
  (318, 13, 17889478753670145781056267624505498855619494560, [], []),
  (319, 13, 13695653081918222649938428631465454311820034720, [], []),
  (320, 13, 19004863648314651925907807759052660206820459168, [], []),
  (321, 13, 14722174038513016443262500090480351609718112928, [], []),
  (322, 13, 30354996422682983265479038599606853025410384544, [], []),
  (323, 13, 14722174038513016443262500090480351609718112928, [], []),
  (324, 13, 14722174038513016443262500090480351609718112928, [], []),
  (325, 13, 24735208632653266233812037594899465925903319712, [], []),
  (326, 13, 14722174038513016443262500090480351609718112928, [], []),
  (327, 13, 18958890139414165455740051996090198594379907744, [], []),
  (328, 13, 15034384471292445167244000146297428670801838752, [], []),
  (329, 13, 15034384471292445167244000146297428670801838752, [], []),
  (330, 13, 15034384471292445167244000146297428670801838752, [], []),
  (331, 13, 15034384471292445167244000146297428670801838752, [], []),
  (332, 13, 15034384471292445167244000146297428670801838752, [], []),
  (333, 13, 15034384471292445167244000146297428670801838752, [], []),
  (334, 13, 15034384471292445167244000146297428670801838752, [], []),
  (335, 13, 15034384471292445167244000146297428670801838752, [], []),
  (336, 13, 30198891206293268903488288571698314494868521632, [], []),
  (337, 13, 14722174038513016443262500090480351609718112928, [], []),
  (338, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (339, 13, 14722174038513016443262500090480351609718112928, [], []),
  (340, 13, 14722174038513016443262500090480351609718112928, [], []),
  (341, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (342, 13, 14722174038513016443262500090480351609718112928, [], []),
  (343, 13, 15056685216490975790385535864570077032307819168, [], []),
  (344, 13, 15034384471292445167244000146297428670801838752, [], []),
  (345, 13, 15034384471292445167244000146297428670801838752, [], []),
  (346, 13, 15034384471292445167244000146297428670801838752, [], []),
  (347, 13, 15034384471292445167244000146297428670801838752, [], []),
  (348, 13, 15034384471292445167244000146297428670801838752, [], []),
  (349, 13, 15034384471292445167244000146297428670801838752, [], []),
  (350, 13, 15034384471292445167244000146297428670801838752, [], []),
  (351, 13, 15034384471292445167244000146297428670801838752, [], []),
  (352, 13, 15034384471292445167244000146297428670801838752, [], []),
  (353, 13, 15034384471292445167244000146297428670801838752, [], []),
  (354, 13, 15034384471292445167244000146297428670801838752, [], []),
  (355, 13, 15034384471292445167244000146297428670801838752, [], []),
  (356, 13, 15034384471292445167244000146297428670801838752, [], []),
  (357, 13, 15034384471292445167244000146297428670801838752, [], []),
  (358, 13, 15034384471292445167244000146297428670801838752, [], []),
  (359, 13, 15034384471292445167244000146297428670801838752, [], []),
  (360, 13, 25203524281822409319784287678625081517528908448, [], []),
  (361, 13, 14722174038513016443262500090480351609718112928, [], []),
  (362, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (363, 13, 14722174038513016443262500090480351609718112928, [], []),
  (364, 13, 14722174038513016443262500090480351609718112928, [], []),
  (365, 12, 14733764334680692147190553521791900222292640, [1170], [([1170], 658, true)]),
  (366, 13, 14722174038513016443262500090480351609718112928, [], []),
  (367, 13, 15056685216490975790385535864570077032307819168, [], []),
  (368, 13, 15034384471292445167244000146297428670801838752, [], []),
  (369, 13, 15034384471292445167244000146297428670801838752, [], []),
  (370, 13, 15034384471292445167244000146297428670801838752, [], []),
  (371, 13, 15034384471292445167244000146297428670801838752, [], []),
  (372, 13, 15034384471292445167244000146297428670801838752, [], []),
  (373, 13, 15034384471292445167244000146297428670801838752, [], []),
  (374, 13, 15034384471292445167244000146297428670801838752, [], []),
  (375, 13, 15034384471292445167244000146297428670801838752, [], []),
  (376, 13, 18959042585914546036171683587914328026538640032, [], []),
  (377, 13, 14722174038513016443262500090480351609718112928, [], []),
  (378, 13, 14900580000101261428394785836661538501765956256, [], []),
  (379, 13, 14722174038513016443262500090480351609718112928, [], []),
  (380, 13, 14722174038513016443262500090480351609718112928, [], []),
  (381, 13, 14900580000101261428394785836661538501765956256, [], []),
  (382, 13, 14722174038513016443262500090480351609718112928, [], []),
  (383, 13, 18958890139414165455740051996090198594379907744, [], []),
  (384, 13, 20209403337354963168908395671858284205819626144, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part3_checked : part3.all packedCert = true := by decide +kernel

def part4 : List Row := [
  (385, 13, 20208156688749867856267602714936897219175973536, [], []),
  (386, 13, 24534501257264808745725532059830679351336174240, [], []),
  (387, 13, 24534501257264808745725532059830679351336174240, [], []),
  (388, 13, 24534501257264808745725532059830679351336174240, [], []),
  (389, 13, 24534501257264808745725532059830679351336174240, [], []),
  (390, 13, 14588368898720150824600601710229510119668908704, [], []),
  (391, 13, 20185736018170878056897591041162189863176438432, [], []),
  (392, 13, 20364261905139582218258352742845435749717836448, [], []),
  (393, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (394, 13, 24534501257264808745725532059830679351336174240, [], []),
  (395, 13, 24534501257264808745725532059830679351336174240, [], []),
  (396, 13, 24534501257264808745725532059830679351336174240, [], []),
  (397, 13, 24534501257264808745725532059830679351336174240, [], []),
  (398, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (399, 13, 14744474115109865186591351738138048650210771616, [], []),
  (400, 13, 25002816906433951831697782143556294942961762976, [], []),
  (401, 13, 25002816906433951831697782143556294942961762976, [], []),
  (402, 13, 25002816906433951831697782143556294942961762976, [], []),
  (403, 13, 25002816906433951831697782143556294942961762976, [], []),
  (404, 13, 25002816906433951831697782143556294942961762976, [], []),
  (405, 13, 25002816906433951831697782143556294942961762976, [], []),
  (406, 13, 25002816906433951831697782143556294942961762976, [], []),
  (407, 13, 25002816906433951831697782143556294942961762976, [], []),
  (408, 13, 25002816906433951831697782143556294942961762976, [], []),
  (409, 13, 25002816906433951831697782143556294942961762976, [], []),
  (410, 13, 25002816906433951831697782143556294942961762976, [], []),
  (411, 13, 25002816906433951831697782143556294942961762976, [], []),
  (412, 13, 25002816906433951831697782143556294942961762976, [], []),
  (413, 13, 25002816906433951831697782143556294942961762976, [], []),
  (414, 13, 25002816906433951831697782143556294942961762976, [], []),
  (415, 13, 25002816906433951831697782143556294942961762976, [], []),
  (416, 13, 25002816906433951831697782143556294942961762976, [], []),
  (417, 13, 25002816906433951831697782143556294942961762976, [], []),
  (418, 13, 25002816906433951831697782143556294942961762976, [], []),
  (419, 13, 25002816906433951831697782143556294942961762976, [], []),
  (420, 13, 25002816906433951831697782143556294942961762976, [], []),
  (421, 13, 25002816906433951831697782143556294942961762976, [], []),
  (422, 13, 25002816906433951831697782143556294942961762976, [], []),
  (423, 13, 25002816906433951831697782143556294942961762976, [], []),
  (424, 13, 25002816906433951831697782143556294942961762976, [], []),
  (425, 13, 25002816906433951831697782143556294942961762976, [], []),
  (426, 13, 25002816906433951831697782143556294942961762976, [], []),
  (427, 13, 25002816906433951831697782143556294942961762976, [], []),
  (428, 13, 25002816906433951831697782143556294942961762976, [], []),
  (429, 13, 25002816906433951831697782143556294942961762976, [], []),
  (430, 13, 25002816906433951831697782143556294942961762976, [], []),
  (431, 13, 25002816906433951831697782143556294942961762976, [], []),
  (432, 13, 15368894980668722634554351849772202772378223264, [], []),
  (433, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (434, 13, 24534501257264808745725532059830679351336174240, [], []),
  (435, 13, 24534501257264808745725532059830679351336174240, [], []),
  (436, 13, 24534501257264808745725532059830679351336174240, [], []),
  (437, 13, 24534501257264808745725532059830679351336174240, [], []),
  (438, 12, 17123907516700531424368653192465161789702816, [585], [([585], 586, true)]),
  (439, 13, 14744474115109865186591351738138048650210771616, [], []),
  (440, 13, 20185812241421068347113406837074254579255804576, [], []),
  (441, 13, 15212789764279008272563601821863664241836360352, [], []),
  (442, 13, 24534501257264808745725532059830679351336174240, [], []),
  (443, 13, 24534501257264808745725532059830679351336174240, [], []),
  (444, 13, 24534501257264808745725532059830679351336174240, [], []),
  (445, 13, 24534501257264808745725532059830679351336174240, [], []),
  (446, 13, 14588368898720150824600601710229510119668908704, [], []),
  (447, 13, 20185736018170878056897591041162189863176438432, [], []),
  (448, 12, 12197336600180800568924936503763233823002816, [448], [([448], 192, true)]),
  (449, 13, 16417226029097543503270539730912666573773742724, [], []),
  (450, 13, 20365546832954398966015152423699796867662488196, [], []),
  (451, 13, 17911174321630290820334716344856493277137871492, [], []),
  (452, 13, 20722445679666445295068316587621070624611377796, [], []),
  (453, 13, 15101204392115617415743453998931337571113902724, [], []),
  (454, 13, 13339058960520087837857930102053485874399683204, [], []),
  (455, 13, 45855951640415935594531956602734002971366150211, [], []),
  (456, 13, 15792767033308942229368226550238601967811232416, [], []),
  (457, 13, 16506842622921771208588622083747396186419561120, [], []),
  (458, 13, 24535110894392795539541480661900806328572510880, [], []),
  (459, 13, 24535110894392795539541480661900806328572510880, [], []),
  (460, 13, 24535110894392795539541480661900806328572510880, [], []),
  (461, 13, 24535110894392795539541480661900806328572510880, [], []),
  (462, 13, 13340136804730422722490550089031328852570342048, [], []),
  (463, 13, 12982187129042371101592383884676325973343404704, [], []),
  (464, 13, 20209365374712117262852790415882797587429917344, [], []),
  (465, 13, 14722783601204235473123159809937283211255153312, [], []),
  (466, 13, 16150031293910195354181445779386778347637899936, [], []),
  (467, 13, 14722783601204235473123159809937283211255153312, [], []),
  (468, 13, 14722783601204235473123159809937283211255153312, [], []),
  (469, 13, 16150031293910195354181445779386778347637899936, [], []),
  (470, 13, 14722783601204235473123159809937283211255153312, [], []),
  (471, 13, 14588205566178975007301105084758245598494261920, [], []),
  (472, 13, 17755031012231488144257906676302124042794631840, [], []),
  (473, 13, 17888868744358320167463874609369394999886676640, [], []),
  (474, 13, 17888868744358320167463874609369394999886676640, [], []),
  (475, 13, 19003906004284851324540660523001813075185697440, [], []),
  (476, 13, 19003906004284851324540660523001813075185697440, [], []),
  (477, 13, 17888868744358320167463874609369394999886676640, [], []),
  (478, 13, 17888868744358320167463874609369394999886676640, [], []),
  (479, 13, 17442820579452059420276406620485046981710906016, [], []),
  (480, 13, 20253977602612928459686283169381527255065363104, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part4_checked : part4.all packedCert = true := by decide +kernel

def part5 : List Row := [
  (481, 13, 17888868744358320167463874609369394999886676640, [], []),
  (482, 13, 17888868744358320167463874609369394999886676640, [], []),
  (483, 13, 19003906004284851324540660523001813075185697440, [], []),
  (484, 13, 19003906004284851324540660523001813075185697440, [], []),
  (485, 13, 17888868744358320167463874609369394999886676640, [], []),
  (486, 13, 17888868744358320167463874609369394999886676640, [], []),
  (487, 13, 17443397698346357331910440503819251260597535392, [], []),
  (488, 13, 15257423924778240162102131536711577142163473056, [], []),
  (489, 13, 14722783601204235473123159809937283211255153312, [], []),
  (490, 13, 16150031293910195354181445779386778347637899936, [], []),
  (491, 13, 14722783601204235473123159809937283211255153312, [], []),
  (492, 13, 14722783601204235473123159809937283211255153312, [], []),
  (493, 13, 16150031293910195354181445779386778347637899936, [], []),
  (494, 13, 14722783601204235473123159809937283211255153312, [], []),
  (495, 13, 15212669987880798335387428508342150986992779936, [], []),
  (496, 13, 13963670365599772330529064532383923661010174624, [], []),
  (497, 13, 13964557670289280170453550200665482974737793696, [], []),
  (498, 13, 24535110894392795539541480661900806328572510880, [], []),
  (499, 13, 24535110894392795539541480661900806328572510880, [], []),
  (500, 13, 24535110894392795539541480661900806328572510880, [], []),
  (501, 13, 24535110894392795539541480661900806328572510880, [], []),
  (502, 13, 13340136804730422722490550089031328852570342048, [], []),
  (503, 13, 13941222618418731861971312636280864775636845216, [], []),
  (504, 13, 45699808340310372403092225709712376061889974360, [], []),
  (505, 13, 13918932780860591389692012917079532356469006980, [], []),
  (506, 13, 15368960336480494738858098796033528433053016708, [], []),
  (507, 13, 17911174321630290820334716344856493277137871492, [], []),
  (508, 13, 18224152431429493181489789773787936407306642052, [], []),
  (509, 13, 15101204392115617415743453998931337571113902724, [], []),
  (510, 13, 13339058960520087837857930102053485874399683204, [], []),
  (511, 13, 45699808323030407427941488083883850020365324363, [], []),
  (512, 11, 898813238907942891642946498585389236896, [585, 3145, 3584], [([585], 586, true), ([3145], 74, true), ([3584], 1536, false), ([585, 3145], 586, true), ([585, 3584], 586, true), ([3145, 3584], 586, true), ([585, 3145, 3584], 586, true)]),
  (513, 12, 3681538881123290036241959917481694757716640, [585], [([585], 586, true)]),
  (514, 13, 24534501257264808745725532059830679351336174240, [], []),
  (515, 13, 24534501257264808745725532059830679351336174240, [], []),
  (516, 13, 24534501257264808745725532059830679351336174240, [], []),
  (517, 13, 24534501257264808745725532059830679351336174240, [], []),
  (518, 13, 24579102747661869992008603496375976074348135072, [], []),
  (519, 13, 1739867363138932639138833717741988904709456544, [], []),
  (520, 12, 3681538881123290036241959917481694757716640, [585], [([585], 586, true)]),
  (521, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (522, 13, 24534501257264808745725532059830679351336174240, [], []),
  (523, 13, 24534501257264808745725532059830679351336174240, [], []),
  (524, 13, 24534501257264808745725532059830679351336174240, [], []),
  (525, 13, 24534501257264808745725532059830679351336174240, [], []),
  (526, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (527, 13, 15056684547889293910572851793955125711294497440, [], []),
  (528, 13, 25002816906433951831697782143556294942961762976, [], []),
  (529, 13, 25002816906433951831697782143556294942961762976, [], []),
  (530, 13, 25002816906433951831697782143556294942961762976, [], []),
  (531, 13, 25002816906433951831697782143556294942961762976, [], []),
  (532, 13, 25002816906433951831697782143556294942961762976, [], []),
  (533, 13, 25002816906433951831697782143556294942961762976, [], []),
  (534, 13, 25002816906433951831697782143556294942961762976, [], []),
  (535, 13, 25002816906433951831697782143556294942961762976, [], []),
  (536, 13, 25002816906433951831697782143556294942961762976, [], []),
  (537, 13, 25002816906433951831697782143556294942961762976, [], []),
  (538, 13, 25002816906433951831697782143556294942961762976, [], []),
  (539, 13, 25002816906433951831697782143556294942961762976, [], []),
  (540, 13, 25002816906433951831697782143556294942961762976, [], []),
  (541, 13, 25002816906433951831697782143556294942961762976, [], []),
  (542, 13, 25002816906433951831697782143556294942961762976, [], []),
  (543, 13, 25002816906433951831697782143556294942961762976, [], []),
  (544, 13, 25002816906433951831697782143556294942961762976, [], []),
  (545, 13, 25002816906433951831697782143556294942961762976, [], []),
  (546, 13, 25002816906433951831697782143556294942961762976, [], []),
  (547, 13, 25002816906433951831697782143556294942961762976, [], []),
  (548, 13, 25002816906433951831697782143556294942961762976, [], []),
  (549, 13, 25002816906433951831697782143556294942961762976, [], []),
  (550, 13, 25002816906433951831697782143556294942961762976, [], []),
  (551, 13, 25002816906433951831697782143556294942961762976, [], []),
  (552, 13, 25002816906433951831697782143556294942961762976, [], []),
  (553, 13, 25002816906433951831697782143556294942961762976, [], []),
  (554, 13, 25002816906433951831697782143556294942961762976, [], []),
  (555, 13, 25002816906433951831697782143556294942961762976, [], []),
  (556, 13, 25002816906433951831697782143556294942961762976, [], []),
  (557, 13, 25002816906433951831697782143556294942961762976, [], []),
  (558, 13, 25002816906433951831697782143556294942961762976, [], []),
  (559, 13, 25002816906433951831697782143556294942961762976, [], []),
  (560, 13, 25359628829610441801962353635918668727057449632, [], []),
  (561, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (562, 13, 24534501257264808745725532059830679351336174240, [], []),
  (563, 13, 24534501257264808745725532059830679351336174240, [], []),
  (564, 13, 24534501257264808745725532059830679351336174240, [], []),
  (565, 13, 24534501257264808745725532059830679351336174240, [], []),
  (566, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (567, 13, 15056684547889293910572851793955125711294497440, [], []),
  (568, 13, 2052154019168551653336149569471130681872548512, [], []),
  (569, 13, 14900579331499579548582101766046587180752634528, [], []),
  (570, 13, 24534501257264808745725532059830679351336174240, [], []),
  (571, 13, 24534501257264808745725532059830679351336174240, [], []),
  (572, 13, 24534501257264808745725532059830679351336174240, [], []),
  (573, 13, 24534501257264808745725532059830679351336174240, [], []),
  (574, 13, 14900579331499579548582101766046587180752634528, [], []),
  (575, 13, 1739867363138932639138833717741988904709456544, [], []),
  (576, 12, 4291176009110083852190561987608671994053280, [585], [([585], 586, true)])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part5_checked : part5.all packedCert = true := by decide +kernel

def part6 : List Row := [
  (577, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (578, 13, 24535110894392795539541480661900806328572510880, [], []),
  (579, 13, 24535110894392795539541480661900806328572510880, [], []),
  (580, 13, 24535110894392795539541480661900806328572510880, [], []),
  (581, 13, 24535110894392795539541480661900806328572510880, [], []),
  (582, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (583, 13, 15101895675414341950671871832570549411542794912, [], []),
  (584, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (585, 13, 45677900164035039724490501489535716375614464000, [], []),
  (586, 13, 29332634910197369543651453642438836766393770628, [], []),
  (587, 13, 26050946507844343668453307466713747786629653124, [], []),
  (588, 13, 26499672781714582168960898001038731345858142852, [], []),
  (589, 13, 29306866007115180715690299210167243823276630660, [], []),
  (590, 13, 45722114511418878150101028772445080498405912578, [], []),
  (591, 13, 15123129465438279159211618391852792611460883076, [], []),
  (592, 13, 17888868744358320167463874609369394999886676640, [], []),
  (593, 13, 29176453489173471722466736075928435174010847904, [], []),
  (594, 13, 13250313743063950554024445208658535806642750112, [], []),
  (595, 13, 17888868744358320167463874609369394999886676640, [], []),
  (596, 13, 17888868744358320167463874609369394999886676640, [], []),
  (597, 13, 13250313743063950554024445208658535806642750112, [], []),
  (598, 13, 29173676785059396864604874939131791945405366944, [], []),
  (599, 13, 17888868744358320167463874609369394999886676640, [], []),
  (600, 13, 14722783601204235473123159809937283211255153312, [], []),
  (601, 13, 25738697944837442748408103328944242333894902432, [], []),
  (602, 13, 14722783601204235473123159809937283211255153312, [], []),
  (603, 13, 13250934418101214345781802403942491351860445856, [], []),
  (604, 13, 13250934418101214345781802403942491351860445856, [], []),
  (605, 13, 14722783601204235473123159809937283211255153312, [], []),
  (606, 13, 15123423450943709962697962323301806274637791904, [], []),
  (607, 13, 14722783601204235473123159809937283211255153312, [], []),
  (608, 13, 14722783601204235473123159809937283211255153312, [], []),
  (609, 13, 26633558902071449882085547336584009105653432992, [], []),
  (610, 13, 14722783601204235473123159809937283211255153312, [], []),
  (611, 13, 13250934418101214345781802403942491351860445856, [], []),
  (612, 13, 13250934418101214345781802403942491351860445856, [], []),
  (613, 13, 14722783601204235473123159809937283211255153312, [], []),
  (614, 13, 26630782197957375024223686199787365877047952032, [], []),
  (615, 13, 14722783601204235473123159809937283211255153312, [], []),
  (616, 13, 17888868744358320167463874609369394999886676640, [], []),
  (617, 13, 28994693704576853967838555309616400774470894240, [], []),
  (618, 13, 13250313743063950554024445208658535806642750112, [], []),
  (619, 13, 17888868744358320167463874609369394999886676640, [], []),
  (620, 13, 17888868744358320167463874609369394999886676640, [], []),
  (621, 13, 13250313743063950554024445208658535806642750112, [], []),
  (622, 13, 17621313653326236165655338990565736406420882080, [], []),
  (623, 13, 17888868744358320167463874609369394999886676640, [], []),
  (624, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (625, 13, 46034401156828304086737944503453106022278832144, [], []),
  (626, 13, 29329934429333484976005408301554258253867655812, [], []),
  (627, 13, 15435791793343767053082305568933127709782975108, [], []),
  (628, 13, 26162542790640799279423048095970211035113071236, [], []),
  (629, 13, 18245696388643991637488582946933656516310344324, [], []),
  (630, 13, 45989788777387063729533789690443599800837414926, [], []),
  (631, 13, 13383671339952890554171832366586220413994410628, [], []),
  (632, 13, 15258000891804056312662621860479087942084657824, [], []),
  (633, 13, 15435263656362868912145897480673926830709867168, [], []),
  (634, 13, 24535110894392795539541480661900806328572510880, [], []),
  (635, 13, 24535110894392795539541480661900806328572510880, [], []),
  (636, 13, 24535110894392795539541480661900806328572510880, [], []),
  (637, 13, 24535110894392795539541480661900806328572510880, [], []),
  (638, 13, 12915279448928908497152361315864661980534080160, [], []),
  (639, 13, 15101895675414341950671871832570549411542794912, [], []),
  (640, 13, 17577268320890717057074767568688421794535768736, [], []),
  (641, 13, 17577268320890717057074767568688421794535768736, [], []),
  (642, 13, 17577268320890717057074767568688421794535768736, [], []),
  (643, 13, 17577268320890717057074767568688421794535768736, [], []),
  (644, 13, 17577268320890717057074767568688421794535768736, [], []),
  (645, 13, 17577268320890717057074767568688421794535768736, [], []),
  (646, 13, 17577268320890717057074767568688421794535768736, [], []),
  (647, 13, 17577268320890717057074767568688421794535768736, [], []),
  (648, 13, 17889478753670145781056267624505498855619494560, [], []),
  (649, 13, 27927002120982289154073251017407772442538082976, [], []),
  (650, 13, 14499765483493491063542838447062947906710471328, [], []),
  (651, 13, 17889478753670145781056267624505498855619494560, [], []),
  (652, 13, 17889478753670145781056267624505498855619494560, [], []),
  (653, 13, 14499765483493491063542838447062947906710471328, [], []),
  (654, 13, 27924225416868214296211389880611129213932602016, [], []),
  (655, 13, 17889478753670145781056267624505498855619494560, [], []),
  (656, 13, 17889478753670145781056267624505498855619494560, [], []),
  (657, 13, 14655870699883205425533588474971486437252334240, [], []),
  (658, 13, 36487352234924540565760494764145893992687534752, [], []),
  (659, 13, 17889478753670145781056267624505498855619494560, [], []),
  (660, 13, 17889478753670145781056267624505498855619494560, [], []),
  (661, 13, 36487352234924540565760494764145893992687534752, [], []),
  (662, 13, 14655870699883205425533588474971486437252334240, [], []),
  (663, 13, 17889478753670145781056267624505498855619494560, [], []),
  (664, 13, 17577268320890717057074767568688421794535768736, [], []),
  (665, 13, 17577268320890717057074767568688421794535768736, [], []),
  (666, 13, 17577268320890717057074767568688421794535768736, [], []),
  (667, 13, 17577268320890717057074767568688421794535768736, [], []),
  (668, 13, 17577268320890717057074767568688421794535768736, [], []),
  (669, 13, 17577268320890717057074767568688421794535768736, [], []),
  (670, 13, 17577268320890717057074767568688421794535768736, [], []),
  (671, 13, 17577268320890717057074767568688421794535768736, [], []),
  (672, 13, 17577268320890717057074767568688421794535768736, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part6_checked : part6.all packedCert = true := by decide +kernel

def part7 : List Row := [
  (673, 13, 17577268320890717057074767568688421794535768736, [], []),
  (674, 13, 17577268320890717057074767568688421794535768736, [], []),
  (675, 13, 17577268320890717057074767568688421794535768736, [], []),
  (676, 13, 17577268320890717057074767568688421794535768736, [], []),
  (677, 13, 17577268320890717057074767568688421794535768736, [], []),
  (678, 13, 17577268320890717057074767568688421794535768736, [], []),
  (679, 13, 17577268320890717057074767568688421794535768736, [], []),
  (680, 13, 17889478753670145781056267624505498855619494560, [], []),
  (681, 13, 14655870699883205425533588474971486437252334240, [], []),
  (682, 13, 36487352234924540565760494764145893992687534752, [], []),
  (683, 13, 17889478753670145781056267624505498855619494560, [], []),
  (684, 13, 17889478753670145781056267624505498855619494560, [], []),
  (685, 13, 36487352234924540565760494764145893992687534752, [], []),
  (686, 13, 14655870699883205425533588474971486437252334240, [], []),
  (687, 13, 17889478753670145781056267624505498855619494560, [], []),
  (688, 13, 17889478753670145781056267624505498855619494560, [], []),
  (689, 13, 27924301640118404586427205676523193930011968160, [], []),
  (690, 13, 14499765483493491063542838447062947906710471328, [], []),
  (691, 13, 17889478753670145781056267624505498855619494560, [], []),
  (692, 13, 17889478753670145781056267624505498855619494560, [], []),
  (693, 13, 14499765483493491063542838447062947906710471328, [], []),
  (694, 13, 27924225416868214296211389880611129213932602016, [], []),
  (695, 13, 17889478753670145781056267624505498855619494560, [], []),
  (696, 13, 17577268320890717057074767568688421794535768736, [], []),
  (697, 13, 17577268320890717057074767568688421794535768736, [], []),
  (698, 13, 17577268320890717057074767568688421794535768736, [], []),
  (699, 13, 17577268320890717057074767568688421794535768736, [], []),
  (700, 13, 17577268320890717057074767568688421794535768736, [], []),
  (701, 13, 17577268320890717057074767568688421794535768736, [], []),
  (702, 13, 17577268320890717057074767568688421794535768736, [], []),
  (703, 13, 17577268320890717057074767568688421794535768736, [], []),
  (704, 13, 15034384471292445167244000146297428670801838752, [], []),
  (705, 13, 15034384471292445167244000146297428670801838752, [], []),
  (706, 13, 15034384471292445167244000146297428670801838752, [], []),
  (707, 13, 15034384471292445167244000146297428670801838752, [], []),
  (708, 13, 15034384471292445167244000146297428670801838752, [], []),
  (709, 13, 15034384471292445167244000146297428670801838752, [], []),
  (710, 13, 15034384471292445167244000146297428670801838752, [], []),
  (711, 13, 15034384471292445167244000146297428670801838752, [], []),
  (712, 13, 14722174038513016443262500090480351609718112928, [], []),
  (713, 13, 23241319226783757710857252067647266448242442912, [], []),
  (714, 13, 14722174038513016443262500090480351609718112928, [], []),
  (715, 13, 14499166586527710211847142907753867994658308768, [], []),
  (716, 13, 14499166586527710211847142907753867994658308768, [], []),
  (717, 13, 14722174038513016443262500090480351609718112928, [], []),
  (718, 13, 17620496978358601026261322404133286773372551840, [], []),
  (719, 13, 14722174038513016443262500090480351609718112928, [], []),
  (720, 13, 15034384471292445167244000146297428670801838752, [], []),
  (721, 13, 15034384471292445167244000146297428670801838752, [], []),
  (722, 13, 15034384471292445167244000146297428670801838752, [], []),
  (723, 13, 15034384471292445167244000146297428670801838752, [], []),
  (724, 13, 15034384471292445167244000146297428670801838752, [], []),
  (725, 13, 15034384471292445167244000146297428670801838752, [], []),
  (726, 13, 15034384471292445167244000146297428670801838752, [], []),
  (727, 13, 15034384471292445167244000146297428670801838752, [], []),
  (728, 13, 14722174038513016443262500090480351609718112928, [], []),
  (729, 13, 14655271802917424573837892935662406525200171680, [], []),
  (730, 13, 14722174038513016443262500090480351609718112928, [], []),
  (731, 13, 58921803757109594679527203875124428687621030560, [], []),
  (732, 13, 58921803757109594679527203875124428687621030560, [], []),
  (733, 13, 14722174038513016443262500090480351609718112928, [], []),
  (734, 13, 14655271802917424573837892935662406525200171680, [], []),
  (735, 13, 14722174038513016443262500090480351609718112928, [], []),
  (736, 13, 14722174038513016443262500090480351609718112928, [], []),
  (737, 13, 14655271802917424573837892935662406525200171680, [], []),
  (738, 13, 14722174038513016443262500090480351609718112928, [], []),
  (739, 13, 58921803757109594679527203875124428687621030560, [], []),
  (740, 13, 58921803757109594679527203875124428687621030560, [], []),
  (741, 13, 14722174038513016443262500090480351609718112928, [], []),
  (742, 13, 14655271802917424573837892935662406525200171680, [], []),
  (743, 13, 14722174038513016443262500090480351609718112928, [], []),
  (744, 13, 15034384471292445167244000146297428670801838752, [], []),
  (745, 13, 15034384471292445167244000146297428670801838752, [], []),
  (746, 13, 15034384471292445167244000146297428670801838752, [], []),
  (747, 13, 15034384471292445167244000146297428670801838752, [], []),
  (748, 13, 15034384471292445167244000146297428670801838752, [], []),
  (749, 13, 15034384471292445167244000146297428670801838752, [], []),
  (750, 13, 15034384471292445167244000146297428670801838752, [], []),
  (751, 13, 15034384471292445167244000146297428670801838752, [], []),
  (752, 13, 14722174038513016443262500090480351609718112928, [], []),
  (753, 13, 18245070290417839054655954107591570327698735776, [], []),
  (754, 13, 14722174038513016443262500090480351609718112928, [], []),
  (755, 13, 14499166586527710211847142907753867994658308768, [], []),
  (756, 13, 14499166586527710211847142907753867994658308768, [], []),
  (757, 13, 14722174038513016443262500090480351609718112928, [], []),
  (758, 13, 17620496978358601026261322404133286773372551840, [], []),
  (759, 13, 14722174038513016443262500090480351609718112928, [], []),
  (760, 13, 15034384471292445167244000146297428670801838752, [], []),
  (761, 13, 15034384471292445167244000146297428670801838752, [], []),
  (762, 13, 15034384471292445167244000146297428670801838752, [], []),
  (763, 13, 15034384471292445167244000146297428670801838752, [], []),
  (764, 13, 15034384471292445167244000146297428670801838752, [], []),
  (765, 13, 15034384471292445167244000146297428670801838752, [], []),
  (766, 13, 15034384471292445167244000146297428670801838752, [], []),
  (767, 13, 15034384471292445167244000146297428670801838752, [], []),
  (768, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part7_checked : part7.all packedCert = true := by decide +kernel

def part8 : List Row := [
  (769, 13, 15034384471292445167244000146297428670801838752, [], []),
  (770, 13, 15034384471292445167244000146297428670801838752, [], []),
  (771, 13, 15034384471292445167244000146297428670801838752, [], []),
  (772, 13, 15034384471292445167244000146297428670801838752, [], []),
  (773, 13, 15034384471292445167244000146297428670801838752, [], []),
  (774, 13, 15034384471292445167244000146297428670801838752, [], []),
  (775, 13, 15034384471292445167244000146297428670801838752, [], []),
  (776, 13, 14722174038513016443262500090480351609718112928, [], []),
  (777, 13, 30380693732607100485027960375276833305992954528, [], []),
  (778, 13, 14722174038513016443262500090480351609718112928, [], []),
  (779, 13, 14499166586527710211847142907753867994658308768, [], []),
  (780, 13, 14499166586527710211847142907753867994658308768, [], []),
  (781, 13, 14722174038513016443262500090480351609718112928, [], []),
  (782, 13, 30377917028493025627166099238480190077387473568, [], []),
  (783, 13, 14722174038513016443262500090480351609718112928, [], []),
  (784, 13, 15034384471292445167244000146297428670801838752, [], []),
  (785, 13, 15034384471292445167244000146297428670801838752, [], []),
  (786, 13, 15034384471292445167244000146297428670801838752, [], []),
  (787, 13, 15034384471292445167244000146297428670801838752, [], []),
  (788, 13, 15034384471292445167244000146297428670801838752, [], []),
  (789, 13, 15034384471292445167244000146297428670801838752, [], []),
  (790, 13, 15034384471292445167244000146297428670801838752, [], []),
  (791, 13, 15034384471292445167244000146297428670801838752, [], []),
  (792, 13, 14722174038513016443262500090480351609718112928, [], []),
  (793, 13, 14655271802917424573837892935662406525200171680, [], []),
  (794, 13, 14722174038513016443262500090480351609718112928, [], []),
  (795, 13, 58921803757109594679527203875124428687621030560, [], []),
  (796, 13, 58921803757109594679527203875124428687621030560, [], []),
  (797, 13, 14722174038513016443262500090480351609718112928, [], []),
  (798, 13, 14655271802917424573837892935662406525200171680, [], []),
  (799, 13, 14722174038513016443262500090480351609718112928, [], []),
  (800, 13, 14722174038513016443262500090480351609718112928, [], []),
  (801, 13, 14655271802917424573837892935662406525200171680, [], []),
  (802, 13, 14722174038513016443262500090480351609718112928, [], []),
  (803, 13, 58921803757109594679527203875124428687621030560, [], []),
  (804, 13, 58921803757109594679527203875124428687621030560, [], []),
  (805, 13, 14722174038513016443262500090480351609718112928, [], []),
  (806, 13, 14655271802917424573837892935662406525200171680, [], []),
  (807, 13, 14722174038513016443262500090480351609718112928, [], []),
  (808, 13, 15034384471292445167244000146297428670801838752, [], []),
  (809, 13, 15034384471292445167244000146297428670801838752, [], []),
  (810, 13, 15034384471292445167244000146297428670801838752, [], []),
  (811, 13, 15034384471292445167244000146297428670801838752, [], []),
  (812, 13, 15034384471292445167244000146297428670801838752, [], []),
  (813, 13, 15034384471292445167244000146297428670801838752, [], []),
  (814, 13, 15034384471292445167244000146297428670801838752, [], []),
  (815, 13, 15034384471292445167244000146297428670801838752, [], []),
  (816, 13, 14722174038513016443262500090480351609718112928, [], []),
  (817, 13, 30378069474993406207597730830304319509546205856, [], []),
  (818, 13, 14722174038513016443262500090480351609718112928, [], []),
  (819, 13, 14499166586527710211847142907753867994658308768, [], []),
  (820, 13, 14499166586527710211847142907753867994658308768, [], []),
  (821, 13, 14722174038513016443262500090480351609718112928, [], []),
  (822, 13, 30377917028493025627166099238480190077387473568, [], []),
  (823, 13, 14722174038513016443262500090480351609718112928, [], []),
  (824, 13, 15034384471292445167244000146297428670801838752, [], []),
  (825, 13, 15034384471292445167244000146297428670801838752, [], []),
  (826, 13, 15034384471292445167244000146297428670801838752, [], []),
  (827, 13, 15034384471292445167244000146297428670801838752, [], []),
  (828, 13, 15034384471292445167244000146297428670801838752, [], []),
  (829, 13, 15034384471292445167244000146297428670801838752, [], []),
  (830, 13, 15034384471292445167244000146297428670801838752, [], []),
  (831, 13, 15034384471292445167244000146297428670801838752, [], []),
  (832, 13, 17577268320890717057074767568688421794535768736, [], []),
  (833, 13, 17577268320890717057074767568688421794535768736, [], []),
  (834, 13, 17577268320890717057074767568688421794535768736, [], []),
  (835, 13, 17577268320890717057074767568688421794535768736, [], []),
  (836, 13, 17577268320890717057074767568688421794535768736, [], []),
  (837, 13, 17577268320890717057074767568688421794535768736, [], []),
  (838, 13, 17577268320890717057074767568688421794535768736, [], []),
  (839, 13, 17577268320890717057074767568688421794535768736, [], []),
  (840, 13, 17889478753670145781056267624505498855619494560, [], []),
  (841, 13, 26497925070271762307835385946068724120250548896, [], []),
  (842, 13, 14499765483493491063542838447062947906710471328, [], []),
  (843, 13, 17889478753670145781056267624505498855619494560, [], []),
  (844, 13, 17889478753670145781056267624505498855619494560, [], []),
  (845, 13, 14499765483493491063542838447062947906710471328, [], []),
  (846, 13, 15122900774624182530996714600914949448202781344, [], []),
  (847, 13, 17889478753670145781056267624505498855619494560, [], []),
  (848, 13, 17889478753670145781056267624505498855619494560, [], []),
  (849, 13, 14655870699883205425533588474971486437252334240, [], []),
  (850, 13, 36487352234924540565760494764145893992687534752, [], []),
  (851, 13, 17889478753670145781056267624505498855619494560, [], []),
  (852, 13, 17889478753670145781056267624505498855619494560, [], []),
  (853, 13, 36487352234924540565760494764145893992687534752, [], []),
  (854, 13, 14655870699883205425533588474971486437252334240, [], []),
  (855, 13, 17889478753670145781056267624505498855619494560, [], []),
  (856, 13, 17577268320890717057074767568688421794535768736, [], []),
  (857, 13, 17577268320890717057074767568688421794535768736, [], []),
  (858, 13, 17577268320890717057074767568688421794535768736, [], []),
  (859, 13, 17577268320890717057074767568688421794535768736, [], []),
  (860, 13, 17577268320890717057074767568688421794535768736, [], []),
  (861, 13, 17577268320890717057074767568688421794535768736, [], []),
  (862, 13, 17577268320890717057074767568688421794535768736, [], []),
  (863, 13, 17577268320890717057074767568688421794535768736, [], []),
  (864, 13, 17577268320890717057074767568688421794535768736, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part8_checked : part8.all packedCert = true := by decide +kernel

def part9 : List Row := [
  (865, 13, 17577268320890717057074767568688421794535768736, [], []),
  (866, 13, 17577268320890717057074767568688421794535768736, [], []),
  (867, 13, 17577268320890717057074767568688421794535768736, [], []),
  (868, 13, 17577268320890717057074767568688421794535768736, [], []),
  (869, 13, 17577268320890717057074767568688421794535768736, [], []),
  (870, 13, 17577268320890717057074767568688421794535768736, [], []),
  (871, 13, 17577268320890717057074767568688421794535768736, [], []),
  (872, 13, 17889478753670145781056267624505498855619494560, [], []),
  (873, 13, 14655870699883205425533588474971486437252334240, [], []),
  (874, 13, 36487352234924540565760494764145893992687534752, [], []),
  (875, 13, 17889478753670145781056267624505498855619494560, [], []),
  (876, 13, 17889478753670145781056267624505498855619494560, [], []),
  (877, 13, 36487352234924540565760494764145893992687534752, [], []),
  (878, 13, 14655870699883205425533588474971486437252334240, [], []),
  (879, 13, 17889478753670145781056267624505498855619494560, [], []),
  (880, 13, 17889478753670145781056267624505498855619494560, [], []),
  (881, 13, 15435187430653801545194030452644091225365873312, [], []),
  (882, 13, 14499765483493491063542838447062947906710471328, [], []),
  (883, 13, 17889478753670145781056267624505498855619494560, [], []),
  (884, 13, 17889478753670145781056267624505498855619494560, [], []),
  (885, 13, 14499765483493491063542838447062947906710471328, [], []),
  (886, 13, 15122900774624182530996714600914949448202781344, [], []),
  (887, 13, 17889478753670145781056267624505498855619494560, [], []),
  (888, 13, 17577268320890717057074767568688421794535768736, [], []),
  (889, 13, 17577268320890717057074767568688421794535768736, [], []),
  (890, 13, 17577268320890717057074767568688421794535768736, [], []),
  (891, 13, 17577268320890717057074767568688421794535768736, [], []),
  (892, 13, 17577268320890717057074767568688421794535768736, [], []),
  (893, 13, 17577268320890717057074767568688421794535768736, [], []),
  (894, 13, 17577268320890717057074767568688421794535768736, [], []),
  (895, 13, 17577268320890717057074767568688421794535768736, [], []),
  (896, 13, 31604447122327003075408303354330336925968302752, [], []),
  (897, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (898, 13, 24535110894392795539541480661900806328572510880, [], []),
  (899, 13, 24535110894392795539541480661900806328572510880, [], []),
  (900, 13, 24535110894392795539541480661900806328572510880, [], []),
  (901, 13, 24535110894392795539541480661900806328572510880, [], []),
  (902, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (903, 13, 15101895675414341950671871832570549411542794912, [], []),
  (904, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (905, 13, 45878258251495675046245313803213287129931587712, [], []),
  (906, 13, 29330544215335007297731934668850775982502584964, [], []),
  (907, 13, 20431158717814626636786306462006360687122588292, [], []),
  (908, 13, 26163762362643843922876100830563246492382929540, [], []),
  (909, 13, 20743379850879421429340583393470273004980150916, [], []),
  (910, 13, 45855951729472264121590601809869109344390701126, [], []),
  (911, 13, 15123129465438279159211618391852792611460883076, [], []),
  (912, 13, 17888868744358320167463874609369394999886676640, [], []),
  (913, 13, 29174362794311109476547217102340374390119662240, [], []),
  (914, 13, 13250313743063950554024445208658535806642750112, [], []),
  (915, 13, 17888868744358320167463874609369394999886676640, [], []),
  (916, 13, 17888868744358320167463874609369394999886676640, [], []),
  (917, 13, 13250313743063950554024445208658535806642750112, [], []),
  (918, 13, 29173676785059396864604874939131791945405366944, [], []),
  (919, 13, 17888868744358320167463874609369394999886676640, [], []),
  (920, 13, 14722783601204235473123159809937283211255153312, [], []),
  (921, 13, 20743331020366583164704102435871009356555289248, [], []),
  (922, 13, 14722783601204235473123159809937283211255153312, [], []),
  (923, 13, 13250934418101214345781802403942491351860445856, [], []),
  (924, 13, 13250934418101214345781802403942491351860445856, [], []),
  (925, 13, 14722783601204235473123159809937283211255153312, [], []),
  (926, 13, 15123423450943709962697962323301806274637791904, [], []),
  (927, 13, 14722783601204235473123159809937283211255153312, [], []),
  (928, 13, 14722783601204235473123159809937283211255153312, [], []),
  (929, 13, 26632154216460800248108370526204530766476542624, [], []),
  (930, 13, 14722783601204235473123159809937283211255153312, [], []),
  (931, 13, 13250934418101214345781802403942491351860445856, [], []),
  (932, 13, 13250934418101214345781802403942491351860445856, [], []),
  (933, 13, 14722783601204235473123159809937283211255153312, [], []),
  (934, 13, 26630782197957375024223686199787365877047952032, [], []),
  (935, 13, 14722783601204235473123159809937283211255153312, [], []),
  (936, 13, 17888868744358320167463874609369394999886676640, [], []),
  (937, 13, 20431207548341094681488839492919429956174414496, [], []),
  (938, 13, 13250313743063950554024445208658535806642750112, [], []),
  (939, 13, 17888868744358320167463874609369394999886676640, [], []),
  (940, 13, 17888868744358320167463874609369394999886676640, [], []),
  (941, 13, 13250313743063950554024445208658535806642750112, [], []),
  (942, 13, 17621313653326236165655338990565736406420882080, [], []),
  (943, 13, 17888868744358320167463874609369394999886676640, [], []),
  (944, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (945, 13, 45699808457282435398494383030559187487561293936, [], []),
  (946, 13, 29329934429333484976005408301554258253867655812, [], []),
  (947, 13, 15435791793343767053082305568933127709782975108, [], []),
  (948, 13, 26162542790640799279423048095970211035113071236, [], []),
  (949, 13, 18245696388643991637488582946933656516310344324, [], []),
  (950, 13, 45677502233006105991511838113354625769179340886, [], []),
  (951, 13, 13383671339952890554171832366586220413994410628, [], []),
  (952, 13, 15258000891804056312662621860479087942084657824, [], []),
  (953, 13, 15435263656362868912145897480673926830709867168, [], []),
  (954, 13, 24535110894392795539541480661900806328572510880, [], []),
  (955, 13, 24535110894392795539541480661900806328572510880, [], []),
  (956, 13, 24535110894392795539541480661900806328572510880, [], []),
  (957, 13, 24535110894392795539541480661900806328572510880, [], []),
  (958, 13, 12915279448928908497152361315864661980534080160, [], []),
  (959, 13, 15101895675414341950671871832570549411542794912, [], []),
  (960, 13, 4550447267405503766914676383304264899177284256, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part9_checked : part9.all packedCert = true := by decide +kernel

def part10 : List Row := [
  (961, 13, 16149421062617294444508101989314895425087537824, [], []),
  (962, 13, 24534501257264808745725532059830679351336174240, [], []),
  (963, 13, 24534501257264808745725532059830679351336174240, [], []),
  (964, 13, 24534501257264808745725532059830679351336174240, [], []),
  (965, 13, 24534501257264808745725532059830679351336174240, [], []),
  (966, 13, 16149421062617294444508101989314895425087537824, [], []),
  (967, 13, 1739867363138932639138833717741988904709456544, [], []),
  (968, 13, 16461631495396723168489602045131972486171263648, [], []),
  (969, 13, 20430325538995777889419649294990425945279627936, [], []),
  (970, 13, 24534501257264808745725532059830679351336174240, [], []),
  (971, 13, 24534501257264808745725532059830679351336174240, [], []),
  (972, 13, 24534501257264808745725532059830679351336174240, [], []),
  (973, 13, 24534501257264808745725532059830679351336174240, [], []),
  (974, 13, 11666132675973242994796112013839619873429324448, [], []),
  (975, 13, 15056684547889293910572851793955125711294497440, [], []),
  (976, 13, 25002816906433951831697782143556294942961762976, [], []),
  (977, 13, 25002816906433951831697782143556294942961762976, [], []),
  (978, 13, 25002816906433951831697782143556294942961762976, [], []),
  (979, 13, 25002816906433951831697782143556294942961762976, [], []),
  (980, 13, 25002816906433951831697782143556294942961762976, [], []),
  (981, 13, 25002816906433951831697782143556294942961762976, [], []),
  (982, 13, 25002816906433951831697782143556294942961762976, [], []),
  (983, 13, 25002816906433951831697782143556294942961762976, [], []),
  (984, 13, 25002816906433951831697782143556294942961762976, [], []),
  (985, 13, 25002816906433951831697782143556294942961762976, [], []),
  (986, 13, 25002816906433951831697782143556294942961762976, [], []),
  (987, 13, 25002816906433951831697782143556294942961762976, [], []),
  (988, 13, 25002816906433951831697782143556294942961762976, [], []),
  (989, 13, 25002816906433951831697782143556294942961762976, [], []),
  (990, 13, 25002816906433951831697782143556294942961762976, [], []),
  (991, 13, 25002816906433951831697782143556294942961762976, [], []),
  (992, 13, 25002816906433951831697782143556294942961762976, [], []),
  (993, 13, 25002816906433951831697782143556294942961762976, [], []),
  (994, 13, 25002816906433951831697782143556294942961762976, [], []),
  (995, 13, 25002816906433951831697782143556294942961762976, [], []),
  (996, 13, 25002816906433951831697782143556294942961762976, [], []),
  (997, 13, 25002816906433951831697782143556294942961762976, [], []),
  (998, 13, 25002816906433951831697782143556294942961762976, [], []),
  (999, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1000, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1001, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1002, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1003, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1004, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1005, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1006, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1007, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1008, 13, 16461631495396723168489602045131972486171263648, [], []),
  (1009, 13, 11978343108752671718777612069656696934513050272, [], []),
  (1010, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1011, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1012, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1013, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1014, 13, 11666132675973242994796112013839619873429324448, [], []),
  (1015, 13, 15056684547889293910572851793955125711294497440, [], []),
  (1016, 13, 2052154019168551653336149569471130681872548512, [], []),
  (1017, 13, 14900579331499579548582101766046587180752634528, [], []),
  (1018, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1019, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1020, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1021, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1022, 13, 14900579331499579548582101766046587180752634528, [], []),
  (1023, 13, 1739867363138932639138833717741988904709456544, [], []),
  (1024, 11, 898976471740433080286518426063739093664, [1170, 2706, 3584], [([1170], 658, true), ([2706], 82, true), ([3584], 1536, false), ([1170, 2706], 658, true), ([1170, 3584], 658, true), ([2706, 3584], 658, true), ([1170, 2706, 3584], 658, true)]),
  (1025, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1026, 12, 3682207482805169848926030532433015771038368, [1170], [([1170], 658, true)]),
  (1027, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1028, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1029, 13, 14744474783711547066404035808752999971224093344, [], []),
  (1030, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1031, 13, 3278678671697356553564556476057561318177178272, [], []),
  (1032, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1033, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1034, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1035, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1036, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1037, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1038, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1039, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1040, 12, 3682207482805169848926030532433015771038368, [1170], [([1170], 658, true)]),
  (1041, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1042, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (1043, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1044, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1045, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (1046, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1047, 13, 14588369567321832704413285780844461440682230432, [], []),
  (1048, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1049, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1050, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1051, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1052, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1053, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1054, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1055, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1056, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part10_checked : part10.all packedCert = true := by decide +kernel

def part11 : List Row := [
  (1057, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1058, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1059, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1060, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1061, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1062, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1063, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1064, 13, 15212790432880690152376285892478615562849682080, [], []),
  (1065, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1066, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (1067, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1068, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1069, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (1070, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1071, 13, 14588369567321832704413285780844461440682230432, [], []),
  (1072, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1073, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1074, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1075, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1076, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1077, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1078, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1079, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1080, 13, 3434936334587451495986938095790229280877773472, [], []),
  (1081, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1082, 13, 15368895649270404514367035920387154093391544992, [], []),
  (1083, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1084, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1085, 13, 14744474783711547066404035808752999971224093344, [], []),
  (1086, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1087, 13, 3278678671697356553564556476057561318177178272, [], []),
  (1088, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1089, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1090, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1091, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1092, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1093, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1094, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1095, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1096, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1097, 13, 37917735969924043815698059193977480304907059872, [], []),
  (1098, 13, 24490499332435210230950840233209413861389697696, [], []),
  (1099, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1100, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1101, 13, 15101885603853817888364302840424453667371942560, [], []),
  (1102, 13, 37917398409816058244742303526366907990841295520, [], []),
  (1103, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1104, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1105, 13, 24646604548824924592941590261117952391931560608, [], []),
  (1106, 13, 16505884537041066736727684801429720175639331488, [], []),
  (1107, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1108, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1109, 13, 16505884537041066736727684801429720175639331488, [], []),
  (1110, 13, 15124186349052348511505838558697102028877922976, [], []),
  (1111, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1112, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1113, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1114, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1115, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1116, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1117, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1118, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1119, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1120, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1121, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1122, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1123, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1124, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1125, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1126, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1127, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1128, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1129, 13, 15257990820243532250355052868332992197913805472, [], []),
  (1130, 13, 16505884537041066736727684801429720175639331488, [], []),
  (1131, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1132, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1133, 13, 16505884537041066736727684801429720175639331488, [], []),
  (1134, 13, 15124186349052348511505838558697102028877922976, [], []),
  (1135, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1136, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1137, 13, 37917474633066248534958119322278972706920661664, [], []),
  (1138, 13, 15436396781831777235487338614514179089961648800, [], []),
  (1139, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1140, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1141, 13, 15101885603853817888364302840424453667371942560, [], []),
  (1142, 13, 37917398409816058244742303526366907990841295520, [], []),
  (1143, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1144, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1145, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1146, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1147, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1148, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1149, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1150, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1151, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1152, 12, 4291770174024199709585749989364617308078752, [1170], [([1170], 658, true)])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part11_checked : part11.all packedCert = true := by decide +kernel

def part12 : List Row := [
  (1153, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1154, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (1155, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1156, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1157, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (1158, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1159, 13, 13340137398895336838347945277033084797884367520, [], []),
  (1160, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1161, 13, 25894836270630813875275197469250156780533645984, [], []),
  (1162, 13, 17755640798233010465984433043598641771429560992, [], []),
  (1163, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1164, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1165, 13, 17755640798233010465984433043598641771429560992, [], []),
  (1166, 13, 17621259801975952689765445990097614661814911648, [], []),
  (1167, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1168, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (1169, 13, 17911860330882003432277058508065075721852166788, [], []),
  (1170, 13, 45678292352903506191339897954920000185595596800, [], []),
  (1171, 13, 13562033745398169659180794800817656039711187588, [], []),
  (1172, 13, 13651269393299516561839430157870562935483409028, [], []),
  (1173, 13, 45699830192818296765011400577878840136637100033, [], []),
  (1174, 13, 17866589164786841779097891150292353279000060548, [], []),
  (1175, 13, 15101177169526263740666376928962743029656986244, [], []),
  (1176, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1177, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1178, 13, 12937574749609568385278481620143591433748677280, [], []),
  (1179, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1180, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1181, 13, 12937574749609568385278481620143591433748677280, [], []),
  (1182, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1183, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1184, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1185, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1186, 13, 13941298841668922152187128432192929491716211360, [], []),
  (1187, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1188, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1189, 13, 13941298841668922152187128432192929491716211360, [], []),
  (1190, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1191, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1192, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (1193, 13, 17911860330882003432277058508065075721852166788, [], []),
  (1194, 13, 45856125948726567096702645987781050082888028168, [], []),
  (1195, 13, 13562033745398169659180794800817656039711187588, [], []),
  (1196, 13, 13651269393299516561839430157870562935483409028, [], []),
  (1197, 13, 45878279689284456480117703481321493543245623305, [], []),
  (1198, 13, 17866589164786841779097891150292353279000060548, [], []),
  (1199, 13, 15101177169526263740666376928962743029656986244, [], []),
  (1200, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1201, 13, 18245680667534810137728446101731768783982363296, [], []),
  (1202, 13, 17398349757483895814363305119789004057692144288, [], []),
  (1203, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1204, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1205, 13, 17398349757483895814363305119789004057692144288, [], []),
  (1206, 13, 17621259801975952689765445990097614661814911648, [], []),
  (1207, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1208, 13, 13964558264454194286310945388667238920051819168, [], []),
  (1209, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1210, 13, 15257206144063410761485514976962820810508141216, [], []),
  (1211, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1212, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1213, 13, 15257206144063410761485514976962820810508141216, [], []),
  (1214, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1215, 13, 13340137398895336838347945277033084797884367520, [], []),
  (1216, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1217, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1218, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1219, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1220, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1221, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1222, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1223, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1224, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1225, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1226, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1227, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1228, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1229, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1230, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1231, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1232, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1233, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1234, 13, 11688427976653902882922232318118549326643921568, [], []),
  (1235, 13, 15056684547889293910572851793955125711294497440, [], []),
  (1236, 13, 16461631495396723168489602045131972486171263648, [], []),
  (1237, 13, 11688427976653902882922232318118549326643921568, [], []),
  (1238, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1239, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1240, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1241, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1242, 13, 14900579331499579548582101766046587180752634528, [], []),
  (1243, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1244, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1245, 13, 14900579331499579548582101766046587180752634528, [], []),
  (1246, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1247, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1248, 13, 24534501257264808745725532059830679351336174240, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part12_checked : part12.all packedCert = true := by decide +kernel

def part13 : List Row := [
  (1249, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1250, 13, 16149421062617294444508101989314895425087537824, [], []),
  (1251, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1252, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1253, 13, 16149421062617294444508101989314895425087537824, [], []),
  (1254, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1255, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1256, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1257, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1258, 13, 11688427976653902882922232318118549326643921568, [], []),
  (1259, 13, 15056684547889293910572851793955125711294497440, [], []),
  (1260, 13, 16461631495396723168489602045131972486171263648, [], []),
  (1261, 13, 11688427976653902882922232318118549326643921568, [], []),
  (1262, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1263, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1264, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1265, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1266, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1267, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1268, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1269, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1270, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1271, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1272, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1273, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1274, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1275, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1276, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1277, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1278, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1279, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1280, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1281, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1282, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1283, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1284, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1285, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1286, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1287, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1288, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1289, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1290, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1291, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1292, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1293, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1294, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1295, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1296, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1297, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1298, 13, 20186422027422590668839933204370772307890733728, [], []),
  (1299, 13, 15056684547889293910572851793955125711294497440, [], []),
  (1300, 13, 17398262793735009340434102212583203669422441120, [], []),
  (1301, 13, 20186422027422590668839933204370772307890733728, [], []),
  (1302, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1303, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1304, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1305, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1306, 13, 14900579331499579548582101766046587180752634528, [], []),
  (1307, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1308, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1309, 13, 14900579331499579548582101766046587180752634528, [], []),
  (1310, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1311, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1312, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1313, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1314, 13, 17866578442904152426406352296308819261048029856, [], []),
  (1315, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1316, 13, 70141822628814115734998850175528956825636504224, [], []),
  (1317, 13, 17866578442904152426406352296308819261048029856, [], []),
  (1318, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1319, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1320, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1321, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1322, 13, 20186422027422590668839933204370772307890733728, [], []),
  (1323, 13, 15056684547889293910572851793955125711294497440, [], []),
  (1324, 13, 17398262793735009340434102212583203669422441120, [], []),
  (1325, 13, 20186422027422590668839933204370772307890733728, [], []),
  (1326, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1327, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1328, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1329, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1330, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1331, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1332, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1333, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1334, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1335, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1336, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1337, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1338, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1339, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1340, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1341, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1342, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1343, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1344, 13, 18959925188925053870014946281740471897391432352, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part13_checked : part13.all packedCert = true := by decide +kernel

def part14 : List Row := [
  (1345, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1346, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (1347, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1348, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1349, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (1350, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1351, 13, 13340137398895336838347945277033084797884367520, [], []),
  (1352, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1353, 13, 19003906004284851324540660523001813075185697440, [], []),
  (1354, 13, 17755640798233010465984433043598641771429560992, [], []),
  (1355, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1356, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1357, 13, 17755640798233010465984433043598641771429560992, [], []),
  (1358, 13, 17621259801975952689765445990097614661814911648, [], []),
  (1359, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1360, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (1361, 13, 17911860330882003432277058508065075721852166788, [], []),
  (1362, 13, 46078969977449954448795040741264376456280281152, [], []),
  (1363, 13, 13562033745398169659180794800817656039711187588, [], []),
  (1364, 13, 13651269393299516561839430157870562935483409028, [], []),
  (1365, 13, 46034357599345724429638095017006586098323042369, [], []),
  (1366, 13, 17866589164786841779097891150292353279000060548, [], []),
  (1367, 13, 15101177169526263740666376928962743029656986244, [], []),
  (1368, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1369, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1370, 13, 12937574749609568385278481620143591433748677280, [], []),
  (1371, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1372, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1373, 13, 12937574749609568385278481620143591433748677280, [], []),
  (1374, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1375, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1376, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1377, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1378, 13, 13941298841668922152187128432192929491716211360, [], []),
  (1379, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1380, 13, 13652347237509851446472050144848405913654067872, [], []),
  (1381, 13, 13941298841668922152187128432192929491716211360, [], []),
  (1382, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1383, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1384, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (1385, 13, 17911860330882003432277058508065075721852166788, [], []),
  (1386, 13, 45722109064241253826024582784238654773963034696, [], []),
  (1387, 13, 13562033745398169659180794800817656039711187588, [], []),
  (1388, 13, 13651269393299516561839430157870562935483409028, [], []),
  (1389, 13, 45677507575172771617666488180248468906651725897, [], []),
  (1390, 13, 17866589164786841779097891150292353279000060548, [], []),
  (1391, 13, 15101177169526263740666376928962743029656986244, [], []),
  (1392, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1393, 13, 18245680667534810137728446101731768783982363296, [], []),
  (1394, 13, 17398349757483895814363305119789004057692144288, [], []),
  (1395, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1396, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1397, 13, 17398349757483895814363305119789004057692144288, [], []),
  (1398, 13, 17621259801975952689765445990097614661814911648, [], []),
  (1399, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1400, 13, 13964558264454194286310945388667238920051819168, [], []),
  (1401, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1402, 13, 15257206144063410761485514976962820810508141216, [], []),
  (1403, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1404, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1405, 13, 15257206144063410761485514976962820810508141216, [], []),
  (1406, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1407, 13, 13340137398895336838347945277033084797884367520, [], []),
  (1408, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1409, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1410, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1411, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1412, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1413, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1414, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1415, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1416, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1417, 13, 37917735969924043815698059193977480304907059872, [], []),
  (1418, 13, 20431763706302636819191339507587412067301261984, [], []),
  (1419, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1420, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1421, 13, 15101885603853817888364302840424453667371942560, [], []),
  (1422, 13, 37917398409816058244742303526366907990841295520, [], []),
  (1423, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1424, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1425, 13, 20743974139082065543172839563404489128384987808, [], []),
  (1426, 13, 13651040702485419933624526366932719772225307296, [], []),
  (1427, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1428, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1429, 13, 13651040702485419933624526366932719772225307296, [], []),
  (1430, 13, 15124186349052348511505838558697102028877922976, [], []),
  (1431, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1432, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1433, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1434, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1435, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1436, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1437, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1438, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1439, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1440, 13, 17577268320890717057074767568688421794535768736, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part14_checked : part14.all packedCert = true := by decide +kernel

def part15 : List Row := [
  (1441, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1442, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1443, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1444, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1445, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1446, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1447, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1448, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1449, 13, 15257990820243532250355052868332992197913805472, [], []),
  (1450, 13, 13651040702485419933624526366932719772225307296, [], []),
  (1451, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1452, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1453, 13, 13651040702485419933624526366932719772225307296, [], []),
  (1454, 13, 15124186349052348511505838558697102028877922976, [], []),
  (1455, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1456, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1457, 13, 37917474633066248534958119322278972706920661664, [], []),
  (1458, 13, 15436396781831777235487338614514179089961648800, [], []),
  (1459, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1460, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1461, 13, 15101885603853817888364302840424453667371942560, [], []),
  (1462, 13, 37917398409816058244742303526366907990841295520, [], []),
  (1463, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1464, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1465, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1466, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1467, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1468, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1469, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1470, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1471, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1472, 13, 4728902229817818199675889499000849444197434016, [], []),
  (1473, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1474, 13, 20364262573741264098071036813460387070731158176, [], []),
  (1475, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1476, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1477, 13, 14744474783711547066404035808752999971224093344, [], []),
  (1478, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1479, 13, 3278678671697356553564556476057561318177178272, [], []),
  (1480, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1481, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1482, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1483, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1484, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1485, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1486, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1487, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1488, 13, 20208157357351549736080286785551848540189295264, [], []),
  (1489, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1490, 13, 19003121402596016720974875281062609553577804448, [], []),
  (1491, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1492, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1493, 13, 19003121402596016720974875281062609553577804448, [], []),
  (1494, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1495, 13, 14588369567321832704413285780844461440682230432, [], []),
  (1496, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1497, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1498, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1499, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1500, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1501, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1502, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1503, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1504, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1505, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1506, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1507, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1508, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1509, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1510, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1511, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1512, 13, 15212790432880690152376285892478615562849682080, [], []),
  (1513, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1514, 13, 19003121402596016720974875281062609553577804448, [], []),
  (1515, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1516, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1517, 13, 19003121402596016720974875281062609553577804448, [], []),
  (1518, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1519, 13, 14588369567321832704413285780844461440682230432, [], []),
  (1520, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1521, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1522, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1523, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1524, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1525, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1526, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1527, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1528, 13, 3434936334587451495986938095790229280877773472, [], []),
  (1529, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1530, 13, 15368895649270404514367035920387154093391544992, [], []),
  (1531, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1532, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1533, 13, 14744474783711547066404035808752999971224093344, [], []),
  (1534, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1535, 13, 3278678671697356553564556476057561318177178272, [], []),
  (1536, 13, 36492840308938241461299232069814553550401897120, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part15_checked : part15.all packedCert = true := by decide +kernel

def part16 : List Row := [
  (1537, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1538, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1539, 13, 17911779498868676404197803342778147217125474976, [], []),
  (1540, 13, 40703141091766973254847307417424772676237460128, [], []),
  (1541, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1542, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1543, 13, 36130551200783792065526754099770958025174614688, [], []),
  (1544, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1545, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1546, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1547, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1548, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1549, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1550, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1551, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1552, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1553, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1554, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1555, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1556, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1557, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1558, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1559, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1560, 13, 17755674282478962042207053314869608686583612064, [], []),
  (1561, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1562, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1563, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (1564, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (1565, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1566, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1567, 13, 15124186349052348511505838558697102028877922976, [], []),
  (1568, 13, 40234825442597830168875057333699157084611871392, [], []),
  (1569, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1570, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1571, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (1572, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (1573, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1574, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1575, 13, 15124186349052348511505838558697102028877922976, [], []),
  (1576, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1577, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1578, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1579, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1580, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1581, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1582, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1583, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1584, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1585, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1586, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1587, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1588, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1589, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1590, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1591, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1592, 13, 36130627424033982355742569895683022741253980832, [], []),
  (1593, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1594, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1595, 13, 15436396781831777235487338614514179089961648800, [], []),
  (1596, 13, 15436396781831777235487338614514179089961648800, [], []),
  (1597, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1598, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1599, 13, 36130551200783792065526754099770958025174614688, [], []),
  (1600, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1601, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1602, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1603, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1604, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1605, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1606, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1607, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1608, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1609, 13, 3301306087968131277631017033953344177166156448, [], []),
  (1610, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1611, 13, 15056685216490975790385535864570077032307819168, [], []),
  (1612, 13, 24489900435469429379255144693900333949337535136, [], []),
  (1613, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1614, 13, 3256377926498825930423020757784912956671197856, [], []),
  (1615, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1616, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1617, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1618, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1619, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1620, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1621, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1622, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1623, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1624, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1625, 13, 14900580000101261428394785836661538501765956256, [], []),
  (1626, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1627, 13, 18958868361342682515678390340115322961214374560, [], []),
  (1628, 13, 18958868361342682515678390340115322961214374560, [], []),
  (1629, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1630, 13, 14900580000101261428394785836661538501765956256, [], []),
  (1631, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1632, 13, 14722174038513016443262500090480351609718112928, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part16_checked : part16.all packedCert = true := by decide +kernel

def part17 : List Row := [
  (1633, 13, 24646005651859143741245894721808872479879398048, [], []),
  (1634, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1635, 13, 18958868361342682515678390340115322961214374560, [], []),
  (1636, 13, 18958868361342682515678390340115322961214374560, [], []),
  (1637, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1638, 13, 17621270914321997451662143465924638605495567008, [], []),
  (1639, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1640, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1641, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1642, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1643, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1644, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1645, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1646, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1647, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1648, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1649, 13, 3256530372999206510854652349609042388829930144, [], []),
  (1650, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1651, 13, 15056685216490975790385535864570077032307819168, [], []),
  (1652, 13, 18245691779880854899625143577558792727663018656, [], []),
  (1653, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1654, 13, 3256377926498825930423020757784912956671197856, [], []),
  (1655, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1656, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1657, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1658, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1659, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1660, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1661, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1662, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1663, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1664, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1665, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1666, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1667, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1668, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1669, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1670, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1671, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1672, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1673, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1674, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1675, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1676, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1677, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1678, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1679, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1680, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1681, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1682, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1683, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1684, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1685, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1686, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1687, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1688, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1689, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1690, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1691, 13, 20185714240099395116835929385187314230010905248, [], []),
  (1692, 13, 20185714240099395116835929385187314230010905248, [], []),
  (1693, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1694, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1695, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1696, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1697, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1698, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1699, 13, 20185714240099395116835929385187314230010905248, [], []),
  (1700, 13, 20185714240099395116835929385187314230010905248, [], []),
  (1701, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1702, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1703, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1704, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1705, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1706, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1707, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1708, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1709, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1710, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1711, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1712, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1713, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1714, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1715, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1716, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1717, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1718, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1719, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1720, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1721, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1722, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1723, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1724, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1725, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1726, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1727, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1728, 13, 16506222542049421532688660076465196586515890848, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part17_checked : part17.all packedCert = true := by decide +kernel

def part18 : List Row := [
  (1729, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1730, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1731, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (1732, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (1733, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1734, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1735, 13, 13696328647034563016855159574111503036762358432, [], []),
  (1736, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1737, 13, 16150031293910195354181445779386778347637899936, [], []),
  (1738, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1739, 13, 15212648209809315395325766852367275353827246752, [], []),
  (1740, 13, 15212648209809315395325766852367275353827246752, [], []),
  (1741, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1742, 13, 15124197014777786689670802738844953718362800800, [], []),
  (1743, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1744, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1745, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1746, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1747, 13, 13941200840347248921909650980305989142471312032, [], []),
  (1748, 13, 13941200840347248921909650980305989142471312032, [], []),
  (1749, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1750, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1751, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1752, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (1753, 13, 14744370690867644505417220850594088153852682884, [], []),
  (1754, 13, 13249855979725965345291787228962892428375761540, [], []),
  (1755, 13, 45699802875853430870554919317076100512047177729, [], []),
  (1756, 13, 45699824652596983889123688948976695629527916545, [], []),
  (1757, 13, 13205221822221679688916223308455282255615500932, [], []),
  (1758, 13, 14655162265555651277835662563509775799537377924, [], []),
  (1759, 13, 15101280426615432304501215842502799727384339076, [], []),
  (1760, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (1761, 13, 14744370690867644505417220850594088153852682884, [], []),
  (1762, 13, 13249855979725965345291787228962892428375761540, [], []),
  (1763, 13, 45856082306191569935692964001188461418140188680, [], []),
  (1764, 13, 45945307063729245763740526562081545095487741964, [], []),
  (1765, 13, 13205221822221679688916223308455282255615500932, [], []),
  (1766, 13, 14655162265555651277835662563509775799537377924, [], []),
  (1767, 13, 15101280426615432304501215842502799727384339076, [], []),
  (1768, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1769, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1770, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1771, 13, 12892973259212507138995410183598294710736716448, [], []),
  (1772, 13, 12892973259212507138995410183598294710736716448, [], []),
  (1773, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1774, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1775, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1776, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1777, 13, 15436407447557215413652302794662030779446526624, [], []),
  (1778, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1779, 13, 14498980807313369574673300555692776519304807072, [], []),
  (1780, 13, 14498980807313369574673300555692776519304807072, [], []),
  (1781, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1782, 13, 15124197014777786689670802738844953718362800800, [], []),
  (1783, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1784, 13, 14008539079813991740836659629928580097846084256, [], []),
  (1785, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1786, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1787, 13, 15257347549996058352405906229765507554124825248, [], []),
  (1788, 13, 15257347549996058352405906229765507554124825248, [], []),
  (1789, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1790, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1791, 13, 13696328647034563016855159574111503036762358432, [], []),
  (1792, 13, 36487690239932859867504663648758128495874343584, [], []),
  (1793, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1794, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1795, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (1796, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (1797, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1798, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1799, 13, 13696328647034563016855159574111503036762358432, [], []),
  (1800, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1801, 13, 25895456945668077667032554664534112325751341728, [], []),
  (1802, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1803, 13, 15212648209809315395325766852367275353827246752, [], []),
  (1804, 13, 15212648209809315395325766852367275353827246752, [], []),
  (1805, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1806, 13, 15124197014777786689670802738844953718362800800, [], []),
  (1807, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1808, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1809, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1810, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1811, 13, 13941200840347248921909650980305989142471312032, [], []),
  (1812, 13, 13941200840347248921909650980305989142471312032, [], []),
  (1813, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1814, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1815, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1816, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (1817, 13, 14744370690867644505417220850594088153852682884, [], []),
  (1818, 13, 13249855979725965345291787228962892428375761540, [], []),
  (1819, 13, 45922859571751218803785522502531933311408029760, [], []),
  (1820, 13, 46212763820130833951186093007772473429808406596, [], []),
  (1821, 13, 13205221822221679688916223308455282255615500932, [], []),
  (1822, 13, 14655162265555651277835662563509775799537377924, [], []),
  (1823, 13, 15101280426615432304501215842502799727384339076, [], []),
  (1824, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part18_checked : part18.all packedCert = true := by decide +kernel

def part19 : List Row := [
  (1825, 13, 14744370690867644505417220850594088153852682884, [], []),
  (1826, 13, 13249855979725965345291787228962892428375761540, [], []),
  (1827, 13, 45744410096552709081808477844258218553205211232, [], []),
  (1828, 13, 47907576941608896176473500512798837103080661092, [], []),
  (1829, 13, 13205221822221679688916223308455282255615500932, [], []),
  (1830, 13, 14655162265555651277835662563509775799537377924, [], []),
  (1831, 13, 15101280426615432304501215842502799727384339076, [], []),
  (1832, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1833, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1834, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1835, 13, 12892973259212507138995410183598294710736716448, [], []),
  (1836, 13, 12892973259212507138995410183598294710736716448, [], []),
  (1837, 13, 13250933823936300229924407215940735406546420384, [], []),
  (1838, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1839, 13, 24535110894392795539541480661900806328572510880, [], []),
  (1840, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1841, 13, 15436407447557215413652302794662030779446526624, [], []),
  (1842, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1843, 13, 14498980807313369574673300555692776519304807072, [], []),
  (1844, 13, 14498980807313369574673300555692776519304807072, [], []),
  (1845, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1846, 13, 15124197014777786689670802738844953718362800800, [], []),
  (1847, 13, 14722783601204235473123159809937283211255153312, [], []),
  (1848, 13, 14008539079813991740836659629928580097846084256, [], []),
  (1849, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1850, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1851, 13, 15257347549996058352405906229765507554124825248, [], []),
  (1852, 13, 15257347549996058352405906229765507554124825248, [], []),
  (1853, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1854, 13, 17888868744358320167463874609369394999886676640, [], []),
  (1855, 13, 13696328647034563016855159574111503036762358432, [], []),
  (1856, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1857, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1858, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1859, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1860, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1861, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1862, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1863, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1864, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1865, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1866, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1867, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1868, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1869, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1870, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1871, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1872, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1873, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1874, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1875, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1876, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1877, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1878, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1879, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1880, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1881, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1882, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1883, 13, 11643826486256841636639160881573252603631960736, [], []),
  (1884, 13, 11643826486256841636639160881573252603631960736, [], []),
  (1885, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1886, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1887, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1888, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1889, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1890, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1891, 13, 11643826486256841636639160881573252603631960736, [], []),
  (1892, 13, 11643826486256841636639160881573252603631960736, [], []),
  (1893, 13, 14499165917926028332034458837138916673644987040, [], []),
  (1894, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1895, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1896, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1897, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1898, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1899, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1900, 13, 14655271134315742694025208865047455204186849952, [], []),
  (1901, 13, 1695254983706129922824931453209254365114729120, [], []),
  (1902, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1903, 13, 24534501257264808745725532059830679351336174240, [], []),
  (1904, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1905, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1906, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1907, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1908, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1909, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1910, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1911, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1912, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1913, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1914, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1915, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1916, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1917, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1918, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1919, 13, 25002816906433951831697782143556294942961762976, [], []),
  (1920, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part19_checked : part19.all packedCert = true := by decide +kernel

def part20 : List Row := [
  (1921, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1922, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1923, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1924, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1925, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1926, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1927, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1928, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1929, 13, 3301306087968131277631017033953344177166156448, [], []),
  (1930, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1931, 13, 15056685216490975790385535864570077032307819168, [], []),
  (1932, 13, 20743375242116284691477144024095409216332825248, [], []),
  (1933, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1934, 13, 3256377926498825930423020757784912956671197856, [], []),
  (1935, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1936, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1937, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1938, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1939, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1940, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1941, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1942, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1943, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1944, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1945, 13, 14900580000101261428394785836661538501765956256, [], []),
  (1946, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1947, 13, 13249529141375115950458659966719332285034857120, [], []),
  (1948, 13, 13249529141375115950458659966719332285034857120, [], []),
  (1949, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1950, 13, 14900580000101261428394785836661538501765956256, [], []),
  (1951, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1952, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1953, 13, 20431164809336855967495643968278332155249099424, [], []),
  (1954, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1955, 13, 13249529141375115950458659966719332285034857120, [], []),
  (1956, 13, 13249529141375115950458659966719332285034857120, [], []),
  (1957, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1958, 13, 17621270914321997451662143465924638605495567008, [], []),
  (1959, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1960, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1961, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1962, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1963, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1964, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1965, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1966, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1967, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1968, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1969, 13, 3256530372999206510854652349609042388829930144, [], []),
  (1970, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1971, 13, 15056685216490975790385535864570077032307819168, [], []),
  (1972, 13, 18245691779880854899625143577558792727663018656, [], []),
  (1973, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1974, 13, 3256377926498825930423020757784912956671197856, [], []),
  (1975, 13, 14722174038513016443262500090480351609718112928, [], []),
  (1976, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1977, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1978, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1979, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1980, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1981, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1982, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1983, 13, 15034384471292445167244000146297428670801838752, [], []),
  (1984, 13, 36131237210035504677469096262979540469888909984, [], []),
  (1985, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1986, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1987, 13, 17911779498868676404197803342778147217125474976, [], []),
  (1988, 13, 20431763706302636819191339507587412067301261984, [], []),
  (1989, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1990, 13, 17889478753670145781056267624505498855619494560, [], []),
  (1991, 13, 36130551200783792065526754099770958025174614688, [], []),
  (1992, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1993, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1994, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1995, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1996, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1997, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1998, 13, 17577268320890717057074767568688421794535768736, [], []),
  (1999, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2000, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2001, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2002, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2003, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2004, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2005, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2006, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2007, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2008, 13, 17755674282478962042207053314869608686583612064, [], []),
  (2009, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2010, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2011, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2012, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2013, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2014, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2015, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2016, 13, 20253357744714391834059053761406225175253418656, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part20_checked : part20.all packedCert = true := by decide +kernel

def part21 : List Row := [
  (2017, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2018, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2019, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2020, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2021, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2022, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2023, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2024, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2025, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2026, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2027, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2028, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2029, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2030, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2031, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2032, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2033, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2034, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2035, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2036, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2037, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2038, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2039, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2040, 13, 36130627424033982355742569895683022741253980832, [], []),
  (2041, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2042, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2043, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2044, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2045, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2046, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2047, 13, 36130551200783792065526754099770958025174614688, [], []),
  (2048, 11, 1045191551276773826305937202694576997024, [1828, 2340, 3584], [([1828], 100, true), ([2340], 804, true), ([3584], 1536, false), ([1828, 2340], 804, true), ([1828, 3584], 804, true), ([2340, 3584], 804, true), ([1828, 2340, 3584], 804, true)]),
  (2049, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2050, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2051, 13, 17911779498868676404197803342778147217125474976, [], []),
  (2052, 12, 4281104448586021544621569841512927823200928, [2340], [([2340], 804, true)]),
  (2053, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2054, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2055, 13, 6534674729183838828816163987182501261550355104, [], []),
  (2056, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2057, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2058, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2059, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2060, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2061, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2062, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2063, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2064, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2065, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2066, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2067, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2068, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2069, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2070, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2071, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2072, 13, 17755674282478962042207053314869608686583612064, [], []),
  (2073, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2074, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2075, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (2076, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (2077, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2078, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2079, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2080, 12, 4281104448586021544621569841512927823200928, [2340], [([2340], 804, true)]),
  (2081, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2082, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2083, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (2084, 12, 12392767865308677642502165218196058075628192, [2340], [([2340], 804, true)]),
  (2085, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2086, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2087, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2088, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2089, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2090, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2091, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2092, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2093, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2094, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2095, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2096, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2097, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2098, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2099, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2100, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2101, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2102, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2103, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2104, 13, 6690856168823743481022729811003104508171584160, [], []),
  (2105, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2106, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2107, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2108, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2109, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2110, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2111, 13, 6534674729183838828816163987182501261550355104, [], []),
  (2112, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part21_checked : part21.all packedCert = true := by decide +kernel

def part22 : List Row := [
  (2113, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2114, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2115, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2116, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2117, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2118, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2119, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2120, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2121, 13, 60357773567444472055280983062511614906799817376, [], []),
  (2122, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2123, 13, 15056685216490975790385535864570077032307819168, [], []),
  (2124, 13, 24489900435469429379255144693900333949337535136, [], []),
  (2125, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2126, 13, 60357436007336486484325227394901042592734053024, [], []),
  (2127, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2128, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2129, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2130, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2131, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2132, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2133, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2134, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2135, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2136, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2137, 13, 14900580000101261428394785836661538501765956256, [], []),
  (2138, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2139, 13, 18958868361342682515678390340115322961214374560, [], []),
  (2140, 13, 18958868361342682515678390340115322961214374560, [], []),
  (2141, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2142, 13, 14900580000101261428394785836661538501765956256, [], []),
  (2143, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2144, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2145, 13, 24646005651859143741245894721808872479879398048, [], []),
  (2146, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2147, 13, 18958868361342682515678390340115322961214374560, [], []),
  (2148, 13, 18958868361342682515678390340115322961214374560, [], []),
  (2149, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2150, 13, 17621270914321997451662143465924638605495567008, [], []),
  (2151, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2152, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2153, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2154, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2155, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2156, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2157, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2158, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2159, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2160, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2161, 13, 60357588453836867064756858986725172024892785312, [], []),
  (2162, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2163, 13, 15056685216490975790385535864570077032307819168, [], []),
  (2164, 13, 18245691779880854899625143577558792727663018656, [], []),
  (2165, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2166, 13, 60357436007336486484325227394901042592734053024, [], []),
  (2167, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2168, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2169, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2170, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2171, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2172, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2173, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2174, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2175, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2176, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2177, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2178, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2179, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2180, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2181, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2182, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2183, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2184, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2185, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2186, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2187, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2188, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2189, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2190, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2191, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2192, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2193, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2194, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2195, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2196, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2197, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2198, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2199, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2200, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2201, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2202, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2203, 13, 20185714240099395116835929385187314230010905248, [], []),
  (2204, 13, 20185714240099395116835929385187314230010905248, [], []),
  (2205, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2206, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2207, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2208, 13, 24534501257264808745725532059830679351336174240, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part22_checked : part22.all packedCert = true := by decide +kernel

def part23 : List Row := [
  (2209, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2210, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2211, 13, 20185714240099395116835929385187314230010905248, [], []),
  (2212, 13, 20185714240099395116835929385187314230010905248, [], []),
  (2213, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2214, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2215, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2216, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2217, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2218, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2219, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2220, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2221, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2222, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2223, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2224, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2225, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2226, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2227, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2228, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2229, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2230, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2231, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2232, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2233, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2234, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2235, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2236, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2237, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2238, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2239, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2240, 13, 16506222542049421532688660076465196586515890848, [], []),
  (2241, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2242, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2243, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (2244, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (2245, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2246, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2247, 13, 13696328647034563016855159574111503036762358432, [], []),
  (2248, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2249, 13, 16150031293910195354181445779386778347637899936, [], []),
  (2250, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2251, 13, 15212648209809315395325766852367275353827246752, [], []),
  (2252, 13, 15212648209809315395325766852367275353827246752, [], []),
  (2253, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2254, 13, 15124197014777786689670802738844953718362800800, [], []),
  (2255, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2256, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2257, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2258, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2259, 13, 13941200840347248921909650980305989142471312032, [], []),
  (2260, 13, 13941200840347248921909650980305989142471312032, [], []),
  (2261, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2262, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2263, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2264, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (2265, 13, 14744370690867644505417220850594088153852682884, [], []),
  (2266, 13, 13249855979725965345291787228962892428375761540, [], []),
  (2267, 13, 45699802875853431664287600252124215886269947977, [], []),
  (2268, 13, 45699824652596985712764430524051045925700014152, [], []),
  (2269, 13, 13205221822221679688916223308455282255615500932, [], []),
  (2270, 13, 14655162265555651277835662563509775799537377924, [], []),
  (2271, 13, 15101280426615432304501215842502799727384339076, [], []),
  (2272, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (2273, 13, 14744370690867644505417220850594088153852682884, [], []),
  (2274, 13, 13249855979725965345291787228962892428375761540, [], []),
  (2275, 13, 45856082306191569540229305801898312453018886209, [], []),
  (2276, 13, 45945307063729249884765999547381682595336294464, [], []),
  (2277, 13, 13205221822221679688916223308455282255615500932, [], []),
  (2278, 13, 14655162265555651277835662563509775799537377924, [], []),
  (2279, 13, 15101280426615432304501215842502799727384339076, [], []),
  (2280, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2281, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2282, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2283, 13, 12892973259212507138995410183598294710736716448, [], []),
  (2284, 13, 12892973259212507138995410183598294710736716448, [], []),
  (2285, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2286, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2287, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2288, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2289, 13, 15436407447557215413652302794662030779446526624, [], []),
  (2290, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2291, 13, 14498980807313369574673300555692776519304807072, [], []),
  (2292, 13, 14498980807313369574673300555692776519304807072, [], []),
  (2293, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2294, 13, 15124197014777786689670802738844953718362800800, [], []),
  (2295, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2296, 13, 14008539079813991740836659629928580097846084256, [], []),
  (2297, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2298, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2299, 13, 15257347549996058352405906229765507554124825248, [], []),
  (2300, 13, 15257347549996058352405906229765507554124825248, [], []),
  (2301, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2302, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2303, 13, 13696328647034563016855159574111503036762358432, [], []),
  (2304, 12, 3671095136760407952228554705409072090383008, [2340], [([2340], 804, true)])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part23_checked : part23.all packedCert = true := by decide +kernel

def part24 : List Row := [
  (2305, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2306, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2307, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (2308, 12, 12697511938015189246723816822291680896025248, [2340], [([2340], 804, true)]),
  (2309, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2310, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2311, 13, 13696328647034563016855159574111503036762358432, [], []),
  (2312, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2313, 13, 25895456945668077667032554664534112325751341728, [], []),
  (2314, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2315, 13, 15212648209809315395325766852367275353827246752, [], []),
  (2316, 13, 15212648209809315395325766852367275353827246752, [], []),
  (2317, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2318, 13, 15124197014777786689670802738844953718362800800, [], []),
  (2319, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2320, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2321, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2322, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2323, 13, 13941200840347248921909650980305989142471312032, [], []),
  (2324, 13, 13941200840347248921909650980305989142471312032, [], []),
  (2325, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2326, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2327, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2328, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (2329, 13, 14744370690867644505417220850594088153852682884, [], []),
  (2330, 13, 13249855979725965345291787228962892428375761540, [], []),
  (2331, 13, 45922859571751218405187298771958962953188843529, [], []),
  (2332, 13, 46212763820130834265544617916119078538447982600, [], []),
  (2333, 13, 13205221822221679688916223308455282255615500932, [], []),
  (2334, 13, 14655162265555651277835662563509775799537377924, [], []),
  (2335, 13, 15101280426615432304501215842502799727384339076, [], []),
  (2336, 12, 12735604947103503332783457468122384697401988, [2340], [([2340], 804, true)]),
  (2337, 13, 14744370690867644505417220850594088153852682884, [], []),
  (2338, 13, 13249855979725965345291787228962892428375761540, [], []),
  (2339, 13, 45744410096552706622639649834975533936083476481, [], []),
  (2340, 13, 52129453887868794231763382697747484856941547520, [], []),
  (2341, 13, 13205221822221679688916223308455282255615500932, [], []),
  (2342, 13, 14655162265555651277835662563509775799537377924, [], []),
  (2343, 13, 15101280426615432304501215842502799727384339076, [], []),
  (2344, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2345, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2346, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2347, 13, 12892973259212507138995410183598294710736716448, [], []),
  (2348, 13, 12892973259212507138995410183598294710736716448, [], []),
  (2349, 13, 13250933823936300229924407215940735406546420384, [], []),
  (2350, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2351, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2352, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2353, 13, 15436407447557215413652302794662030779446526624, [], []),
  (2354, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2355, 13, 14498980807313369574673300555692776519304807072, [], []),
  (2356, 13, 14498980807313369574673300555692776519304807072, [], []),
  (2357, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2358, 13, 15124197014777786689670802738844953718362800800, [], []),
  (2359, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2360, 13, 14008539079813991740836659629928580097846084256, [], []),
  (2361, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2362, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2363, 13, 15257347549996058352405906229765507554124825248, [], []),
  (2364, 13, 15257347549996058352405906229765507554124825248, [], []),
  (2365, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2366, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2367, 13, 13696328647034563016855159574111503036762358432, [], []),
  (2368, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2369, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2370, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2371, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2372, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2373, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2374, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2375, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2376, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2377, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2378, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2379, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2380, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2381, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2382, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2383, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2384, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2385, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2386, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2387, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2388, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2389, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2390, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2391, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2392, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2393, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2394, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2395, 13, 11643826486256841636639160881573252603631960736, [], []),
  (2396, 13, 11643826486256841636639160881573252603631960736, [], []),
  (2397, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2398, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2399, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2400, 13, 24534501257264808745725532059830679351336174240, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part24_checked : part24.all packedCert = true := by decide +kernel

def part25 : List Row := [
  (2401, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2402, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2403, 13, 11643826486256841636639160881573252603631960736, [], []),
  (2404, 13, 11643826486256841636639160881573252603631960736, [], []),
  (2405, 13, 14499165917926028332034458837138916673644987040, [], []),
  (2406, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2407, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2408, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2409, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2410, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2411, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2412, 13, 14655271134315742694025208865047455204186849952, [], []),
  (2413, 13, 70147408704149489860815064933084556732595765920, [], []),
  (2414, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2415, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2416, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2417, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2418, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2419, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2420, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2421, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2422, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2423, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2424, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2425, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2426, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2427, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2428, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2429, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2430, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2431, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2432, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2433, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2434, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2435, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2436, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2437, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2438, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2439, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2440, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2441, 13, 60357773567444472055280983062511614906799817376, [], []),
  (2442, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2443, 13, 15056685216490975790385535864570077032307819168, [], []),
  (2444, 13, 20743375242116284691477144024095409216332825248, [], []),
  (2445, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2446, 13, 60357436007336486484325227394901042592734053024, [], []),
  (2447, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2448, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2449, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2450, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2451, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2452, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2453, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2454, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2455, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2456, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2457, 13, 14900580000101261428394785836661538501765956256, [], []),
  (2458, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2459, 13, 13249529141375115950458659966719332285034857120, [], []),
  (2460, 13, 13249529141375115950458659966719332285034857120, [], []),
  (2461, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2462, 13, 14900580000101261428394785836661538501765956256, [], []),
  (2463, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2464, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2465, 13, 20431164809336855967495643968278332155249099424, [], []),
  (2466, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2467, 13, 13249529141375115950458659966719332285034857120, [], []),
  (2468, 13, 13249529141375115950458659966719332285034857120, [], []),
  (2469, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2470, 13, 17621270914321997451662143465924638605495567008, [], []),
  (2471, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2472, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2473, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2474, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2475, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2476, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2477, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2478, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2479, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2480, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2481, 13, 60357588453836867064756858986725172024892785312, [], []),
  (2482, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2483, 13, 15056685216490975790385535864570077032307819168, [], []),
  (2484, 13, 18245691779880854899625143577558792727663018656, [], []),
  (2485, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2486, 13, 60357436007336486484325227394901042592734053024, [], []),
  (2487, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2488, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2489, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2490, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2491, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2492, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2493, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2494, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2495, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2496, 13, 7940307685942980698675256401567930481141416608, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part25_checked : part25.all packedCert = true := by decide +kernel

def part26 : List Row := [
  (2497, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2498, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2499, 13, 17911779498868676404197803342778147217125474976, [], []),
  (2500, 13, 20431763706302636819191339507587412067301261984, [], []),
  (2501, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2502, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2503, 13, 6534674729183838828816163987182501261550355104, [], []),
  (2504, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2505, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2506, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2507, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2508, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2509, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2510, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2511, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2512, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2513, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2514, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2515, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2516, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2517, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2518, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2519, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2520, 13, 17755674282478962042207053314869608686583612064, [], []),
  (2521, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2522, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2523, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2524, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2525, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2526, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2527, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2528, 13, 20253357744714391834059053761406225175253418656, [], []),
  (2529, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2530, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2531, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2532, 13, 16148724164720849725476526813469336260895113888, [], []),
  (2533, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2534, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2535, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2536, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2537, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2538, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2539, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2540, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2541, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2542, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2543, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2544, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2545, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2546, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2547, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2548, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2549, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2550, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2551, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2552, 13, 6690856168823743481022729811003104508171584160, [], []),
  (2553, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2554, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2555, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2556, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2557, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2558, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2559, 13, 6534674729183838828816163987182501261550355104, [], []),
  (2560, 13, 58977555620105921237381043170806049591385981600, [], []),
  (2561, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2562, 13, 60327197969508140767703043958046250889448063648, [], []),
  (2563, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2564, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2565, 13, 14744474783711547066404035808752999971224093344, [], []),
  (2566, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2567, 13, 58921825535181077619588865531099304320786563744, [], []),
  (2568, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2569, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2570, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2571, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2572, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2573, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2574, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2575, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2576, 13, 60171092753118426405712293930137712358906200736, [], []),
  (2577, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2578, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (2579, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2580, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2581, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (2582, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2583, 13, 14588369567321832704413285780844461440682230432, [], []),
  (2584, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2585, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2586, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2587, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2588, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2589, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2590, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2591, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2592, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part26_checked : part26.all packedCert = true := by decide +kernel

def part27 : List Row := [
  (2593, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2594, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2595, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2596, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2597, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2598, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2599, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2600, 13, 15212790432880690152376285892478615562849682080, [], []),
  (2601, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2602, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (2603, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2604, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2605, 12, 7416332316377337212067755540337248913392288, [1170], [([1170], 658, true)]),
  (2606, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2607, 13, 14588369567321832704413285780844461440682230432, [], []),
  (2608, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2609, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2610, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2611, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2612, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2613, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2614, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2615, 13, 15034384471292445167244000146297428670801838752, [], []),
  (2616, 13, 58921977981681458200020497122923433752945296032, [], []),
  (2617, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2618, 13, 15368895649270404514367035920387154093391544992, [], []),
  (2619, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2620, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2621, 13, 14744474783711547066404035808752999971224093344, [], []),
  (2622, 13, 14722174038513016443262500090480351609718112928, [], []),
  (2623, 13, 58921825535181077619588865531099304320786563744, [], []),
  (2624, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2625, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2626, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2627, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2628, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2629, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2630, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2631, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2632, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2633, 13, 6512711544093293776630383936520425214110139040, [], []),
  (2634, 13, 24490499332435210230950840233209413861389697696, [], []),
  (2635, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2636, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2637, 13, 15101885603853817888364302840424453667371942560, [], []),
  (2638, 13, 6512373983985308205674628268909852900044374688, [], []),
  (2639, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2640, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2641, 13, 24646604548824924592941590261117952391931560608, [], []),
  (2642, 13, 16505884537041066736727684801429720175639331488, [], []),
  (2643, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2644, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2645, 13, 16505884537041066736727684801429720175639331488, [], []),
  (2646, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2647, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2648, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2649, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2650, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2651, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2652, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2653, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2654, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2655, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2656, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2657, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2658, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2659, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2660, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2661, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2662, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2663, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2664, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2665, 13, 15257990820243532250355052868332992197913805472, [], []),
  (2666, 13, 16505884537041066736727684801429720175639331488, [], []),
  (2667, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2668, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2669, 13, 16505884537041066736727684801429720175639331488, [], []),
  (2670, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2671, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2672, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2673, 13, 6512450207235498495890444064821917616123740832, [], []),
  (2674, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2675, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2676, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2677, 13, 15101885603853817888364302840424453667371942560, [], []),
  (2678, 13, 6512373983985308205674628268909852900044374688, [], []),
  (2679, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2680, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2681, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2682, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2683, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2684, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2685, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2686, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2687, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2688, 13, 58922860584691930539646953426326335716108337824, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part27_checked : part27.all packedCert = true := by decide +kernel

def part28 : List Row := [
  (2689, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2690, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (2691, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2692, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2693, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (2694, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2695, 13, 13340137398895336838347945277033084797884367520, [], []),
  (2696, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2697, 13, 25894836270630813875275197469250156780533645984, [], []),
  (2698, 13, 17755640798233010465984433043598641771429560992, [], []),
  (2699, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2700, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2701, 13, 17755640798233010465984433043598641771429560992, [], []),
  (2702, 13, 17621259801975952689765445990097614661814911648, [], []),
  (2703, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2704, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (2705, 13, 17911860330882003432277058508065075721852166788, [], []),
  (2706, 13, 45677948678153945559480299902660834976455811154, [], []),
  (2707, 13, 13562033745398169659180794800817656039711187588, [], []),
  (2708, 13, 13651269393299516561839430157870562935483409028, [], []),
  (2709, 13, 45699830192818297954962350395807621110424739920, [], []),
  (2710, 13, 17866589164786841779097891150292353279000060548, [], []),
  (2711, 13, 15101177169526263740666376928962743029656986244, [], []),
  (2712, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2713, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2714, 13, 12937574749609568385278481620143591433748677280, [], []),
  (2715, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2716, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2717, 13, 12937574749609568385278481620143591433748677280, [], []),
  (2718, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2719, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2720, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2721, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2722, 13, 13941298841668922152187128432192929491716211360, [], []),
  (2723, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2724, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2725, 13, 13941298841668922152187128432192929491716211360, [], []),
  (2726, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2727, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2728, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (2729, 13, 17911860330882003432277058508065075721852166788, [], []),
  (2730, 13, 45856125948726566621875694793074455816610013250, [], []),
  (2731, 13, 13562033745398169659180794800817656039711187588, [], []),
  (2732, 13, 13651269393299516561839430157870562935483409028, [], []),
  (2733, 13, 45878279689284455768128506538868378754082938944, [], []),
  (2734, 13, 17866589164786841779097891150292353279000060548, [], []),
  (2735, 13, 15101177169526263740666376928962743029656986244, [], []),
  (2736, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2737, 13, 18245680667534810137728446101731768783982363296, [], []),
  (2738, 13, 17398349757483895814363305119789004057692144288, [], []),
  (2739, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2740, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2741, 13, 17398349757483895814363305119789004057692144288, [], []),
  (2742, 13, 17621259801975952689765445990097614661814911648, [], []),
  (2743, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2744, 13, 13964558264454194286310945388667238920051819168, [], []),
  (2745, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2746, 13, 15257206144063410761485514976962820810508141216, [], []),
  (2747, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2748, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2749, 13, 15257206144063410761485514976962820810508141216, [], []),
  (2750, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2751, 13, 13340137398895336838347945277033084797884367520, [], []),
  (2752, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2753, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2754, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2755, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2756, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2757, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2758, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2759, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2760, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2761, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2762, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2763, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2764, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2765, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2766, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2767, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2768, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2769, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2770, 13, 11688427976653902882922232318118549326643921568, [], []),
  (2771, 13, 15056684547889293910572851793955125711294497440, [], []),
  (2772, 13, 16461631495396723168489602045131972486171263648, [], []),
  (2773, 13, 11688427976653902882922232318118549326643921568, [], []),
  (2774, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2775, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2776, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2777, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2778, 13, 14900579331499579548582101766046587180752634528, [], []),
  (2779, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2780, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2781, 13, 14900579331499579548582101766046587180752634528, [], []),
  (2782, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2783, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2784, 13, 24534501257264808745725532059830679351336174240, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part28_checked : part28.all packedCert = true := by decide +kernel

def part29 : List Row := [
  (2785, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2786, 13, 16149421062617294444508101989314895425087537824, [], []),
  (2787, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2788, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2789, 13, 16149421062617294444508101989314895425087537824, [], []),
  (2790, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2791, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2792, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2793, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2794, 13, 11688427976653902882922232318118549326643921568, [], []),
  (2795, 13, 15056684547889293910572851793955125711294497440, [], []),
  (2796, 13, 16461631495396723168489602045131972486171263648, [], []),
  (2797, 13, 11688427976653902882922232318118549326643921568, [], []),
  (2798, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2799, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2800, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2801, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2802, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2803, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2804, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2805, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2806, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2807, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2808, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2809, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2810, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2811, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2812, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2813, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2814, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2815, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2816, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2817, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2818, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2819, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2820, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2821, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2822, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2823, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2824, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2825, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2826, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2827, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2828, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2829, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2830, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2831, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2832, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2833, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2834, 13, 20186422027422590668839933204370772307890733728, [], []),
  (2835, 13, 15056684547889293910572851793955125711294497440, [], []),
  (2836, 13, 17398262793735009340434102212583203669422441120, [], []),
  (2837, 13, 20186422027422590668839933204370772307890733728, [], []),
  (2838, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2839, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2840, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2841, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2842, 13, 14900579331499579548582101766046587180752634528, [], []),
  (2843, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2844, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2845, 13, 14900579331499579548582101766046587180752634528, [], []),
  (2846, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2847, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2848, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2849, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2850, 13, 17866578442904152426406352296308819261048029856, [], []),
  (2851, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2852, 13, 1650653493309068676541860016663957642102768288, [], []),
  (2853, 13, 17866578442904152426406352296308819261048029856, [], []),
  (2854, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2855, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2856, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2857, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2858, 13, 20186422027422590668839933204370772307890733728, [], []),
  (2859, 13, 15056684547889293910572851793955125711294497440, [], []),
  (2860, 13, 17398262793735009340434102212583203669422441120, [], []),
  (2861, 13, 20186422027422590668839933204370772307890733728, [], []),
  (2862, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2863, 13, 24534501257264808745725532059830679351336174240, [], []),
  (2864, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2865, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2866, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2867, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2868, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2869, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2870, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2871, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2872, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2873, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2874, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2875, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2876, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2877, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2878, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2879, 13, 25002816906433951831697782143556294942961762976, [], []),
  (2880, 13, 18959925188925053870014946281740471897391432352, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part29_checked : part29.all packedCert = true := by decide +kernel

def part30 : List Row := [
  (2881, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2882, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (2883, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2884, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2885, 12, 6501802133110261184392203004178917261116064, [1170], [([1170], 658, true)]),
  (2886, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2887, 13, 13340137398895336838347945277033084797884367520, [], []),
  (2888, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2889, 13, 19003906004284851324540660523001813075185697440, [], []),
  (2890, 13, 17755640798233010465984433043598641771429560992, [], []),
  (2891, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2892, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2893, 13, 17755640798233010465984433043598641771429560992, [], []),
  (2894, 13, 17621259801975952689765445990097614661814911648, [], []),
  (2895, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2896, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (2897, 13, 17911860330882003432277058508065075721852166788, [], []),
  (2898, 13, 46078969977449949533089065369981216447386411018, [], []),
  (2899, 13, 13562033745398169659180794800817656039711187588, [], []),
  (2900, 13, 13651269393299516561839430157870562935483409028, [], []),
  (2901, 13, 46034357599345725616957742023103570586848239624, [], []),
  (2902, 13, 17866589164786841779097891150292353279000060548, [], []),
  (2903, 13, 15101177169526263740666376928962743029656986244, [], []),
  (2904, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2905, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2906, 13, 12937574749609568385278481620143591433748677280, [], []),
  (2907, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2908, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2909, 13, 12937574749609568385278481620143591433748677280, [], []),
  (2910, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2911, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2912, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2913, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2914, 13, 13941298841668922152187128432192929491716211360, [], []),
  (2915, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2916, 13, 13652347237509851446472050144848405913654067872, [], []),
  (2917, 13, 13941298841668922152187128432192929491716211360, [], []),
  (2918, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2919, 13, 24535110894392795539541480661900806328572510880, [], []),
  (2920, 12, 6387485860201876816464693132477876753408644, [1170], [([1170], 658, true)]),
  (2921, 13, 17911860330882003432277058508065075721852166788, [], []),
  (2922, 13, 45722109064241253349281786203156567550257545217, [], []),
  (2923, 13, 13562033745398169659180794800817656039711187588, [], []),
  (2924, 13, 13651269393299516561839430157870562935483409028, [], []),
  (2925, 13, 45677507575172770903219979310494027502437019649, [], []),
  (2926, 13, 17866589164786841779097891150292353279000060548, [], []),
  (2927, 13, 15101177169526263740666376928962743029656986244, [], []),
  (2928, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2929, 13, 18245680667534810137728446101731768783982363296, [], []),
  (2930, 13, 17398349757483895814363305119789004057692144288, [], []),
  (2931, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2932, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2933, 13, 17398349757483895814363305119789004057692144288, [], []),
  (2934, 13, 17621259801975952689765445990097614661814911648, [], []),
  (2935, 13, 17888868744358320167463874609369394999886676640, [], []),
  (2936, 13, 13964558264454194286310945388667238920051819168, [], []),
  (2937, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2938, 13, 15257206144063410761485514976962820810508141216, [], []),
  (2939, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2940, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2941, 13, 15257206144063410761485514976962820810508141216, [], []),
  (2942, 13, 14722783601204235473123159809937283211255153312, [], []),
  (2943, 13, 13340137398895336838347945277033084797884367520, [], []),
  (2944, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2945, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2946, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2947, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2948, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2949, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2950, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2951, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2952, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2953, 13, 6512711544093293776630383936520425214110139040, [], []),
  (2954, 13, 20431763706302636819191339507587412067301261984, [], []),
  (2955, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2956, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2957, 13, 15101885603853817888364302840424453667371942560, [], []),
  (2958, 13, 6512373983985308205674628268909852900044374688, [], []),
  (2959, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2960, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2961, 13, 20743974139082065543172839563404489128384987808, [], []),
  (2962, 13, 13651040702485419933624526366932719772225307296, [], []),
  (2963, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2964, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2965, 13, 13651040702485419933624526366932719772225307296, [], []),
  (2966, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2967, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2968, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2969, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2970, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2971, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2972, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2973, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2974, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2975, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2976, 13, 17577268320890717057074767568688421794535768736, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part30_checked : part30.all packedCert = true := by decide +kernel

def part31 : List Row := [
  (2977, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2978, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2979, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2980, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2981, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2982, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2983, 13, 17577268320890717057074767568688421794535768736, [], []),
  (2984, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2985, 13, 15257990820243532250355052868332992197913805472, [], []),
  (2986, 13, 13651040702485419933624526366932719772225307296, [], []),
  (2987, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2988, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2989, 13, 13651040702485419933624526366932719772225307296, [], []),
  (2990, 13, 15124186349052348511505838558697102028877922976, [], []),
  (2991, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2992, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2993, 13, 6512450207235498495890444064821917616123740832, [], []),
  (2994, 13, 15436396781831777235487338614514179089961648800, [], []),
  (2995, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2996, 13, 17889478753670145781056267624505498855619494560, [], []),
  (2997, 13, 15101885603853817888364302840424453667371942560, [], []),
  (2998, 13, 6512373983985308205674628268909852900044374688, [], []),
  (2999, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3000, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3001, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3002, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3003, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3004, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3005, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3006, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3007, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3008, 13, 58922511544432790231531207694307886765500859040, [], []),
  (3009, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3010, 13, 20364262573741264098071036813460387070731158176, [], []),
  (3011, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3012, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3013, 13, 14744474783711547066404035808752999971224093344, [], []),
  (3014, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3015, 13, 58921825535181077619588865531099304320786563744, [], []),
  (3016, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3017, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3018, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3019, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3020, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3021, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3022, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3023, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3024, 13, 20208157357351549736080286785551848540189295264, [], []),
  (3025, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3026, 13, 19003121402596016720974875281062609553577804448, [], []),
  (3027, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3028, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3029, 13, 19003121402596016720974875281062609553577804448, [], []),
  (3030, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3031, 13, 14588369567321832704413285780844461440682230432, [], []),
  (3032, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3033, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3034, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3035, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3036, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3037, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3038, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3039, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3040, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3041, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3042, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3043, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3044, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3045, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3046, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3047, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3048, 13, 15212790432880690152376285892478615562849682080, [], []),
  (3049, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3050, 13, 19003121402596016720974875281062609553577804448, [], []),
  (3051, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3052, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3053, 13, 19003121402596016720974875281062609553577804448, [], []),
  (3054, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3055, 13, 14588369567321832704413285780844461440682230432, [], []),
  (3056, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3057, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3058, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3059, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3060, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3061, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3062, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3063, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3064, 13, 58921977981681458200020497122923433752945296032, [], []),
  (3065, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3066, 13, 15368895649270404514367035920387154093391544992, [], []),
  (3067, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3068, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3069, 13, 14744474783711547066404035808752999971224093344, [], []),
  (3070, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3071, 13, 58921825535181077619588865531099304320786563744, [], []),
  (3072, 13, 70175268302094040934695738338944210459604091552, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part31_checked : part31.all packedCert = true := by decide +kernel

def part32 : List Row := [
  (3073, 13, 70161825933458463693307611645669226992572105376, [], []),
  (3074, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3075, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3076, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3077, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3078, 13, 24579102747661869992008603496375976074348135072, [], []),
  (3079, 13, 70141844406885598675060511831503832458802037408, [], []),
  (3080, 13, 70317931149848178055298361673577765523113968288, [], []),
  (3081, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (3082, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3083, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3084, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3085, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3086, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (3087, 13, 15056684547889293910572851793955125711294497440, [], []),
  (3088, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3089, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3090, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3091, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3092, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3093, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3094, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3095, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3096, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3097, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3098, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3099, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3100, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3101, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3102, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3103, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3104, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3105, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3106, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3107, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3108, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3109, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3110, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3111, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3112, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3113, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3114, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3115, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3116, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3117, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3118, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3119, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3120, 13, 25359628829610441801962353635918668727057449632, [], []),
  (3121, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (3122, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3123, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3124, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3125, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3126, 12, 4928187486218602677034916838868681401369248, [585], [([585], 586, true)]),
  (3127, 13, 15056684547889293910572851793955125711294497440, [], []),
  (3128, 13, 70141920630135788965276327627415897174881403552, [], []),
  (3129, 13, 14900579331499579548582101766046587180752634528, [], []),
  (3130, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3131, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3132, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3133, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3134, 13, 14900579331499579548582101766046587180752634528, [], []),
  (3135, 13, 70141844406885598675060511831503832458802037408, [], []),
  (3136, 13, 71567382518093879745040310498916200744685208224, [], []),
  (3137, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (3138, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3139, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3140, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3141, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3142, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (3143, 13, 15101895675414341950671871832570549411542794912, [], []),
  (3144, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (3145, 13, 45677900164014569061383199320225898184116060234, [], []),
  (3146, 13, 29332634910197369543651453642438836766393770628, [], []),
  (3147, 13, 26050946507844343668453307466713747786629653124, [], []),
  (3148, 13, 26499672781714582168960898001038731345858142852, [], []),
  (3149, 13, 29306866007115180715690299210167243823276630660, [], []),
  (3150, 13, 45722114511418878626901683776144663369700651082, [], []),
  (3151, 13, 15123129465438279159211618391852792611460883076, [], []),
  (3152, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3153, 13, 29176453489173471722466736075928435174010847904, [], []),
  (3154, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3155, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3156, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3157, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3158, 13, 29173676785059396864604874939131791945405366944, [], []),
  (3159, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3160, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3161, 13, 25738697944837442748408103328944242333894902432, [], []),
  (3162, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3163, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3164, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3165, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3166, 13, 15123423450943709962697962323301806274637791904, [], []),
  (3167, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3168, 13, 14722783601204235473123159809937283211255153312, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part32_checked : part32.all packedCert = true := by decide +kernel

def part33 : List Row := [
  (3169, 13, 26633558902071449882085547336584009105653432992, [], []),
  (3170, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3171, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3172, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3173, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3174, 13, 26630782197957375024223686199787365877047952032, [], []),
  (3175, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3176, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3177, 13, 28994693704576853967838555309616400774470894240, [], []),
  (3178, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3179, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3180, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3181, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3182, 13, 17621313653326236165655338990565736406420882080, [], []),
  (3183, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3184, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (3185, 13, 46034401156828302899321413406991650308244127810, [], []),
  (3186, 13, 29329934429333484976005408301554258253867655812, [], []),
  (3187, 13, 15435791793343767053082305568933127709782975108, [], []),
  (3188, 13, 26162542790640799279423048095970211035113071236, [], []),
  (3189, 13, 18245696388643991637488582946933656516310344324, [], []),
  (3190, 13, 45989788777387062621384224809778530269308137538, [], []),
  (3191, 13, 13383671339952890554171832366586220413994410628, [], []),
  (3192, 13, 15258000891804056312662621860479087942084657824, [], []),
  (3193, 13, 15435263656362868912145897480673926830709867168, [], []),
  (3194, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3195, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3196, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3197, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3198, 13, 12915279448928908497152361315864661980534080160, [], []),
  (3199, 13, 15101895675414341950671871832570549411542794912, [], []),
  (3200, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3201, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3202, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3203, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3204, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3205, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3206, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3207, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3208, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3209, 13, 27927002120982289154073251017407772442538082976, [], []),
  (3210, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3211, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3212, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3213, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3214, 13, 27924225416868214296211389880611129213932602016, [], []),
  (3215, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3216, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3217, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3218, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3219, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3220, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3221, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3222, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3223, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3224, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3225, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3226, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3227, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3228, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3229, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3230, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3231, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3232, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3233, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3234, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3235, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3236, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3237, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3238, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3239, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3240, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3241, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3242, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3243, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3244, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3245, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3246, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3247, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3248, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3249, 13, 27924301640118404586427205676523193930011968160, [], []),
  (3250, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3251, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3252, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3253, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3254, 13, 27924225416868214296211389880611129213932602016, [], []),
  (3255, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3256, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3257, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3258, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3259, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3260, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3261, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3262, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3263, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3264, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part33_checked : part33.all packedCert = true := by decide +kernel

def part34 : List Row := [
  (3265, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3266, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3267, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3268, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3269, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3270, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3271, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3272, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3273, 13, 23241319226783757710857252067647266448242442912, [], []),
  (3274, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3275, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3276, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3277, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3278, 13, 17620496978358601026261322404133286773372551840, [], []),
  (3279, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3280, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3281, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3282, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3283, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3284, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3285, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3286, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3287, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3288, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3289, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3290, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3291, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3292, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3293, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3294, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3295, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3296, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3297, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3298, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3299, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3300, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3301, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3302, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3303, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3304, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3305, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3306, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3307, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3308, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3309, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3310, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3311, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3312, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3313, 13, 18245070290417839054655954107591570327698735776, [], []),
  (3314, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3315, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3316, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3317, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3318, 13, 17620496978358601026261322404133286773372551840, [], []),
  (3319, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3320, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3321, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3322, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3323, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3324, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3325, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3326, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3327, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3328, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3329, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3330, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3331, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3332, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3333, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3334, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3335, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3336, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3337, 13, 30380693732607100485027960375276833305992954528, [], []),
  (3338, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3339, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3340, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3341, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3342, 13, 30377917028493025627166099238480190077387473568, [], []),
  (3343, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3344, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3345, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3346, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3347, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3348, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3349, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3350, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3351, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3352, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3353, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3354, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3355, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3356, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3357, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3358, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3359, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3360, 13, 14722174038513016443262500090480351609718112928, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part34_checked : part34.all packedCert = true := by decide +kernel

def part35 : List Row := [
  (3361, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3362, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3363, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3364, 13, 3256356148427342990361359101810037323505664672, [], []),
  (3365, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3366, 13, 14655271802917424573837892935662406525200171680, [], []),
  (3367, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3368, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3369, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3370, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3371, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3372, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3373, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3374, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3375, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3376, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3377, 13, 30378069474993406207597730830304319509546205856, [], []),
  (3378, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3379, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3380, 13, 14499166586527710211847142907753867994658308768, [], []),
  (3381, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3382, 13, 30377917028493025627166099238480190077387473568, [], []),
  (3383, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3384, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3385, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3386, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3387, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3388, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3389, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3390, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3391, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3392, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3393, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3394, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3395, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3396, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3397, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3398, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3399, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3400, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3401, 13, 26497925070271762307835385946068724120250548896, [], []),
  (3402, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3403, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3404, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3405, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3406, 13, 15122900774624182530996714600914949448202781344, [], []),
  (3407, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3408, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3409, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3410, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3411, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3412, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3413, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3414, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3415, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3416, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3417, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3418, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3419, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3420, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3421, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3422, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3423, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3424, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3425, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3426, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3427, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3428, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3429, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3430, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3431, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3432, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3433, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3434, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3435, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3436, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3437, 13, 6512363094949566735643797440922415083461608096, [], []),
  (3438, 13, 14655870699883205425533588474971486437252334240, [], []),
  (3439, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3440, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3441, 13, 15435187430653801545194030452644091225365873312, [], []),
  (3442, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3443, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3444, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3445, 13, 14499765483493491063542838447062947906710471328, [], []),
  (3446, 13, 15122900774624182530996714600914949448202781344, [], []),
  (3447, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3448, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3449, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3450, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3451, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3452, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3453, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3454, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3455, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3456, 13, 31604447122327003075408303354330336925968302752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part35_checked : part35.all packedCert = true := by decide +kernel

def part36 : List Row := [
  (3457, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (3458, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3459, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3460, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3461, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3462, 12, 3403871319602243927704893706049358266434208, [585], [([585], 586, true)]),
  (3463, 13, 15101895675414341950671871832570549411542794912, [], []),
  (3464, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (3465, 13, 45878258251495664979470797185359999250418679818, [], []),
  (3466, 13, 29330544215335007297731934668850775982502584964, [], []),
  (3467, 13, 20431158717814626636786306462006360687122588292, [], []),
  (3468, 13, 26163762362643843922876100830563246492382929540, [], []),
  (3469, 13, 20743379850879421429340583393470273004980150916, [], []),
  (3470, 13, 45855951729472264595837372498610773676836040714, [], []),
  (3471, 13, 15123129465438279159211618391852792611460883076, [], []),
  (3472, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3473, 13, 29174362794311109476547217102340374390119662240, [], []),
  (3474, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3475, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3476, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3477, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3478, 13, 29173676785059396864604874939131791945405366944, [], []),
  (3479, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3480, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3481, 13, 20743331020366583164704102435871009356555289248, [], []),
  (3482, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3483, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3484, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3485, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3486, 13, 15123423450943709962697962323301806274637791904, [], []),
  (3487, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3488, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3489, 13, 26632154216460800248108370526204530766476542624, [], []),
  (3490, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3491, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3492, 13, 13250934418101214345781802403942491351860445856, [], []),
  (3493, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3494, 13, 26630782197957375024223686199787365877047952032, [], []),
  (3495, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3496, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3497, 13, 20431207548341094681488839492919429956174414496, [], []),
  (3498, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3499, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3500, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3501, 13, 13250313743063950554024445208658535806642750112, [], []),
  (3502, 13, 17621313653326236165655338990565736406420882080, [], []),
  (3503, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3504, 12, 3213331798775199219570575009765693823394436, [585], [([585], 586, true)]),
  (3505, 13, 45699808457282434208543338751462594359773380610, [], []),
  (3506, 13, 29329934429333484976005408301554258253867655812, [], []),
  (3507, 13, 15435791793343767053082305568933127709782975108, [], []),
  (3508, 13, 26162542790640799279423048095970211035113071236, [], []),
  (3509, 13, 18245696388643991637488582946933656516310344324, [], []),
  (3510, 13, 45677502233006104880731069595165868882730692610, [], []),
  (3511, 13, 13383671339952890554171832366586220413994410628, [], []),
  (3512, 13, 15258000891804056312662621860479087942084657824, [], []),
  (3513, 13, 15435263656362868912145897480673926830709867168, [], []),
  (3514, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3515, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3516, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3517, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3518, 13, 12915279448928908497152361315864661980534080160, [], []),
  (3519, 13, 15101895675414341950671871832570549411542794912, [], []),
  (3520, 13, 70142530416137311287002853994712414903516332704, [], []),
  (3521, 13, 16149421062617294444508101989314895425087537824, [], []),
  (3522, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3523, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3524, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3525, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3526, 13, 16149421062617294444508101989314895425087537824, [], []),
  (3527, 13, 70141844406885598675060511831503832458802037408, [], []),
  (3528, 13, 16461631495396723168489602045131972486171263648, [], []),
  (3529, 13, 20430325538995777889419649294990425945279627936, [], []),
  (3530, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3531, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3532, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3533, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3534, 13, 11666132675973242994796112013839619873429324448, [], []),
  (3535, 13, 15056684547889293910572851793955125711294497440, [], []),
  (3536, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3537, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3538, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3539, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3540, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3541, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3542, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3543, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3544, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3545, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3546, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3547, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3548, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3549, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3550, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3551, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3552, 13, 25002816906433951831697782143556294942961762976, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part36_checked : part36.all packedCert = true := by decide +kernel

def part37 : List Row := [
  (3553, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3554, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3555, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3556, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3557, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3558, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3559, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3560, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3561, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3562, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3563, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3564, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3565, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3566, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3567, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3568, 13, 16461631495396723168489602045131972486171263648, [], []),
  (3569, 13, 11978343108752671718777612069656696934513050272, [], []),
  (3570, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3571, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3572, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3573, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3574, 13, 11666132675973242994796112013839619873429324448, [], []),
  (3575, 13, 15056684547889293910572851793955125711294497440, [], []),
  (3576, 13, 70141920630135788965276327627415897174881403552, [], []),
  (3577, 13, 14900579331499579548582101766046587180752634528, [], []),
  (3578, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3579, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3580, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3581, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3582, 13, 14900579331499579548582101766046587180752634528, [], []),
  (3583, 13, 70141844406885598675060511831503832458802037408, [], []),
  (3584, 12, 16728962304236291515018295252256678662379008, [3584], [([3584], 1536, true)]),
  (3585, 13, 36403572014993160411898754241577740312211628676, [], []),
  (3586, 13, 37831211713128601377676657778359585494627525252, [], []),
  (3587, 13, 17911174321630290820334716344856493277137871492, [], []),
  (3588, 13, 40708791665562062203696531098286144363049263748, [], []),
  (3589, 13, 15101204392115617415743453998931337571113902724, [], []),
  (3590, 13, 13339058960520087837857930102053485874399683204, [], []),
  (3591, 13, 45747197991438921034809731593569297443267674192, [], []),
  (3592, 13, 35779113019204559137996441060903675706249118368, [], []),
  (3593, 13, 36488310320805209543404625656040328095778013856, [], []),
  (3594, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3595, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3596, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3597, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3598, 13, 13340136804730422722490550089031328852570342048, [], []),
  (3599, 13, 12982187129042371101592383884676325973343404704, [], []),
  (3600, 13, 37206714605717176588542045686816970622769365664, [], []),
  (3601, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3602, 13, 36131498991793633688997449351679710256996352672, [], []),
  (3603, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3604, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3605, 13, 25984659926462200159598697537624705771775263392, [], []),
  (3606, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3607, 13, 14588205566178975007301105084758245598494261920, [], []),
  (3608, 13, 17755031012231488144257906676302124042794631840, [], []),
  (3609, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3610, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3611, 13, 51629896229735152980607416355886365958435046048, [], []),
  (3612, 13, 51942106662514581704588916411703443019518771872, [], []),
  (3613, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3614, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3615, 13, 17442820579452059420276406620485046981710906016, [], []),
  (3616, 13, 40240323588508545368314497680046600993503249056, [], []),
  (3617, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3618, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3619, 13, 51629896229735152980607416355886365958435046048, [], []),
  (3620, 13, 58966841400051727994172667667587676893902602912, [], []),
  (3621, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3622, 13, 17888868744358320167463874609369394999886676640, [], []),
  (3623, 13, 17443397698346357331910440503819251260597535392, [], []),
  (3624, 13, 15257423924778240162102131536711577142163473056, [], []),
  (3625, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3626, 13, 26609080792021057607561697649258859893942715040, [], []),
  (3627, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3628, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3629, 13, 25984659926462200159598697537624705771775263392, [], []),
  (3630, 13, 14722783601204235473123159809937283211255153312, [], []),
  (3631, 13, 15212669987880798335387428508342150986992779936, [], []),
  (3632, 13, 13963670365599772330529064532383923661010174624, [], []),
  (3633, 13, 13964557670289280170453550200665482974737793696, [], []),
  (3634, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3635, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3636, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3637, 13, 24535110894392795539541480661900806328572510880, [], []),
  (3638, 13, 13340136804730422722490550089031328852570342048, [], []),
  (3639, 13, 13941222618418731861971312636280864775636845216, [], []),
  (3640, 13, 46215551780160579730018630814543053390826717250, [], []),
  (3641, 13, 13918932780860591389692012917079532356469006980, [], []),
  (3642, 13, 15368960336480494738858098796033528433053016708, [], []),
  (3643, 13, 17911174321630290820334716344856493277137871492, [], []),
  (3644, 13, 18224152431429493181489789773787936407306642052, [], []),
  (3645, 13, 15101204392115617415743453998931337571113902724, [], []),
  (3646, 13, 13339058960520087837857930102053485874399683204, [], []),
  (3647, 13, 45922870290646424660716113173736019983511863362, [], []),
  (3648, 13, 34529966246248893635640191758878633599144362656, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part37_checked : part37.all packedCert = true := by decide +kernel

def part38 : List Row := [
  (3649, 13, 36130888760500732779324105561607827334445990560, [], []),
  (3650, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3651, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3652, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3653, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3654, 13, 14588368898720150824600601710229510119668908704, [], []),
  (3655, 13, 11733040356086705599236134582651283866238648992, [], []),
  (3656, 13, 36443099193280161503305605617424904395529716384, [], []),
  (3657, 13, 70381555639698319933770359146959926711825793696, [], []),
  (3658, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3659, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3660, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3661, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3662, 13, 1672959683025470034698811148930324911900132000, [], []),
  (3663, 13, 14744474115109865186591351738138048650210771616, [], []),
  (3664, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3665, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3666, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3667, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3668, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3669, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3670, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3671, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3672, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3673, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3674, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3675, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3676, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3677, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3678, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3679, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3680, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3681, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3682, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3683, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3684, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3685, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3686, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3687, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3688, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3689, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3690, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3691, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3692, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3693, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3694, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3695, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3696, 13, 15368894980668722634554351849772202772378223264, [], []),
  (3697, 13, 1985170115804898758680311204747401972983857824, [], []),
  (3698, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3699, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3700, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3701, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3702, 13, 1672959683025470034698811148930324911900132000, [], []),
  (3703, 13, 14744474115109865186591351738138048650210771616, [], []),
  (3704, 13, 12045327012116324613433450434380425643401740960, [], []),
  (3705, 13, 15212789764279008272563601821863664241836360352, [], []),
  (3706, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3707, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3708, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3709, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3710, 13, 14588368898720150824600601710229510119668908704, [], []),
  (3711, 13, 11733040356086705599236134582651283866238648992, [], []),
  (3712, 13, 34708421208661208068401404874575218144164512416, [], []),
  (3713, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3714, 13, 37379731160220129555062789855491086899794215584, [], []),
  (3715, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3716, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3717, 13, 24735208632653266233812037594899465925903319712, [], []),
  (3718, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3719, 13, 13338753900240721383086464495784801364224311968, [], []),
  (3720, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3721, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3722, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3723, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3724, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3725, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3726, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3727, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3728, 13, 37848046809389272641035039939216702491419804320, [], []),
  (3729, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3730, 13, 58963617654356839597917583346885644365444743840, [], []),
  (3731, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3732, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3733, 13, 3278656893625873613502894820082685685011645088, [], []),
  (3734, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3735, 13, 15056685216490975790385535864570077032307819168, [], []),
  (3736, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3737, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3738, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3739, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3740, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3741, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3742, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3743, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3744, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part38_checked : part38.all packedCert = true := by decide +kernel

def part39 : List Row := [
  (3745, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3746, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3747, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3748, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3749, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3750, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3751, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3752, 13, 25203524281822409319784287678625081517528908448, [], []),
  (3753, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3754, 13, 3434762110015587975493644847991224215553508000, [], []),
  (3755, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3756, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3757, 13, 3278656893625873613502894820082685685011645088, [], []),
  (3758, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3759, 13, 15056685216490975790385535864570077032307819168, [], []),
  (3760, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3761, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3762, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3763, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3764, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3765, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3766, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3767, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3768, 13, 13963327212299959411481096199243084918550495904, [], []),
  (3769, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3770, 13, 14900580000101261428394785836661538501765956256, [], []),
  (3771, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3772, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3773, 13, 14900580000101261428394785836661538501765956256, [], []),
  (3774, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3775, 13, 13338753900240721383086464495784801364224311968, [], []),
  (3776, 13, 16506494323042589058454211168726237904274260640, [], []),
  (3777, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3778, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3779, 13, 47883981045693833906421808701217545081163154080, [], []),
  (3780, 13, 50693874940708692422255309203571238630916686496, [], []),
  (3781, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3782, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3783, 13, 16149083502900318236493944137054784208126411424, [], []),
  (3784, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3785, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3786, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3787, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3788, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3789, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3790, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3791, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3792, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3793, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3794, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3795, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3796, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3797, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3798, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3799, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3800, 13, 47727875829304119544431058673309006550621291168, [], []),
  (3801, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3802, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3803, 13, 6534663840148097358785333159195063444967588512, [], []),
  (3804, 13, 6690769056537811720776083187103601975509451424, [], []),
  (3805, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3806, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3807, 13, 15101885603853817888364302840424453667371942560, [], []),
  (3808, 13, 50225559291539549336283059119845623039291097760, [], []),
  (3809, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3810, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3811, 13, 6534663840148097358785333159195063444967588512, [], []),
  (3812, 13, 7939610787655526616702083410371910219844354720, [], []),
  (3813, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3814, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3815, 13, 15101885603853817888364302840424453667371942560, [], []),
  (3816, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3817, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3818, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3819, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3820, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3821, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3822, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3823, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3824, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3825, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3826, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3827, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3828, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3829, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3830, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3831, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3832, 13, 16149159726150508526709759932966848924205777568, [], []),
  (3833, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3834, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3835, 13, 15257990820243532250355052868332992197913805472, [], []),
  (3836, 13, 15257990820243532250355052868332992197913805472, [], []),
  (3837, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3838, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3839, 13, 16149083502900318236493944137054784208126411424, [], []),
  (3840, 13, 36492578972080410686342485807692804044725748384, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part39_checked : part39.all packedCert = true := by decide +kernel

def part40 : List Row := [
  (3841, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3842, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3843, 13, 47883981045693833906421808701217545081163154080, [], []),
  (3844, 13, 60216293140481268503691060905992088993970324128, [], []),
  (3845, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3846, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3847, 13, 13695653081918222649938428631465454311820034720, [], []),
  (3848, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3849, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3850, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3851, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3852, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3853, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3854, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3855, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3856, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3857, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3858, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3859, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3860, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3861, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3862, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3863, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3864, 13, 47727875829304119544431058673309006550621291168, [], []),
  (3865, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3866, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3867, 13, 6534663840148097358785333159195063444967588512, [], []),
  (3868, 13, 6690769056537811720776083187103601975509451424, [], []),
  (3869, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3870, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3871, 13, 15101885603853817888364302840424453667371942560, [], []),
  (3872, 13, 60394699102069513488823346652173275886018167456, [], []),
  (3873, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3874, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3875, 13, 6534663840148097358785333159195063444967588512, [], []),
  (3876, 13, 36127752718598234267603231306999439163403600544, [], []),
  (3877, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3878, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3879, 13, 15101885603853817888364302840424453667371942560, [], []),
  (3880, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3881, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3882, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3883, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3884, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3885, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3886, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3887, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3888, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3889, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3890, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3891, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3892, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3893, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3894, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3895, 13, 17577268320890717057074767568688421794535768736, [], []),
  (3896, 13, 14007939737947841664135744483194596088983126688, [], []),
  (3897, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3898, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3899, 13, 15257990820243532250355052868332992197913805472, [], []),
  (3900, 13, 15257990820243532250355052868332992197913805472, [], []),
  (3901, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3902, 13, 17889478753670145781056267624505498855619494560, [], []),
  (3903, 13, 13695653081918222649938428631465454311820034720, [], []),
  (3904, 13, 19004863648314651925907807759052660206820459168, [], []),
  (3905, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3906, 13, 30354996422682983265479038599606853025410384544, [], []),
  (3907, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3908, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3909, 13, 24735208632653266233812037594899465925903319712, [], []),
  (3910, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3911, 13, 18958890139414165455740051996090198594379907744, [], []),
  (3912, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3913, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3914, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3915, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3916, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3917, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3918, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3919, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3920, 13, 30198891206293268903488288571698314494868521632, [], []),
  (3921, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3922, 13, 4683603841133302871419645071259532459888411296, [], []),
  (3923, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3924, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3925, 13, 3278656893625873613502894820082685685011645088, [], []),
  (3926, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3927, 13, 15056685216490975790385535864570077032307819168, [], []),
  (3928, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3929, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3930, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3931, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3932, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3933, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3934, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3935, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3936, 13, 15034384471292445167244000146297428670801838752, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part40_checked : part40.all packedCert = true := by decide +kernel

def part41 : List Row := [
  (3937, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3938, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3939, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3940, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3941, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3942, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3943, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3944, 13, 25203524281822409319784287678625081517528908448, [], []),
  (3945, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3946, 13, 3434762110015587975493644847991224215553508000, [], []),
  (3947, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3948, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3949, 13, 3278656893625873613502894820082685685011645088, [], []),
  (3950, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3951, 13, 15056685216490975790385535864570077032307819168, [], []),
  (3952, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3953, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3954, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3955, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3956, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3957, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3958, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3959, 13, 15034384471292445167244000146297428670801838752, [], []),
  (3960, 13, 18959042585914546036171683587914328026538640032, [], []),
  (3961, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3962, 13, 14900580000101261428394785836661538501765956256, [], []),
  (3963, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3964, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3965, 13, 14900580000101261428394785836661538501765956256, [], []),
  (3966, 13, 14722174038513016443262500090480351609718112928, [], []),
  (3967, 13, 18958890139414165455740051996090198594379907744, [], []),
  (3968, 13, 20209403337354963168908395671858284205819626144, [], []),
  (3969, 13, 20208156688749867856267602714936897219175973536, [], []),
  (3970, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3971, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3972, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3973, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3974, 13, 14588368898720150824600601710229510119668908704, [], []),
  (3975, 13, 20185736018170878056897591041162189863176438432, [], []),
  (3976, 13, 20364261905139582218258352742845435749717836448, [], []),
  (3977, 13, 4482853578040328550532311651284018461653664416, [], []),
  (3978, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3979, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3980, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3981, 13, 24534501257264808745725532059830679351336174240, [], []),
  (3982, 13, 1672959683025470034698811148930324911900132000, [], []),
  (3983, 13, 14744474115109865186591351738138048650210771616, [], []),
  (3984, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3985, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3986, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3987, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3988, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3989, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3990, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3991, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3992, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3993, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3994, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3995, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3996, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3997, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3998, 13, 25002816906433951831697782143556294942961762976, [], []),
  (3999, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4000, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4001, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4002, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4003, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4004, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4005, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4006, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4007, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4008, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4009, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4010, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4011, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4012, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4013, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4014, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4015, 13, 25002816906433951831697782143556294942961762976, [], []),
  (4016, 13, 15368894980668722634554351849772202772378223264, [], []),
  (4017, 13, 1985170115804898758680311204747401972983857824, [], []),
  (4018, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4019, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4020, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4021, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4022, 13, 1672959683025470034698811148930324911900132000, [], []),
  (4023, 13, 14744474115109865186591351738138048650210771616, [], []),
  (4024, 13, 20185812241421068347113406837074254579255804576, [], []),
  (4025, 13, 15212789764279008272563601821863664241836360352, [], []),
  (4026, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4027, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4028, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4029, 13, 24534501257264808745725532059830679351336174240, [], []),
  (4030, 13, 14588368898720150824600601710229510119668908704, [], []),
  (4031, 13, 20185736018170878056897591041162189863176438432, [], []),
  (4032, 13, 49962382089933849291689031289359104482685796362, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part41_checked : part41.all packedCert = true := by decide +kernel

def part42 : List Row := [
  (4033, 13, 16417226029097543503270539730912666573773742724, [], []),
  (4034, 13, 20365546832954398966015152423699796867662488196, [], []),
  (4035, 13, 17911174321630290820334716344856493277137871492, [], []),
  (4036, 13, 20722445679666445295068316587621070624611377796, [], []),
  (4037, 13, 15101204392115617415743453998931337571113902724, [], []),
  (4038, 13, 13339058960520087837857930102053485874399683204, [], []),
  (4039, 13, 45855951640415935989569987909768218571616337930, [], []),
  (4040, 13, 15792767033308942229368226550238601967811232416, [], []),
  (4041, 13, 16506842622921771208588622083747396186419561120, [], []),
  (4042, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4043, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4044, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4045, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4046, 13, 13340136804730422722490550089031328852570342048, [], []),
  (4047, 13, 12982187129042371101592383884676325973343404704, [], []),
  (4048, 13, 20209365374712117262852790415882797587429917344, [], []),
  (4049, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4050, 13, 16150031293910195354181445779386778347637899936, [], []),
  (4051, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4052, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4053, 13, 16150031293910195354181445779386778347637899936, [], []),
  (4054, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4055, 13, 14588205566178975007301105084758245598494261920, [], []),
  (4056, 13, 17755031012231488144257906676302124042794631840, [], []),
  (4057, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4058, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4059, 13, 19003906004284851324540660523001813075185697440, [], []),
  (4060, 13, 19003906004284851324540660523001813075185697440, [], []),
  (4061, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4062, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4063, 13, 17442820579452059420276406620485046981710906016, [], []),
  (4064, 13, 20253977602612928459686283169381527255065363104, [], []),
  (4065, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4066, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4067, 13, 19003906004284851324540660523001813075185697440, [], []),
  (4068, 13, 19003906004284851324540660523001813075185697440, [], []),
  (4069, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4070, 13, 17888868744358320167463874609369394999886676640, [], []),
  (4071, 13, 17443397698346357331910440503819251260597535392, [], []),
  (4072, 13, 15257423924778240162102131536711577142163473056, [], []),
  (4073, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4074, 13, 16150031293910195354181445779386778347637899936, [], []),
  (4075, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4076, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4077, 13, 16150031293910195354181445779386778347637899936, [], []),
  (4078, 13, 14722783601204235473123159809937283211255153312, [], []),
  (4079, 13, 15212669987880798335387428508342150986992779936, [], []),
  (4080, 13, 13963670365599772330529064532383923661010174624, [], []),
  (4081, 13, 13964557670289280170453550200665482974737793696, [], []),
  (4082, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4083, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4084, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4085, 13, 24535110894392795539541480661900806328572510880, [], []),
  (4086, 13, 13340136804730422722490550089031328852570342048, [], []),
  (4087, 13, 13941222618418731861971312636280864775636845216, [], []),
  (4088, 13, 45699808340310370579470741935928417961203777546, [], []),
  (4089, 13, 13918932780860591389692012917079532356469006980, [], []),
  (4090, 13, 15368960336480494738858098796033528433053016708, [], []),
  (4091, 13, 17911174321630290820334716344856493277137871492, [], []),
  (4092, 13, 18224152431429493181489789773787936407306642052, [], []),
  (4093, 13, 15101204392115617415743453998931337571113902724, [], []),
  (4094, 13, 13339058960520087837857930102053485874399683204, [], []),
  (4095, 13, 45699808323030406634266835588178081271441797120, [], [])
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem part42_checked : part42.all packedCert = true := by decide +kernel

def allPivots : List Row := part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15 ++ part16 ++ part17 ++ part18 ++ part19 ++ part20 ++ part21 ++ part22 ++ part23 ++ part24 ++ part25 ++ part26 ++ part27 ++ part28 ++ part29 ++ part30 ++ part31 ++ part32 ++ part33 ++ part34 ++ part35 ++ part36 ++ part37 ++ part38 ++ part39 ++ part40 ++ part41 ++ part42
theorem allPivots_checked : allPivots.all packedCert = true := by
  simp [allPivots, List.all_append, part0_checked, part1_checked, part2_checked, part3_checked, part4_checked, part5_checked, part6_checked, part7_checked, part8_checked, part9_checked, part10_checked, part11_checked, part12_checked, part13_checked, part14_checked, part15_checked, part16_checked, part17_checked, part18_checked, part19_checked, part20_checked, part21_checked, part22_checked, part23_checked, part24_checked, part25_checked, part26_checked, part27_checked, part28_checked, part29_checked, part30_checked, part31_checked, part32_checked, part33_checked, part34_checked, part35_checked, part36_checked, part37_checked, part38_checked, part39_checked, part40_checked, part41_checked, part42_checked]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem allPivots_ids : allPivots.map Prod.fst = (List.range 4095).map (1 + ·) := by decide +kernel


end PEqualNP.Outside.L_pcx_118.Finite
namespace PEqualNP.Outside.L_pcx_118.High

open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.Outside.L_pcx_118.Graph
open PEqualNP.Outside.L_pcx_118.Linear (V assignment formMask forms)
open PEqualNP.Outside.L_pcx_118.Finite (Row packedCert)

abbrev K := PEqualNP.Outside.L_pcx_118.Finite.Label

local instance : Fintype K := Fintype.ofFinset
  (p := {x | x ∈ PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical})
  ((PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical).toFinset)
  (by intro x; simp)

theorem label_card : Fintype.card K = 22 := by
  exact (Fintype.card_ofFinset (p := {x | x ∈ PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical})
    ((PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical).toFinset) (by intro x; simp)).trans (by decide +kernel)

def ax (k : K) : LinClause V := PEqualNP.Outside.L_pcx_118.Linear.linearOf k.val.1

theorem row_exists (row : Nat × Bool) (h : row ∈ PEqualNP.Outside.L_pcx_118.Linear.axioms) :
    ∃ k : K, k.val.1 = row := by
  have eq : (PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical).map Prod.fst =
      PEqualNP.Outside.L_pcx_118.Linear.axioms := by decide +kernel
  rw [← eq] at h
  obtain ⟨p,hp,he⟩ := List.mem_map.mp h
  exact ⟨⟨p,hp⟩,he⟩

theorem row_mem (k : K) : k.val.1 ∈ PEqualNP.Outside.L_pcx_118.Linear.axioms := by
  have eq : (PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical).map Prod.fst =
      PEqualNP.Outside.L_pcx_118.Linear.axioms := by decide +kernel
  rw [← eq]
  exact List.mem_map.mpr ⟨k.val,k.property,rfl⟩

theorem bad_iff (a : Nat) (k : K) :
    (¬ LinClauseSat (assignment a) (ax k)) ↔ PEqualNP.Outside.L_pcx_118.Finite.bad a k := by
  have hl := List.all_eq_true.mp PEqualNP.Outside.L_pcx_118.Linear.all_rows_small _ (row_mem k)
  have hs : k.val.1.1 < 4096 := of_decide_eq_true hl
  rw [ax, ← PEqualNP.Outside.L_pcx_118.Linear.false_on_spec a _ hs]
  simp [PEqualNP.Outside.L_pcx_118.Finite.bad, PEqualNP.Outside.L_pcx_118.Finite.falseAxiom]

def phpIndex (C : Clause V) : Bool :=
  (List.finRange 4).any (fun i => PEqualNP.Outside.L_pcx_118.Linear.pigeon i == C) ||
  (List.finRange 4).any (fun i => (List.finRange 4).any (fun j =>
    (i != j) && (List.finRange 3).any (fun h => PEqualNP.Outside.L_pcx_118.Linear.collision i j h == C)))

theorem ax_index : PEqualNP.Outside.L_pcx_118.Linear.axioms.all
    (fun x => phpIndex (PEqualNP.Outside.L_pcx_118.Linear.clauseOf x)) = true := by decide +kernel

theorem verify_php {C : Clause V} (h : phpIndex C = true) : C ∈ PHP 4 3 := by
  simp only [phpIndex, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  rcases h with ⟨i, _, e⟩ | ⟨i, _, j, _, ne, h, _, e⟩
  · exact Or.inl ⟨i, e.symm⟩
  · exact Or.inr ⟨i,j,h,ne,e.symm⟩

theorem formula_range :
    ((linOfClause : Clause V → LinClause V) '' PHP 4 3) = Set.range ax := by
  ext C
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨row,hm,e⟩ := PEqualNP.Outside.L_pcx_118.Linear.php_covered hD
    obtain ⟨k,hk⟩ := row_exists row hm
    exact ⟨k, by rw [ax, PEqualNP.Outside.L_pcx_118.Linear.linearOf, hk, e]⟩
  · rintro ⟨k,rfl⟩
    refine ⟨PEqualNP.Outside.L_pcx_118.Linear.clauseOf k.val.1, ?_, rfl⟩
    exact verify_php (List.all_eq_true.mp ax_index _ (row_mem k))

def pointA (k : K) (a : V → Bool) : Prop :=
  ∃ n, PEqualNP.Outside.L_pcx_118.Finite.point k n ∧ assignment n = a

theorem point_exists (k : K) : ∃ a, pointA k a := by
  obtain ⟨n,hn⟩ := PEqualNP.Outside.L_pcx_118.Finite.label_has_point k
  exact ⟨assignment n, n, hn, rfl⟩

theorem point_only {k : K} {a : V → Bool} (h : pointA k a) (j : K) :
    (¬ LinClauseSat a (ax j)) ↔ j = k := by
  obtain ⟨n,hn,rfl⟩ := h
  exact (bad_iff n j).trans (PEqualNP.Outside.L_pcx_118.Finite.label_point_unique hn j)

def side (f : Finset V) (a : V → Bool) : Bool :=
  decide (Odd (f.filter (fun v => a v = true)).card)

theorem side_mask (f : Finset V) (a : Nat) :
    side f (assignment a) = PEqualNP.Outside.L_pcx_118.Finite.parity a (formMask f) :=
  (PEqualNP.Outside.L_pcx_118.Linear.parity_form a f).symm

theorem lift_force {f : Finset V} {a : Nat}
    (h : PEqualNP.Outside.L_pcx_118.Finite.forced (formMask f) a) :
    Forced (fun u k => ¬ LinClauseSat u (ax k)) pointA (side f) (assignment a) := by
  rcases h with ⟨k,ka,b,kb,ne⟩ | h
  · exact Or.inl ⟨k,⟨a,ka,rfl⟩,assignment b,⟨b,kb,rfl⟩,by simpa only [side_mask] using ne⟩
  · refine Or.inr ?_
    intro k bka u hbu
    obtain ⟨b,kb,rfl⟩ := hbu
    simpa only [side_mask] using h k ((bad_iff a k).mp bka) b kb

theorem high_impossible (rows : List Row)
    (valid : rows.all packedCert = true)
    (ids : rows.map Prod.fst = (List.range 4095).map (1 + ·))
    {C : ClauseMap V} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule (linOfClause '' PHP 4 3) C P i)
    (fr : ∀ a, FalseAt C a r)
    (prev : ∀ j < r, ∃ a, LinClauseSat a (C j))
    (rc : LocalEdge P r r c) (rd : LocalEdge P r r d) (ne : c ≠ d)
    (size : (Live P r).card ≤ 47) (wcount : 3 ≤ (WithArity P r 1).card)
    (f : Finset V) (nf : f ≠ ∅)
    (br : ∀ a, if Odd (f.filter (fun v => a v = true)).card
      then FalseAt C a c else FalseAt C a d) : False := by
  have hq : 0 < formMask f :=
    Nat.pos_of_ne_zero (PEqualNP.Outside.L_pcx_118.Linear.mask_nz (Finset.nonempty_iff_ne_empty.mpr nf))
  have hlt := PEqualNP.Outside.L_pcx_118.Linear.mask_lt f
  obtain ⟨p,hp⟩ := PEqualNP.Outside.L_pcx_118.Finite.forced_exists rows valid ids (formMask f) hq hlt
  have bc : ∀ a, FalseAt C a (if side f a then c else d) := by
    intro a
    by_cases h : Odd (f.filter (fun v => a v = true)).card <;> simpa [side,h] using br a
  obtain ⟨z,hz,hw,hs,hn⟩ := high_weak_shared rules fr rc rd ne size wcount
    label_card ax formula_range pointA point_exists point_only (side f) bc
    ⟨assignment p,lift_force hp⟩
  have false_p : ¬ LinClauseSat (assignment p) (C z) := hw _ (lift_force hp)
  have hpz (a : Nat) : PEqualNP.Outside.L_pcx_118.Finite.possible p (forms (C z)) a = true ↔
      FalseAt C (assignment a) z := PEqualNP.Outside.L_pcx_118.Linear.possible_clause false_p a
  have hnz (a : Nat) : PEqualNP.Outside.L_pcx_118.Finite.possible p (forms (C z)) a = false ↔
      ¬ FalseAt C (assignment a) z := by
    rw [← hpz]
    cases PEqualNP.Outside.L_pcx_118.Finite.possible p (forms (C z)) a <;> simp
  refine PEqualNP.Outside.L_pcx_118.Finite.no_shared rows valid ids (formMask f) p (forms (C z)) hq hlt
    (PEqualNP.Outside.L_pcx_118.Linear.possible_nonempty false_p (prev z hz))
    (PEqualNP.Outside.L_pcx_118.Linear.forms_lt (C z))
    (fun a ha => (hpz a).2 (hw _ (lift_force ha))) ?_ ?_
  · intro a ha
    obtain ⟨k,hk,hh⟩ := hs _ ((hpz a).1 ha)
    exact ⟨k,(bad_iff a k).1 hk,fun b hb => (hpz b).2 (hh _ ⟨b,hb,rfl⟩)⟩
  · intro a ha
    obtain ⟨k,hk,b,⟨n,hn',rfl⟩,hb⟩ := hn _ ((hnz a).1 ha)
    exact ⟨k,(bad_iff a k).1 hk,n,hn',(hnz n).2 hb⟩

end PEqualNP.Outside.L_pcx_118.High
namespace PEqualNP.Outside.L_pcx_118.Orientation

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem axis_sat (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, h]

def lower (a : V → Bool) (S : Finset V) (v : V) : Bool :=
  if v ∈ S then false else a v

theorem filter_lower (a : V → Bool) (S f : Finset V) :
    f.filter (fun x => lower a S x = true) = (f.filter (fun x => a x = true)) \ S := by
  ext x
  by_cases hx : x ∈ S <;> simp [lower, hx]

theorem lower_sat (a : V → Bool) (S : Finset V) (q : LinEq V)
    (heven : ((q.1.filter (fun x => a x = true)) ∩ S).card % 2 = 0) :
    LinEqSat (lower a S) q ↔ LinEqSat a q := by
  unfold LinEqSat
  rw [filter_lower, Nat.odd_iff, Nat.odd_iff]
  have hc := Finset.card_sdiff_add_card_inter (q.1.filter (fun x => a x = true)) S
  have hh : ((q.1.filter (fun x => a x = true)) \ S).card % 2 = 1 ↔
      (q.1.filter (fun x => a x = true)).card % 2 = 1 := by omega
  exact iff_congr hh Iff.rfl

theorem weak_lost_neg_injective {C D : LinClause V} {f : Finset V}
    (shape : ∀ q ∈ D, q.1.card = 1 ∨ q.1 = f)
    (weak : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D)
    {a : V → Bool} (hD : ¬ LinClauseSat a D)
    {v w : V} (hv : ({v}, false) ∈ C) (hw : ({w}, false) ∈ C)
    (hv' : ({v}, false) ∉ D) (hw' : ({w}, false) ∉ D) : v = w := by
  by_contra hne
  have hc : ¬ LinClauseSat a C := fun h => hD (weak _ h)
  have value {x : V} (hx : ({x}, false) ∈ C) : a x = true := by
    cases h : a x
    · exact False.elim (hc ⟨_, hx, (axis_sat _ _ _).2 h⟩)
    · rfl
  have hal : a v = true := value hv
  have har : a w = true := value hw
  have absent {x : V} (hx : a x = true) (hx' : ({x}, false) ∉ D)
      (s : Bool) : ({x}, s) ∉ D := by
    cases s
    · exact hx'
    · intro hm
      exact hD ⟨_, hm, (axis_sat _ _ _).2 hx⟩
  have protect {S : Finset V} (hs : S ⊆ {v, w})
      (hp : ((f.filter (fun x => a x = true)) ∩ S).card % 2 = 0) :
      ¬ LinClauseSat (lower a S) D := by
    rintro ⟨q, hq, h⟩
    apply hD
    refine ⟨q, hq, ?_⟩
    rcases shape q hq with h1 | hf
    · rcases q with ⟨Q, s⟩
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      change Q = {x} at hx
      subst Q
      have hxS : x ∉ S := by
        intro hsx
        have hxv : x = v ∨ x = w := by simpa using hs hsx
        rcases hxv with rfl | rfl
        · exact absent hal hv' s hq
        · exact absent har hw' s hq
      exact (axis_sat _ _ _).2 (by
        simpa [lower, hxS] using (axis_sat _ _ _).1 h)
    · exact (lower_sat a S q (by simpa only [hf] using hp)).1 h
  have relapse {S : Finset V} (hs : S ⊆ {v, w})
      (hp : ((f.filter (fun x => a x = true)) ∩ S).card % 2 = 0)
      (hx : v ∈ S ∨ w ∈ S) : False := by
    apply protect hs hp
    apply weak
    rcases hx with h | h
    · exact ⟨_, hv, (axis_sat _ _ _).2 (by simp [lower, h])⟩
    · exact ⟨_, hw, (axis_sat _ _ _).2 (by simp [lower, h])⟩
  by_cases hvf : v ∈ f
  · by_cases hwf : w ∈ f
    · have hsub : ({v, w} : Finset V) ⊆ f.filter (fun x => a x = true) := by
        intro x hx
        rcases (show x = v ∨ x = w by simpa using hx) with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hvf, hal⟩
        · exact Finset.mem_filter.mpr ⟨hwf, har⟩
      apply relapse (S := {v, w}) (fun _ h => h) _ (Or.inl (by simp))
      rw [Finset.inter_eq_right.mpr hsub]
      simp [hne]
    · apply relapse (S := {w}) (by simp) _ (Or.inr (by simp))
      have he : (f.filter (fun x => a x = true)) ∩ {w} = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨h, rfl⟩
        exact hwf (Finset.mem_filter.mp h).1
      simp [he]
  · apply relapse (S := {v}) (by simp) _ (Or.inl (by simp))
    have he : (f.filter (fun x => a x = true)) ∩ {v} = ∅ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨h, rfl⟩
      exact hvf (Finset.mem_filter.mp h).1
    simp [he]


def neg (v : V) : LinEq V := ({v}, false)

theorem loss_edge {E : ℕ → ℕ → Prop} {C : ℕ → LinClause V}
    {r t : ℕ} {v : V} (route : Relation.ReflTransGen E r t)
    (hroot : neg v ∉ C r) (htip : neg v ∈ C t) :
    ∃ i j, Relation.ReflTransGen E r i ∧ E i j ∧ Relation.ReflTransGen E j t ∧
      neg v ∉ C i ∧ neg v ∈ C j := by
  induction route with
  | refl => exact (hroot htip).elim
  | @tail u t walk step ih =>
    by_cases h : neg v ∈ C u
    · obtain ⟨i, j, pr, edge, su, hm, hp⟩ := ih h
      exact ⟨i, j, pr, edge, su.tail step, hm, hp⟩
    · exact ⟨u, t, walk, step, .refl, h, htip⟩

theorem loss_edge_internal {E : ℕ → ℕ → Prop} {j t : ℕ}
    (route : Relation.ReflTransGen E j t) (exit : ∃ k, E t k) : ∃ k, E j k := by
  rcases route.cases_head with rfl | ⟨k, hk, _⟩
  · exact exit
  · exact ⟨k,hk⟩

theorem loss_resolvent {C D R : LinClause V} {v : V} {f : Finset V}
    (hR : R = C.erase (f, false) ∪ D.erase (f, true))
    (hn : neg v ∉ R) (hm : neg v ∈ C ∨ neg v ∈ D) : neg v ∈ C ∧ neg v ∉ D ∧ f = {v} := by
  have hbad : neg v ∉ D := by
    intro h
    apply hn
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp [neg], h⟩)
  have hC : neg v ∈ C := hm.resolve_right hbad
  refine ⟨hC, hbad, ?_⟩
  by_contra he
  apply hn
  rw [hR]
  apply Finset.mem_union_left
  exact Finset.mem_erase.mpr ⟨fun h => he ((congrArg Prod.fst h).symm), hC⟩

theorem collision_heads_card {S : Finset (Fin 4 × Fin 3)}
    (cover : ∀ (i j : Fin 4) (h : Fin 3), i ≠ j → (i, h) ∈ S ∨ (j, h) ∈ S) : 9 ≤ S.card := by
  let T := Finset.univ \ S
  have hinj : Set.InjOn Prod.snd (T : Set (Fin 4 × Fin 3)) := by
    rintro ⟨i,h⟩ hi ⟨j,k⟩ hj eq
    change h = k at eq
    subst k
    have hi' : (i,h) ∉ S := (Finset.mem_sdiff.mp hi).2
    have hj' : (j,h) ∉ S := (Finset.mem_sdiff.mp hj).2
    by_cases he : i = j
    · simp [he]
    · exact False.elim ((cover i j h he).elim hi' hj')
  have hT : T.card ≤ 3 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using (Finset.card_le_univ (T.image Prod.snd))
  have hCard : T.card = 12 - S.card := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  omega

theorem no_axis_in_form {a : V → Bool} {D : LinClause V} {v : V}
    (hD : ¬ LinClauseSat a D) (hav : a v = true) (hn : neg v ∉ D)
    {q : LinEq V} (hq : q ∈ D) (hcard : q.1.card = 1) : v ∉ q.1 := by
  intro h
  rcases q with ⟨Q, sign⟩
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  change Q = {x} at hx
  subst Q
  have he : v = x := Finset.mem_singleton.mp h
  subst x
  cases sign
  · exact hn hq
  · exact hD ⟨_, hq, (axis_sat _ _ _).2 hav⟩

theorem keep_axis_free_parity (a : V → Bool) (q : LinEq V) {v : V}
    (hv : v ∉ q.1) : LinEqSat (lower a {v}) q ↔ LinEqSat a q := by
  apply lower_sat
  have h : (q.1.filter (fun x => a x = true)) ∩ {v} = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨hm, rfl⟩
    exact hv (Finset.mem_filter.mp hm).1
  simp [h]

theorem weak_lost_axis_supported {C D : LinClause V}
    (weak : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D)
    {a : V → Bool} (hD : ¬ LinClauseSat a D) {v : V}
    (hin : neg v ∈ C) (hout : neg v ∉ D) :
    ∃ q ∈ D, q.1.card ≠ 1 ∧ v ∈ q.1 := by
  have hav : a v = true := by
    cases h : a v
    · exact False.elim (hD (weak _ ⟨_, hin, (axis_sat _ _ _).2 h⟩))
    · rfl
  by_contra hn
  have hnew : LinClauseSat (lower a {v}) D := by
    exact weak _ ⟨_, hin, (axis_sat _ _ _).2 (by simp [lower])⟩
  obtain ⟨q, hq, hs⟩ := hnew
  have hv : v ∉ q.1 := by
    by_cases hcard : q.1.card = 1
    · exact no_axis_in_form hD hav hout hq hcard
    · exact fun h => hn ⟨q, hq, hcard, h⟩
  exact hD ⟨q, hq, (keep_axis_free_parity a q hv).1 hs⟩

theorem flip_axis_parity (a : V → Bool) (q : LinEq V) {v : V}
    (hv : v ∈ q.1) (hav : a v = true) :
    LinEqSat (lower a {v}) q ↔ ¬ LinEqSat a q := by
  unfold LinEqSat
  rw [filter_lower, Nat.odd_iff, Nat.odd_iff]
  have hs : ({v} : Finset V) ⊆ q.1.filter (fun x => a x = true) := by
    simp [hv, hav]
  have hn := Finset.card_sdiff_add_card_inter (q.1.filter (fun x => a x = true)) {v}
  rw [Finset.inter_eq_right.mpr hs, Finset.card_singleton] at hn
  have hops : ((q.1.filter (fun x => a x = true)) \ {v}).card % 2 = 1 ↔
      ¬ (q.1.filter (fun x => a x = true)).card % 2 = 1 := by omega
  cases h : q.2 <;> simp [hops, h]

theorem weak_pure_recovers_axis {C D : LinClause V}
    (pure : ∀ q ∈ D, q.1.card = 1)
    (weak : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D)
    {a : V → Bool} (hD : ¬ LinClauseSat a D) {q : LinEq V}
    (hq : q ∈ C) {v : V} (hv : v ∈ q.1) (hav : a v = true) : neg v ∈ D := by
  by_contra hn
  have hnq : ¬ LinEqSat a q := fun hs => hD (weak _ ⟨_, hq, hs⟩)
  have news : LinClauseSat (lower a {v}) D :=
    weak _ ⟨_, hq, (flip_axis_parity a q hv hav).2 hnq⟩
  obtain ⟨p, hp, hs⟩ := news
  have hvp : v ∉ p.1 := no_axis_in_form hD hav hn hp (pure p hp)
  exact hD ⟨p, hp, (keep_axis_free_parity a p hvp).1 hs⟩
end PEqualNP.Outside.L_pcx_118.Orientation
namespace PEqualNP.Outside.L_pcx_118.ParShape

variable {X : Type} [DecidableEq X]

abbrev Edge (P : ℕ → List ℕ) (i j : ℕ) : Prop := j ∈ P i
abbrev Reach (P : ℕ → List ℕ) := Relation.ReflTransGen (Edge P)

def Pivot (C : ℕ → Finset (X × Bool)) (P : ℕ → List ℕ) (i : ℕ) : Prop :=
  ∃ j k f, P i = [j,k] ∧ (f,false) ∈ C j ∧ (f,true) ∈ C k ∧
    C i = (C j).erase (f,false) ∪ (C k).erase (f,true)

structure Rules (C : ℕ → Finset (X × Bool)) (P : ℕ → List ℕ)
    (r u v : ℕ) : Prop where
  dec : ∀ {i j}, Edge P i j → j < i
  root : C r = ∅
  clean : ∀ {i}, Reach P r i → ∀ f, (f,false) ∈ C i → (f,true) ∉ C i
  cases : ∀ {i}, Reach P r i →
    (i = u ∨ i = v) ∨ (P i = [] ∧ C i = ∅) ∨
    (∃ j k, P i = [j,k] ∧ C i = C j ∪ C k) ∨ Pivot C P i

def opp (q : X × Bool) : X × Bool := (q.1, !q.2)

theorem all_origins {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v : ℕ}
    (R : Rules C P r u v) (i : ℕ) (hi : Reach P r i) : C i ⊆ C u ∪ C v := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases R.cases hi with (rfl | rfl) | ⟨_,heq⟩ | ⟨j,k,hp,hc⟩ | ⟨j,k,f,hp,_,_,hc⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
    · simp [heq]
    all_goals
      have hj : Edge P i j := by simp [Edge,hp]
      have hk : Edge P i k := by simp [Edge,hp]
      have sj := ih j (R.dec hj) (hi.tail hj)
      have sk := ih k (R.dec hk) (hi.tail hk)
      intro x hx
      rw [hc] at hx
      rcases Finset.mem_union.mp hx with hm | hm
      · apply sj
        first | exact hm | exact Finset.mem_of_mem_erase hm
      · apply sk
        first | exact hm | exact Finset.mem_of_mem_erase hm

def Built (C : ℕ → Finset (X × Bool)) (u v i : ℕ) : Prop :=
  ∃ a b : Bool, (a = true → u ≤ i) ∧ (b = true → v ≤ i) ∧
    C i = (if a then C u else ∅) ∪ (if b then C v else ∅)

theorem before_first {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v t : ℕ}
    (R : Rules C P r u v) (no : ∀ i < t, Reach P r i → ¬ Pivot C P i)
    (i : ℕ) (hi : Reach P r i) (lt : i < t) : Built C u v i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases R.cases hi with (rfl | rfl) | ⟨hp,hc⟩ | ⟨j,k,hp,hc⟩ | piv
    · exact ⟨true, false, by simp, by simp, by simp⟩
    · exact ⟨false, true, by simp, by simp, by simp⟩
    · exact ⟨false, false, by simp, by simp, by simp [hc]⟩
    · have hj : Edge P i j := by simp [Edge,hp]
      have hk : Edge P i k := by simp [Edge,hp]
      have ji := R.dec hj
      have ki := R.dec hk
      obtain ⟨a,b,ha,hb,hj'⟩ := ih j ji (hi.tail hj) (ji.trans lt)
      obtain ⟨c,d,hc',hd,hk'⟩ := ih k ki (hi.tail hk) (ki.trans lt)
      refine ⟨a || c, b || d, ?_, ?_, ?_⟩
      · intro hab
        rcases (show a = true ∨ c = true by simpa using hab) with h | h
        · exact (ha h).trans ji.le
        · exact (hc' h).trans ki.le
      · intro hbd
        rcases (show b = true ∨ d = true by simpa using hbd) with h | h
        · exact (hb h).trans ji.le
        · exact (hd h).trans ki.le
      · rw [hc, hj', hk']
        cases a <;> cases b <;> cases c <;> cases d <;>
          simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
    · exact False.elim (no i lt hi piv)

theorem one_step_persist {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i j : ℕ}
    (R : Rules C P r u v) (hi : Reach P r i) (e : Edge P i j)
    (neU : i ≠ u) (neV : i ≠ v) {q : X × Bool} (hq : q ∈ C j)
    (missing : opp q ∉ C u ∪ C v) : q ∈ C i := by
  rcases R.cases hi with (he | he) | ⟨p0,_⟩ | ⟨a,b,eq,hu⟩ | ⟨a,b,f,eq,ha,hb,hu⟩
  · exact (neU he).elim
  · exact (neV he).elim
  · simpa [Edge,p0] using e
  · rw [hu]
    rcases (show j = a ∨ j = b by simpa [Edge,eq] using e) with rfl | rfl
    · exact Finset.mem_union_left _ hq
    · exact Finset.mem_union_right _ hq
  · rw [hu]
    have ea : Edge P i a := by simp [Edge,eq]
    have eb : Edge P i b := by simp [Edge,eq]
    rcases (show j = a ∨ j = b by simpa [Edge,eq] using e) with rfl | rfl
    · apply Finset.mem_union_left
      refine Finset.mem_erase.mpr ⟨?_,hq⟩
      intro h
      subst q
      exact missing (all_origins R b (hi.tail eb) (by simpa [opp] using hb))
    · apply Finset.mem_union_right
      refine Finset.mem_erase.mpr ⟨?_,hq⟩
      intro h
      subst q
      exact missing (all_origins R a (hi.tail ea) (by simpa [opp] using ha))

theorem unopposed_persists {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i : ℕ}
    (R : Rules C P r u v) (path : Reach P r i) (hu : u ≤ i) (hv : v ≤ i)
    {q : X × Bool} (hq : q ∈ C i) (miss : opp q ∉ C u ∪ C v) : q ∈ C r := by
  induction path with
  | refl => exact hq
  | @tail a b route e ih =>
    have ua := hu.trans_lt (R.dec e)
    have va := hv.trans_lt (R.dec e)
    exact ih ua.le va.le (one_step_persist R route e (ne_of_gt ua) (ne_of_gt va) hq miss)


theorem no_both_forms {A B : Finset (X × Bool)} {f : X} {q : X × Bool}
    (nA : (f,true) ∉ A) (nB : (f,false) ∉ B)
    (hq : q ∈ A.erase (f,false) ∪ B.erase (f,true)) :
    opp q ∈ A ∪ B → opp q ∈ A.erase (f,false) ∪ B.erase (f,true) := by
  have neg : q ≠ (f,false) := by
    intro h
    subst q
    rcases Finset.mem_union.mp hq with h | h
    · simpa using h
    · exact nB (Finset.mem_of_mem_erase h)
  have pos : q ≠ (f,true) := by
    intro h
    subst q
    rcases Finset.mem_union.mp hq with h | h
    · exact nA (Finset.mem_of_mem_erase h)
    · simpa using h
  intro ho
  rcases Finset.mem_union.mp ho with hm | hm
  · apply Finset.mem_union_left
    refine Finset.mem_erase.mpr ⟨?_,hm⟩
    intro e
    exact pos (by simpa [opp] using congrArg opp e)
  · apply Finset.mem_union_right
    refine Finset.mem_erase.mpr ⟨?_,hm⟩
    intro e
    exact neg (by simpa [opp] using congrArg opp e)

theorem built_single_source {C : ℕ → Finset (X × Bool)} {u v j : ℕ}
    (build : Built C u v j) {q : X × Bool} (hit : q ∈ C j)
    (avoid : opp q ∉ C j) (other : opp q ∈ C u ∪ C v) :
    (u ≤ j ∧ C j = C u) ∨ (v ≤ j ∧ C j = C v) := by
  obtain ⟨a,b,ha,hb,eq⟩ := build
  cases a <;> cases b
  · simp at eq
    rw [eq] at hit
    simp at hit
  · exact Or.inr ⟨hb rfl, by simpa using eq⟩
  · exact Or.inl ⟨ha rfl, by simpa using eq⟩
  · simp at eq
    exact False.elim (avoid (by rwa [eq]))

theorem single_form_sources {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v : ℕ}
    (R : Rules C P r u v) (existsPivot : ∃ i, Reach P r i ∧ Pivot C P i) :
    ∃ f : X, (C u = {(f,false)} ∧ C v = {(f,true)}) ∨
             (C u = {(f,true)} ∧ C v = {(f,false)}) := by
  classical
  let t := Nat.find existsPivot
  have found : Reach P r t ∧ Pivot C P t := Nat.find_spec existsPivot
  have earlier (i : ℕ) (lt : i < t) (hi : Reach P r i) : ¬ Pivot C P i := by
    intro piv
    exact (Nat.not_le_of_lt lt) (Nat.find_min' existsPivot ⟨hi,piv⟩)
  obtain ⟨j,k,f,hp,hj,hk,ht⟩ := found.2
  have ej : Edge P t j := by simp [Edge,hp]
  have ek : Edge P t k := by simp [Edge,hp]
  have rj := found.1.tail ej
  have rk := found.1.tail ek
  have jlt := R.dec ej
  have klt := R.dec ek
  have nhj := R.clean rj f hj
  have nhk : (f,false) ∉ C k := fun h => R.clean rk f h hk
  have js := built_single_source (before_first R earlier j rj jlt) hj
    (by simpa [opp] using nhj)
    (by simpa [opp] using all_origins R k rk hk)
  have ks := built_single_source (before_first R earlier k rk klt) hk
    (by simpa [opp] using nhk)
    (by simpa [opp] using all_origins R j rj hj)
  have hsource :
      ((u ≤ j ∧ C j = C u) ∧ (v ≤ k ∧ C k = C v)) ∨
      ((v ≤ j ∧ C j = C v) ∧ (u ≤ k ∧ C k = C u)) := by
    rcases js with a | a <;> rcases ks with b | b
    · exfalso
      apply nhj
      rwa [a.2, ← b.2]
    · exact Or.inl ⟨a,b⟩
    · exact Or.inr ⟨a,b⟩
    · exfalso
      apply nhj
      rwa [a.2, ← b.2]
  have hEnds : u ≤ t ∧ v ≤ t ∧ C u ∪ C v = C j ∪ C k := by
    rcases hsource with ⟨a,b⟩ | ⟨a,b⟩
    · exact ⟨a.1.trans jlt.le, b.1.trans klt.le, by rw [a.2,b.2]⟩
    · exact ⟨b.1.trans klt.le, a.1.trans jlt.le, by rw [a.2,b.2,Finset.union_comm]⟩
  obtain ⟨hu,hv,he⟩ := hEnds
  have hEmpty : C t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    by_cases hq' : opp q ∈ C u ∪ C v
    · have hq'' : opp q ∈ C t := by
        rw [ht]
        apply no_both_forms nhj nhk (ht ▸ hq)
        simpa only [he] using hq'
      rcases q with ⟨g,b⟩
      cases b
      · exact R.clean found.1 g hq (by simpa [opp] using hq'')
      · exact R.clean found.1 g (by simpa [opp] using hq'') hq
    · have hbad := unopposed_persists R found.1 hu hv hq hq'
      simpa [R.root] using hbad
  have ha : (C j).erase (f,false) = ∅ ∧ (C k).erase (f,true) = ∅ :=
    Finset.union_eq_empty.mp (ht.symm.trans hEmpty)
  have hj' : C j = {(f,false)} := by
    rw [← Finset.insert_erase hj, ha.1]
    rfl
  have hk' : C k = {(f,true)} := by
    rw [← Finset.insert_erase hk, ha.2]
    rfl
  refine ⟨f,?_⟩
  rcases hsource with ⟨a,b⟩ | ⟨a,b⟩
  · exact Or.inl ⟨a.2.symm.trans hj', b.2.symm.trans hk'⟩
  · exact Or.inr ⟨b.2.symm.trans hk', a.2.symm.trans hj'⟩

theorem pass_at {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i j : ℕ}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (hi : Reach P r i) (e : Edge P i j) (neU : i ≠ u) (neV : i ≠ v) :
    C j ⊆ C i := by
  rcases R.cases hi with (he | he) | ⟨p0,_⟩ | ⟨a,b,eq,hu⟩ | piv
  · exact (neU he).elim
  · exact (neV he).elim
  · simp [Edge,p0] at e
  · rw [hu]
    rcases (show j = a ∨ j = b by simpa [Edge,eq] using e) with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exact (no i hi piv).elim

theorem pure_after_sources {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i : ℕ}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (hi : Reach P r i) (hu : u ≤ i) (hv : v ≤ i) : C i = ∅ := by
  induction hi with
  | refl => exact R.root
  | @tail a b path0 e ih =>
    have ult := hu.trans_lt (R.dec e)
    have vlt := hv.trans_lt (R.dec e)
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := pass_at R no path0 e (ne_of_gt ult) (ne_of_gt vlt) hx
    rw [ih ult.le vlt.le] at h
    simp at h

theorem mark_to_reach {P : ℕ → List ℕ} {E : ℕ → ℕ → Prop} {i j : ℕ}
    (sub : ∀ {a b}, E a b → Edge P a b)
    (path : Relation.ReflTransGen E i j) : Reach P i j := by
  induction path with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (sub e)

theorem passive_cross_core {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ}
    {E : ℕ → ℕ → Prop} {r u v i : ℕ} {q : X × Bool}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (sub : ∀ {a b}, E a b → Edge P a b)
    (path : Relation.ReflTransGen E r i) (bound : u ≤ i) (hit : q ∈ C i)
    (tail : Relation.ReflTransGen E i u) :
    ∃ j, Relation.ReflTransGen E r v ∧ E v j ∧ Relation.ReflTransGen E j u ∧ q ∈ C j := by
  induction path with
  | refl => simp [R.root] at hit
  | @tail a b path0 e ih =>
    by_cases h : a = v
    · subst a
      exact ⟨b,path0,e,tail,hit⟩
    · have dec := R.dec (sub e)
      have ul := bound.trans_lt dec
      have here := pass_at R no (mark_to_reach sub path0) (sub e) (ne_of_gt ul) h hit
      exact ih ul.le here (.head e tail)

theorem passive_cross {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ}
    {E : ℕ → ℕ → Prop} {r u v : ℕ} {q : X × Bool}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (sub : ∀ {a b}, E a b → Edge P a b)
    (path : Relation.ReflTransGen E r u) (hit : q ∈ C u) :
    ∃ j, Relation.ReflTransGen E r v ∧ E v j ∧ Relation.ReflTransGen E j u ∧ q ∈ C j :=
  passive_cross_core R no sub path (Nat.le_refl _) hit .refl

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

def parity (C : LinClause V) : LinClause V := C.filter (fun q => q.1.card ≠ 1)

theorem parity_mem {C : LinClause V} {q : LinEq V} :
    q ∈ parity C ↔ q ∈ C ∧ q.1.card ≠ 1 := by
  simp [parity]

theorem filtered_res {L H R : LinClause V} {f : Finset V}
    (he : R = L.erase (f,false) ∪ H.erase (f,true)) :
    parity R = (parity L).erase (f,false) ∪ (parity H).erase (f,true) := by
  simp [parity, he, Finset.filter_erase, Finset.filter_union]

theorem filtered_axis_res {L H R : LinClause V} {f : Finset V}
    (he : R = L.erase (f,false) ∪ H.erase (f,true)) (hf : f.card = 1) :
    parity R = parity L ∪ parity H := by
  rw [filtered_res he]
  have hnL : (f,false) ∉ parity L := by simp [parity,hf]
  have hnH : (f,true) ∉ parity H := by simp [parity,hf]
  rw [Finset.erase_eq_of_notMem hnL, Finset.erase_eq_of_notMem hnH]

theorem parity_clean_of_false {C : LinClause V} {a : V → Bool}
    (ha : ¬ LinClauseSat a C) (f : Finset V) :
    (f,false) ∈ parity C → (f,true) ∉ parity C := by
  intro h0 h1
  have h0 := (parity_mem.mp h0).1
  have h1 := (parity_mem.mp h1).1
  by_cases hd : Odd (f.filter (fun x => a x = true)).card
  · exact ha ⟨_,h1, by simp [LinEqSat,hd]⟩
  · exact ha ⟨_,h0, by simp [LinEqSat,hd]⟩

def clip (P : ℕ → List ℕ) (r i : ℕ) : List ℕ :=
  if i ≤ r then P i else []

theorem edge_clip {P : ℕ → List ℕ} {r i j : ℕ} :
    Edge (clip P r) i j ↔ i ≤ r ∧ j ∈ P i := by
  by_cases hi : i ≤ r <;> simp [Edge,clip,hi]

theorem clip_desc {P : ℕ → List ℕ} {r : ℕ}
    (steps : ∀ i ≤ r, ∀ j ∈ P i, j < i)
    {i j : ℕ} (e : Edge (clip P r) i j) : j < i :=
  steps i (edge_clip.mp e).1 j (edge_clip.mp e).2

theorem clip_le {P : ℕ → List ℕ} {r i : ℕ}
    (steps : ∀ i ≤ r, ∀ j ∈ P i, j < i) (h : Reach (clip P r) r i) : i ≤ r := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (clip_desc steps e).le.trans ih

theorem mk_rules {C : ℕ → LinClause V} {P : ℕ → List ℕ} {F : Set (LinClause V)}
    {r u v : ℕ}
    (given : ∀ i ≤ r,
      (P i = [] ∧ C i ∈ F) ∨
      (∃ j < i, P i = [j] ∧ (∀ a, LinClauseSat a (C j) → LinClauseSat a (C i))) ∨
      (∃ j < i, ∃ k < i, P i = [j,k] ∧ IsLinResolvent (C j) (C k) (C i)))
    (pure : ∀ D ∈ F, ∀ q ∈ D, q.1.card = 1)
    (empty : C r = ∅) (useful : ∀ i ≤ r, ∃ a, ¬ LinClauseSat a (C i))
    (weak_cover : ∀ i, Reach (clip P r) r i → (P i).length = 1 → i = u ∨ i = v) :
    Rules (fun i => parity (C i)) (clip P r) r u v := by
  have desc : ∀ i ≤ r, ∀ j ∈ P i, j < i := by
    intro i hi j hj
    rcases given i hi with ⟨p0,_⟩ | ⟨k,lt,hp,_⟩ | ⟨k,lt,l,llt,hp,_⟩
    · simp [p0] at hj
    · have eq : j = k := by simpa [hp] using hj
      rwa [eq]
    · rcases (show j = k ∨ j = l by simpa [hp] using hj) with rfl | rfl
      · exact lt
      · exact llt
  refine ⟨clip_desc desc, by simp [parity,empty], ?_, ?_⟩
  · intro i hi f
    obtain ⟨a,ha⟩ := useful i (clip_le desc hi)
    exact parity_clean_of_false ha f
  · intro i hi
    have ir := clip_le desc hi
    have eq : clip P r i = P i := by simp [clip,ir]
    rcases given i ir with ⟨p0,hF⟩ | ⟨j,lt,hp,_⟩ | ⟨j,jlt,k,klt,hp,res⟩
    · right; left
      refine ⟨eq.trans p0, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
      intro q hq
      obtain ⟨hm,hn⟩ := parity_mem.mp hq
      exact hn (pure _ hF q hm)
    · exact Or.inl (weak_cover i hi (by simp [hp]))
    · obtain ⟨f,hL,hR,he⟩ := res
      by_cases h : f.card = 1
      · exact Or.inr (Or.inr (Or.inl ⟨j,k,eq.trans hp, filtered_axis_res he h⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨j,k,f,eq.trans hp,parity_mem.mpr ⟨hL,h⟩,parity_mem.mpr ⟨hR,h⟩,filtered_res he⟩))
end PEqualNP.Outside.L_pcx_118.ParShape
namespace PEqualNP.Outside.L_pcx_118.Orientation

open PEqualNP.ProofComplexity ParShape

variable {V : Type} [DecidableEq V]

def Wide (C : LinClause V) : Prop :=
  ¬ ∃ f : Finset V, ∀ q ∈ C, q.1.card = 1 ∨ q.1 = f

theorem not_wide_of_empty_parity {C : LinClause V} (empty : parity C = ∅) : ¬ Wide C := by
  intro h
  apply h
  refine ⟨∅, ?_⟩
  intro q hq
  left
  by_contra hn
  have h := parity_mem.mpr ⟨hq,hn⟩
  rw [empty] at h
  simp at h

theorem not_wide_of_singleton_parity {C : LinClause V} {f : Finset V} {b : Bool}
    (single : parity C = {(f,b)}) : ¬ Wide C := by
  intro h
  apply h
  refine ⟨f, ?_⟩
  intro q hq
  by_cases hn : q.1.card = 1
  · exact Or.inl hn
  · have h := parity_mem.mpr ⟨hq,hn⟩
    rw [single] at h
    exact Or.inr (congrArg Prod.fst (Finset.mem_singleton.mp h))

def ParityRules {V : Type} [DecidableEq V] (C : ℕ → LinClause V) (P : ℕ → List ℕ)
    (r u v : ℕ) : Prop := Rules (fun i => parity (C i)) P r u v

theorem wide_forbids_pivot {C : ℕ → LinClause V} {P : ℕ → List ℕ}
    {r u v i : ℕ} (R : ParityRules C P r u v)
    (location : i = u ∨ i = v) (wide : Wide (C i)) :
    ∀ j, Reach P r j → ¬ Pivot (fun k => parity (C k)) P j := by
  intro j hr hp
  obtain ⟨f, hh⟩ := single_form_sources R ⟨j,hr,hp⟩
  rcases location with rfl | rfl <;> rcases hh with ⟨a,b⟩ | ⟨a,b⟩
  · exact not_wide_of_singleton_parity a wide
  · exact not_wide_of_singleton_parity a wide
  · exact not_wide_of_singleton_parity b wide
  · exact not_wide_of_singleton_parity b wide

theorem wide_source_is_older {C : ℕ → LinClause V} {P : ℕ → List ℕ}
    {r u v i : ℕ} (R : ParityRules C P r u v) (order : u ≤ v)
    (seen : Reach P r i) (location : i = u ∨ i = v) (wide : Wide (C i)) : i = u := by
  rcases location with h | e
  · exact h
  · subst i
    have np := wide_forbids_pivot R (Or.inr rfl) wide
    exact (not_wide_of_empty_parity (pure_after_sources R np seen order (Nat.le_refl _)) wide).elim

theorem path_false {C : ℕ → LinClause V} {E : ℕ → ℕ → Prop} {a : V → Bool}
    {r i : ℕ} (rootFalse : ¬ LinClauseSat a (C r))
    (edgeFalse : ∀ {j k}, E j k → ¬ LinClauseSat a (C k))
    (path : Relation.ReflTransGen E r i) : ¬ LinClauseSat a (C i) := by
  cases path with
  | refl => exact rootFalse
  | tail _ e => exact edgeFalse e

theorem recover_large_weak {C : ℕ → LinClause V} {P : ℕ → List ℕ} {E : ℕ → ℕ → Prop}
    {r u v j : ℕ} (R : ParityRules C P r u v) (order : u ≤ v)
    (wide : Wide (C u))
    (old_weak : ∀ a : V → Bool, LinClauseSat a (C j) → LinClauseSat a (C u))
    (new_weak : ∀ k, Edge P v k → ∀ a : V → Bool, LinClauseSat a (C k) → LinClauseSat a (C v))
    (sub : ∀ {i k}, E i k → Edge P i k) {a : V → Bool}
    (rootFalse : ¬ LinClauseSat a (C r))
    (edgeFalse : ∀ {i k}, E i k → ¬ LinClauseSat a (C k))
    (walk : Relation.ReflTransGen E r u)
    {x : V} (hneg : neg x ∈ C j) (hgone : neg x ∉ C u) :
    Relation.ReflTransGen E r v ∧ Relation.ReflTransGen E v u ∧ neg x ∈ C v := by
  have fu := path_false rootFalse edgeFalse walk
  have tj : ¬ LinClauseSat a (C j) := fun h => fu (old_weak a h)
  have hx : a x = true := by
    cases h : a x
    · exact False.elim (tj ⟨_,hneg,(axis_sat _ _ _).2 h⟩)
    · rfl
  obtain ⟨q,hq,hn,qx⟩ := weak_lost_axis_supported old_weak fu hneg hgone
  have no := wide_forbids_pivot R (Or.inl rfl) wide
  obtain ⟨k,pathv,ek,suf,hsrc⟩ := passive_cross R no sub walk (parity_mem.mpr ⟨hq,hn⟩)
  have pure : ∀ p ∈ C v, p.1.card = 1 := by
    intro p hp
    have h := pure_after_sources R no (mark_to_reach sub pathv) order (Nat.le_refl _)
    by_contra hn'
    have e := parity_mem.mpr ⟨hp,hn'⟩
    rw [h] at e
    simp at e
  exact ⟨pathv, .head ek suf, weak_pure_recovers_axis pure (new_weak k (sub ek))
    (path_false rootFalse edgeFalse pathv) (parity_mem.mp hsrc).1 qx hx⟩

end PEqualNP.Outside.L_pcx_118.Orientation
namespace PEqualNP.Outside.L_pcx_118.Orientation

theorem two_cover_sources {S T : Finset ℕ} {root : ℕ}
    (rootLive : root ∈ T) (inLive : S ⊆ T) (small : S.card ≤ 2) :
    ∃ u v, u ∈ T ∧ v ∈ T ∧ u ≤ v ∧ (S.Nonempty → u ∈ S ∧ v ∈ S) ∧ ∀ i ∈ S, i = u ∨ i = v := by
  by_cases h0 : S = ∅
  · exact ⟨root, root, rootLive, rootLive, Nat.le_refl _, by simp [h0], by simp [h0]⟩
  by_cases h1 : S.card = 1
  · obtain ⟨u,rfl⟩ := Finset.card_eq_one.mp h1
    have live : u ∈ T := inLive (by simp)
    exact ⟨u,u,live,live,Nat.le_refl _,by simp,by simp⟩
  have htwo : 1 < S.card := by
    have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
    omega
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp htwo
  have both : ({a,b} : Finset ℕ) ⊆ S := by
    intro x hx
    rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
    · exact ha
    · exact hb
  have equal : ({a,b} : Finset ℕ) = S :=
    Finset.eq_of_subset_of_card_le both (by simpa [ne] using small)
  rcases le_total a b with ord | ord
  · refine ⟨a,b,inLive ha,inLive hb,ord,(fun _ => ⟨ha,hb⟩),?_⟩
    intro x hx
    simpa [← equal] using hx
  · refine ⟨b,a,inLive hb,inLive ha,ord,(fun _ => ⟨hb,ha⟩),?_⟩
    intro x hx
    have e : x = a ∨ x = b := by simpa [← equal] using hx
    exact e.symm

end PEqualNP.Outside.L_pcx_118.Orientation
namespace PEqualNP.Outside.L_pcx_118.Charge

open PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.Outside.L_pcx_118.Graph PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_118.Orientation (neg loss_resolvent collision_heads_card)

variable {V : Type} [DecidableEq V]
variable {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r : Nat}

def NegOnly (D : LinClause V) : Prop := ∀ q ∈ D, q.2 = false

def FirstUse (i j : Nat) : Prop :=
  Edge P i j ∧ P j = [] ∧ NegOnly (C j)

theorem unique_firstUse {i j k : Nat} (rule : Rule F C P i)
    (h : FirstUse (P := P) (C := C) i j) (g : FirstUse (P := P) (C := C) i k) : j = k := by
  rcases h with ⟨hj, _, hn⟩
  rcases g with ⟨hk, _, gn⟩
  rcases rule with ⟨p0, _⟩ | ⟨l, _, pl, _⟩ | ⟨l, _, m, _, pm, f, _, mf, _⟩
  · simp [Edge, p0] at hj
  · simp only [Edge, pl, List.mem_singleton] at hj hk
    exact hj.trans hk.symm
  · simp only [Edge, pm, List.mem_cons, List.not_mem_nil, or_false] at hj hk
    rcases hj with rfl | rfl
    · rcases hk with rfl | rfl
      · rfl
      · have no := gn (f, true) mf
        contradiction
    · have no := hn (f, true) mf
      contradiction

def Loss (i j : Nat) (v : V) : Prop :=
  Edge P i j ∧ P j ≠ [] ∧ neg v ∉ C i ∧ neg v ∈ C j

theorem loss_rule {i j : Nat} {v : V} (rule : Rule F C P i)
    (h : Loss (P := P) (C := C) i j v) :
    (P i = [j] ∧ ∀ a, LinClauseSat a (C j) → LinClauseSat a (C i)) ∨
    (∃ k, P i = [j, k] ∧ (({v}, true) : LinEq V) ∈ C k ∧
      C i = (C j).erase (neg v) ∪ (C k).erase ({v}, true)) := by
  obtain ⟨he, _, hi, hj⟩ := h
  rcases rule with ⟨p0, _⟩ | ⟨l, _, pl, hw⟩ | ⟨l, _, k, _, pr, f, _, hfk, rr⟩
  · simp [Edge, p0] at he
  · have eq : j = l := by simpa [Edge, pl] using he
    subst l
    exact Or.inl ⟨pl, hw⟩
  · have mem : neg v ∈ C l ∨ neg v ∈ C k := by
      simp only [Edge, pr, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> tauto
    obtain ⟨_, nk, mv⟩ := loss_resolvent rr hi mem
    have eq : j = l := by
      simp only [Edge, pr, List.mem_cons, List.not_mem_nil, or_false] at he
      exact he.resolve_right (fun e => nk (e ▸ hj))
    subst l
    subst f
    exact Or.inr ⟨k, pr, hfk, rr⟩

theorem loss_not_firstUse {i j k : Nat} {v : V} (rule : Rule F C P i)
    (h : Loss (P := P) (C := C) i j v) :
    ¬ FirstUse (P := P) (C := C) i k := by
  rintro ⟨ek, k0, kn⟩
  have j0 := h.2.1
  rcases loss_rule rule h with ⟨pl, _⟩ | ⟨m, pl, hm, _⟩
  · have eq : k = j := by simpa [Edge, pl] using ek
    exact j0 (eq ▸ k0)
  · simp only [Edge, pl, List.mem_cons, List.not_mem_nil, or_false] at ek
    rcases ek with rfl | rfl
    · exact j0 k0
    · have no := kn _ hm
      contradiction

theorem binary_loss_unique {i j k : Nat} {v w : V} (rule : Rule F C P i)
    (two : (P i).length = 2) (h : Loss (P := P) (C := C) i j v)
    (g : Loss (P := P) (C := C) i k w) : v = w := by
  rcases loss_rule rule h with ⟨e, _⟩ | ⟨a, e, _, rv⟩
  · simp [e] at two
  rcases loss_rule rule g with ⟨f, _⟩ | ⟨b, f, _, _⟩
  · simp [f] at two
  have same : j = k := (List.cons.inj (e.symm.trans f)).1
  subst k
  have has := g.2.2.2
  by_contra ne
  apply g.2.2.1
  rw [rv]
  refine Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, has⟩)
  intro he
  apply ne
  simpa [neg] using (congrArg Prod.fst he).symm

theorem first_loss {E : Nat → Nat → Prop} {i j : Nat} {v : V}
    (w : Walk E i j) (h0 : neg v ∉ C i) (h1 : neg v ∈ C j) :
    ∃ p q, Walk (fun u v' => E u v' ∧ neg v ∉ C v') i p ∧
       E p q ∧ Walk E q j ∧ neg v ∉ C p ∧ neg v ∈ C q := by
  induction w using Relation.ReflTransGen.head_induction_on with
  | refl => exact (h0 h1).elim
  | @head i x e w ih =>
    by_cases hx : neg v ∈ C x
    · exact ⟨i, x, .refl, e, w, h0, hx⟩
    · obtain ⟨p, q, pr, ep, suf, np, yq⟩ := ih hx
      exact ⟨p, q, .head ⟨e, hx⟩ pr, ep, suf, np, yq⟩

abbrev Grid := Fin 4 × Fin 3
abbrev Collision := {t : Fin 4 × Fin 4 × Fin 3 // t.1 < t.2.1}

def first (k : Collision) : Grid := (k.val.1, k.val.2.2)
def second (k : Collision) : Grid := (k.val.2.1, k.val.2.2)
def collision (k : Collision) : LinClause Grid := {neg (first k), neg (second k)}

theorem nCollision : Fintype.card Collision = 18 := by decide +kernel

theorem collision_injective : Function.Injective collision := by decide +kernel

theorem collision_negative (k : Collision) : NegOnly (collision k) := by
  intro a ha
  simp only [collision, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> rfl

theorem heads_large (endpoint : Collision → Grid)
    (each : ∀ k, endpoint k = first k ∨ endpoint k = second k) :
    9 ≤ (Finset.univ.image endpoint).card := by
  apply collision_heads_card
  intro i j h ne
  rcases lt_or_gt_of_ne ne with ij | ji
  · let k : Collision := ⟨(i,j,h), ij⟩
    have hm : endpoint k ∈ (Finset.univ.image endpoint : Finset Grid) := Finset.mem_image.2 ⟨_, by simp, rfl⟩
    rcases each k with eq | eq
    · simpa [k, eq, first] using Or.inl (b := (j,h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm
    · simpa [k, eq, second] using Or.inr (a := (i,h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm
  · let k : Collision := ⟨(j,i,h), ji⟩
    have hm : endpoint k ∈ (Finset.univ.image endpoint : Finset Grid) := Finset.mem_image.2 ⟨_, by simp, rfl⟩
    rcases each k with eq | eq
    · simpa [k, eq, first] using Or.inr (a := (i,h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm
    · simpa [k, eq, second] using Or.inl (b := (j,h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm

theorem collision_charges {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (axes : 22 ≤ (WithArity P r 0).card)
    (good : Nat → Nat → Grid → Prop)
    (is_loss : ∀ i j v, good i j v → Loss (C := C) (P := P) i j v)
    (one_loss : ∀ i j k v w, i ∈ Live P r → good i j v → good i k w → v = w)
    (witnesses : ∀ k : Collision, ∃ i j, i ∈ Live P r ∧ Edge P i j ∧ P j = [] ∧ C j = collision k ∧
        ∃ v l t, (v = first k ∨ v = second k) ∧ l ∈ Live P r ∧ good l t v) :
    49 ≤ (Live P r).card := by
  classical
  choose i j hi eij j0 cj kk using witnesses
  choose endpoint loss target endp loss_live loss_good using kk
  have firstuse (k : Collision) : FirstUse (C := C) (P := P) (i k) (j k) :=
    ⟨eij k, j0 k, cj k ▸ collision_negative k⟩
  have rule_live : ∀ u ∈ Live P r, Rule F C P u := by
    intro u hu
    exact rules _ (walk_le (bounded_edge rules) ((live_iff rules).1 hu))
  have ii : Function.Injective i := by
    intro k l eq
    have same := unique_firstUse (rule_live (i k) (hi k)) (firstuse k) (eq ▸ firstuse l)
    have e := (cj k).symm.trans ((congrArg C same).trans (cj l))
    exact collision_injective e
  let I := Finset.univ.image i
  have ic : I.card = 18 := by simp [I, Finset.card_image_of_injective _ ii, nCollision]
  let S := Finset.univ.image endpoint
  have sc : 9 ≤ S.card := heads_large endpoint endp
  have all : ∀ v ∈ S, ∃ l t, l ∈ Live P r ∧ good l t v := by
    intro v hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨loss k, target k, loss_live k, loss_good k⟩
  choose ll tt hl ht using all
  let L := S.attach.image (fun v => ll v.val v.property)
  have lc : L.card = S.card := by
    rw [Finset.card_image_of_injective, Finset.card_attach]
    intro a b ee
    apply Subtype.ext
    change ll a.val a.property = ll b.val b.property at ee
    have hb := ht b.val b.property
    rw [← ee] at hb
    exact one_loss _ _ _ _ _ (hl a.val a.property) (ht a.val a.property) hb
  let A := WithArity P r 0
  have Asub : A ⊆ Live P r := Finset.filter_subset _ _
  have Isub : I ⊆ Live P r := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hu
    exact hi k
  have Lsub : L ⊆ Live P r := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hu
    exact hl v.val v.property
  have AI : Disjoint A I := by
    apply Finset.disjoint_left.2
    intro u au iu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 iu
    have p0 := (Finset.mem_filter.1 au).2
    simp at p0
    have ee := eij k
    simp [Edge, p0] at ee
  have AL : Disjoint A L := by
    apply Finset.disjoint_left.2
    intro u au lu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 lu
    have p0 := (Finset.mem_filter.1 au).2
    simp at p0
    have ee := (is_loss _ _ _ (ht v.val v.property)).1
    simp [Edge, p0] at ee
  have IL : Disjoint I L := by
    apply Finset.disjoint_left.2
    intro u iu lu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 lu
    obtain ⟨k, _, e⟩ := Finset.mem_image.1 iu
    exact loss_not_firstUse (rule_live _ (hl v.val v.property))
      (is_loss _ _ _ (ht v.val v.property)) (e ▸ firstuse k)
  have hist : A ∪ I ∪ L ⊆ Live P r :=
    Finset.union_subset (Finset.union_subset Asub Isub) Lsub
  have bound := Finset.card_le_card hist
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨AL, IL⟩),
    Finset.card_union_of_disjoint AI, ic, lc] at bound
  change 22 ≤ A.card at axes
  omega

open PEqualNP.Outside.L_pcx_118.Orientation (weak_lost_neg_injective)

def SmallForms (D : LinClause V) : Prop :=
  ∃ q : Finset V, ∀ e ∈ D, e.1.card = 1 ∨ e.1 = q

def GoodLoss (i j : Nat) (v : V) : Prop :=
  Loss (C := C) (P := P) i j v ∧ (∃ a, FalseAt C a i) ∧
    ((P i).length = 2 ∨ SmallForms (C i))

theorem good_unique {i j k : Nat} {v w : V} (rule : Rule F C P i)
    (h : GoodLoss (C := C) (P := P) i j v)
    (g : GoodLoss (C := C) (P := P) i k w) : v = w := by
  obtain ⟨hl, ⟨a, ff⟩, two | ⟨q, shape⟩⟩ := h
  · exact binary_loss_unique rule two hl g.1
  · rcases loss_rule rule hl with ⟨vj, weak⟩ | ⟨l, vv, _, _⟩
    · have eq : k = j := by simpa [Edge, vj] using g.1.1
      subst k
      exact weak_lost_neg_injective shape weak ff hl.2.2.2 g.1.2.2.2 hl.2.2.1 g.1.2.2.1
    · exact binary_loss_unique rule (by simp [vv]) hl g.1

theorem collision_residue {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {i j : Nat} {k : Collision} (rule : Rule F C P i)
    (he : Edge P i j) (cj : C j = collision k) (two : (P i).length = 2) :
    neg (first k) ∈ C i ∨ neg (second k) ∈ C i := by
  rcases rule with ⟨p0, _⟩ | ⟨l, _, p1, _⟩ | ⟨l, _, m, _, pm, f, fl, fm, rr⟩
  · simp [p0] at two
  · simp [p1] at two
  · simp only [Edge, pm, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have first_ne_second : first k ≠ second k := fun eq => (ne_of_lt k.property) (congrArg Prod.fst eq)
      rw [cj] at fl rr
      have opts : (f, false) = neg (first k) ∨ (f, false) = neg (second k) := by
        simpa only [collision, Finset.mem_insert, Finset.mem_singleton] using fl
      rcases opts with ho | ho
      · right
        rw [rr]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun eq => first_ne_second
          ((Finset.singleton_inj.1 (congrArg Prod.fst (eq.trans ho))).symm), by simp [collision]⟩)
      · left
        rw [rr]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun eq => first_ne_second
          (Finset.singleton_inj.1 (congrArg Prod.fst (eq.trans ho))), by simp [collision]⟩)
    · have zz := collision_negative k (f, true) (cj ▸ fm)
      contradiction

def Mark (C : ClauseMap V) (P : Parents) (r : Nat) (a : V → Bool) (i j : Nat) : Prop :=
  LocalEdge P r i j ∧ FalseAt C a j

theorem rootRawAbsent {v : V} (h : ∀ a, FalseAt C a r) : neg v ∉ C r := by
  intro hm
  apply h (fun _ => false)
  exact ⟨_, hm, by simp [neg, LinEqSat]⟩

theorem false_on_mark {a : V → Bool} {i j : Nat}
    (w : Walk (Mark C P r a) i j) (h : FalseAt C a i) : FalseAt C a j := by
  rcases w.cases_tail with rfl | ⟨k, _, hk⟩
  · exact h
  · exact hk.2

theorem has_child_from_path {a : V → Bool} {i j k : Nat}
    (w : Walk (Mark C P r a) i j) (out : Edge P j k) : P i ≠ [] := by
  rcases w.cases_head with rfl | ⟨l, hl, _⟩
  · intro he
    simpa [Edge, he] using out
  · intro he
    have ho := hl.1.2
    simpa [Edge, he] using ho

def Recover (C : ClauseMap V) (P : Parents) (r : Nat) : Prop :=
  ∀ (a : V → Bool) i j v, P i = [j] → ¬ SmallForms (C i) →
    neg v ∈ C j → neg v ∉ C i →
    ∀ Q : Nat → Nat → Prop, (∀ {u z}, Q u z → Mark C P r a u z) →
      Walk Q r i → ∃ t, Walk Q r t ∧ Walk Q t i ∧ neg v ∈ C t

theorem charge_path {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (fr : ∀ a, FalseAt C a r) (rootInternal : P r ≠ []) (recover : Recover C P r)
    (k : Collision) (crit : ∃ a, ∀ D ∈ F, ¬ LinClauseSat a D → D = collision k) :
    ∃ i j, i ∈ Live P r ∧ Edge P i j ∧ P j = [] ∧ C j = collision k ∧
      ∃ v l t, (v = first k ∨ v = second k) ∧ l ∈ Live P r ∧
        GoodLoss (C := C) (P := P) l t v := by
  classical
  obtain ⟨a, ua⟩ := crit
  obtain ⟨j, j0, jf, af, wj⟩ := localized_route rules a le_rfl (fr a)
  have cj : C j = collision k := ua _ jf af
  obtain ⟨i, wi0, ei0⟩ := wj.cases_tail.resolve_left (fun e => rootInternal (e ▸ j0))
  have wi : Walk (Mark C P r a) r i :=
    walk_sub (fun e => ⟨e.1, e.2.2⟩) wi0
  have ir : i ≤ r := ei0.1.1
  have eij : Edge P i j := ei0.1.2
  have fi := false_on_mark wi (fr a)
  have il := (live_iff rules).2 (walk_sub (fun e => e.1) wi)
  refine ⟨i, j, il, eij, j0, cj, ?_⟩
  have pay : ∃ v t, (v = first k ∨ v = second k) ∧ neg v ∈ C t ∧
      Walk (Mark C P r a) r t ∧ Walk (Mark C P r a) t i := by
    by_cases has : neg (first k) ∈ C i ∨ neg (second k) ∈ C i
    · rcases has with h | h
      · exact ⟨first k, i, Or.inl rfl, h, wi, .refl⟩
      · exact ⟨second k, i, Or.inr rfl, h, wi, .refl⟩
    push Not at has
    have possible : ∀ u, P i = [u] → u = j := by
      intro u pu
      exact (by simpa [Edge, pu] using eij : j = u).symm
    have ic := rules i ir
    rcases ic with ⟨p0, _⟩ | ⟨u, _, pu, wu⟩ | ⟨u, _, z, _, e, _⟩
    · simp [Edge, p0] at eij
    · have ji := possible u pu
      subst u
      have fv : neg (first k) ∈ C j := by simp [cj, collision]
      have sv : neg (second k) ∈ C j := by simp [cj, collision]
      have nonsmall : ¬ SmallForms (C i) := by
        rintro ⟨q, sq⟩
        have hh := weak_lost_neg_injective sq wu fi fv sv has.1 has.2
        exact (ne_of_lt k.property) (congrArg Prod.fst hh)
      obtain ⟨t, wt, ws, ht⟩ := recover a i j (first k) pu nonsmall fv has.1 _ (fun e => e) wi
      exact ⟨first k, t, Or.inl rfl, ht, wt, ws⟩
    · exact False.elim ((collision_residue (rules i ir) eij cj (by simp [e])).elim has.1 has.2)
  obtain ⟨v, t, hv, tv, wt, ti⟩ := pay
  have nr := rootRawAbsent (v := v) fr
  obtain ⟨l, u, pre, edge, suffix, nv, pv⟩ := first_loss (C := C) wt nr tv
  have marked : Walk (Mark C P r a) r l := walk_sub (fun e => e.1) pre
  have fl := false_on_mark marked (fr a)
  have ll := (live_iff rules).2 (walk_sub (fun e => e.1) marked)
  have hinternal := has_child_from_path (suffix.trans ti) eij
  have loss : Loss (C := C) (P := P) l u v := ⟨edge.1.2, hinternal, nv, pv⟩
  have shape : (P l).length = 2 ∨ SmallForms (C l) := by
    rcases loss_rule (rules l edge.1.1) loss with ⟨pu, _⟩ | ⟨x, pe, _, _⟩
    · right
      by_contra h
      obtain ⟨z, wz, _, nz⟩ := recover a l u v pu h pv nv _ (fun e => e.1) pre
      rcases wz.cases_tail with e | ⟨z0, _, e⟩
      · exact nr (e ▸ nz)
      · exact e.2 nz
    · left
      simp [pe]
  exact ⟨v, l, u, hv, ll, loss, ⟨a, fl⟩, shape⟩

theorem low_bound_of_recover {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (fr : ∀ a, FalseAt C a r) (rootInternal : P r ≠ [])
    (axes : 22 ≤ (WithArity P r 0).card) (recover : Recover C P r)
    (crits : ∀ k : Collision, ∃ a, ∀ D ∈ F, ¬ LinClauseSat a D → D = collision k) :
    49 ≤ (Live P r).card := by
  apply collision_charges rules axes (GoodLoss (C := C) (P := P)) (fun _ _ _ h => h.1)
  · intro i j k v w il h g
    have ir := walk_le (bounded_edge rules) ((live_iff rules).1 il)
    exact good_unique (rules i ir) h g
  · exact fun k => charge_path rules fr rootInternal recover k (crits k)

end PEqualNP.Outside.L_pcx_118.Charge
namespace PEqualNP.Outside.L_pcx_118.Low

open PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Charge PEqualNP.ProofComplexity

theorem collisions_indexed : ∀ k : Collision,
    PEqualNP.Outside.L_pcx_118.Linear.axioms.any
      (fun row => PEqualNP.Outside.L_pcx_118.Linear.linearOf row == collision k) = true := by
  decide +kernel

theorem collision_crit (k : Collision) :
    ∃ a, ∀ D ∈ (linOfClause '' PHP 4 3), ¬ LinClauseSat a D → D = collision k := by
  obtain ⟨row, rm, eq⟩ := List.any_eq_true.mp (collisions_indexed k)
  obtain ⟨label, hl⟩ := PEqualNP.Outside.L_pcx_118.High.row_exists row rm
  have same : PEqualNP.Outside.L_pcx_118.High.ax label = collision k := by
    simpa only [PEqualNP.Outside.L_pcx_118.High.ax, hl] using beq_iff_eq.mp eq
  obtain ⟨a, ha⟩ := PEqualNP.Outside.L_pcx_118.High.point_exists label
  refine ⟨a, ?_⟩
  intro D hd nh
  rw [PEqualNP.Outside.L_pcx_118.High.formula_range] at hd
  obtain ⟨j, rfl⟩ := hd
  have e := (PEqualNP.Outside.L_pcx_118.High.point_only ha j).1 nh
  exact e ▸ same

theorem low_impossible {C : ClauseMap Grid} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule (linOfClause '' PHP 4 3) C P i)
    (fr : ∀ a, FalseAt C a r) (rootInternal : P r ≠ [])
    (size : (Live P r).card ≤ 47) (recover : Recover C P r) : False := by
  letI : Fintype PEqualNP.Outside.L_pcx_118.High.K := Fintype.ofFinset
    (p := {x | x ∈ PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical})
    ((PEqualNP.Outside.L_pcx_118.Finite.axioms.zip PEqualNP.Outside.L_pcx_118.Finite.critical).toFinset) (by intro x; simp)
  have crit : ∀ k : PEqualNP.Outside.L_pcx_118.High.K, ∃ a : Grid → Bool, ∀ j,
      (¬ LinClauseSat a (PEqualNP.Outside.L_pcx_118.High.ax j)) ↔ j = k := by
    intro k
    obtain ⟨a, ha⟩ := PEqualNP.Outside.L_pcx_118.High.point_exists k
    exact ⟨a, PEqualNP.Outside.L_pcx_118.High.point_only ha⟩
  obtain ⟨_, _, _, lower, _⟩ := unique_leaves rules fr PEqualNP.Outside.L_pcx_118.High.ax
    PEqualNP.Outside.L_pcx_118.High.formula_range crit
  rw [PEqualNP.Outside.L_pcx_118.High.label_card] at lower
  have lb := low_bound_of_recover rules fr rootInternal lower recover collision_crit
  omega

end PEqualNP.Outside.L_pcx_118.Low
namespace PEqualNP.Outside.L_pcx_118.Strip

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph

variable {V : Type} [DecidableEq V]

def strip (D : LinClause V) : LinClause V := D.filter (fun q => q.1 ≠ ∅)

theorem no_false_empty {D : LinClause V} (live : ∃ a, ¬ LinClauseSat a D) :
    (∅, false) ∉ D := by
  intro hm
  obtain ⟨a,ha⟩ := live
  exact ha ⟨_,hm,by simp [LinEqSat]⟩

theorem strip_sat {D : LinClause V} (live : ∃ a, ¬ LinClauseSat a D) (a : V → Bool) :
    LinClauseSat a (strip D) ↔ LinClauseSat a D := by
  constructor
  · rintro ⟨q, hq, hs⟩
    exact ⟨q, (Finset.mem_filter.1 hq).1, hs⟩
  · rintro ⟨⟨f,b⟩, hq, hs⟩
    have hn : f ≠ ∅ := by
      rintro rfl
      cases b
      · exact no_false_empty live hq
      · simp [LinEqSat] at hs
    exact ⟨_, Finset.mem_filter.2 ⟨hq,hn⟩,hs⟩

theorem nonempty_equation_sat (q : LinEq V) (hn : q.1 ≠ ∅) :
    ∃ a : V → Bool, LinEqSat a q := by
  rcases q with ⟨f,b⟩
  cases b
  · exact ⟨fun _ => false, by simp [LinEqSat]⟩
  · obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.2 hn
    let a := fun j : V => decide (j = v)
    have fe : f.filter (fun j => a j = true) = {v} := by
      ext j
      simp only [a, Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hv, h⟩⟩
    exact ⟨a, by simp [LinEqSat, fe]⟩

theorem strip_false {D : LinClause V} (h : ∀ a, ¬ LinClauseSat a D) : strip D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro q hq
  obtain ⟨hm,hn⟩ := Finset.mem_filter.1 hq
  obtain ⟨a,ha⟩ := nonempty_equation_sat q hn
  exact h a ⟨q,hm,ha⟩

theorem strip_ax {D : LinClause V} (axes : ∀ q ∈ D, q.1.card = 1) : strip D = D := by
  refine Finset.filter_true_of_mem ?_
  intro q hq he
  have eq := axes q hq
  simp [he] at eq

theorem strip_rules {F : Set (LinClause V)} {C : ClauseMap V}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (useful : ∀ i ≤ r, ∃ a, FalseAt C a i)
    (pure : ∀ D ∈ F, ∀ q ∈ D, q.1.card = 1) :
    ∀ i ≤ r, Rule F (fun i => strip (C i)) P i := by
  intro i hi
  rcases rules i hi with ⟨p0, f⟩ | ⟨j,ji,p1,hw⟩ | ⟨j,ji,k,ki,p2,g,hj,hk,hr⟩
  · exact Or.inl ⟨p0, by simpa only [strip_ax (pure _ f)] using f⟩
  · refine Or.inr (Or.inl ⟨j,ji,p1,fun a ha => ?_⟩)
    have hs := strip_sat (useful j (ji.le.trans hi)) a
    exact (strip_sat (useful i hi) a).2 (hw a (hs.1 ha))
  · have nz : g ≠ ∅ := by
      rintro rfl
      exact no_false_empty (useful j (ji.le.trans hi)) hj
    refine Or.inr (Or.inr ⟨j,ji,k,ki,p2,g,Finset.mem_filter.2 ⟨hj,nz⟩,
      Finset.mem_filter.2 ⟨hk,nz⟩,?_⟩)
    simp [strip, hr, Finset.filter_erase, Finset.filter_union]

theorem php_pure {D : LinClause (Fin 4 × Fin 3)}
    (h : D ∈ (linOfClause '' PHP 4 3)) : ∀ q ∈ D, q.1.card = 1 := by
  obtain ⟨C, _, rfl⟩ := h
  intro q hq
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.1 hq
  simp

end PEqualNP.Outside.L_pcx_118.Strip
namespace PEqualNP.Outside.L_pcx_118.Recovery

open PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.Outside.L_pcx_118.Charge PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_118.Orientation

variable {V : Type} [DecidableEq V]

theorem weaken_edge {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents}
    {i j : Nat} (rule : Rule F C P i)
    (hw : (P i).length = 1) (he : Edge P i j) :
    ∀ a, LinClauseSat a (C j) → LinClauseSat a (C i) := by
  rcases rule with ⟨p0, _⟩ | ⟨k, _, p1, wk⟩ | ⟨k, _, l, _, p2, _⟩
  · simp [p0] at hw
  · have eq : j = k := by simpa [Edge, p1] using he
    exact eq.symm ▸ wk
  · simp [p2] at hw

theorem recover_of_few {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents}
    {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (pure : ∀ D ∈ F, ∀ q ∈ D, q.1.card = 1)
    (root : C r = ∅) (live : ∀ i ≤ r, ∃ a, FalseAt C a i)
    (few : (WithArity P r 1).card ≤ 2) : Recover C P r := by
  have rt : r ∈ Live P r := (live_iff rules).2 .refl
  obtain ⟨u,v,_,hv,order,real,cover⟩ :=
    two_cover_sources rt (Finset.filter_subset _ _) few
  have weak_cover : ∀ i, PEqualNP.Outside.L_pcx_118.ParShape.Reach (PEqualNP.Outside.L_pcx_118.ParShape.clip P r) r i →
      (P i).length = 1 → i = u ∨ i = v := by
    intro i w h
    have wr := walk_sub (fun e => PEqualNP.Outside.L_pcx_118.ParShape.edge_clip.mp e) w
    exact cover i (Finset.mem_filter.2 ⟨(live_iff rules).2 wr,h⟩)
  have R : ParityRules C (PEqualNP.Outside.L_pcx_118.ParShape.clip P r) r u v :=
    PEqualNP.Outside.L_pcx_118.ParShape.mk_rules rules pure root live weak_cover
  intro a i j x pj wide hn hg Q sub path
  have sub_clip : ∀ {h k}, Q h k → PEqualNP.Outside.L_pcx_118.ParShape.Edge (PEqualNP.Outside.L_pcx_118.ParShape.clip P r) h k :=
    fun e => PEqualNP.Outside.L_pcx_118.ParShape.edge_clip.mpr (sub e).1
  have rpath : PEqualNP.Outside.L_pcx_118.ParShape.Reach (PEqualNP.Outside.L_pcx_118.ParShape.clip P r) r i := walk_sub sub_clip path
  have lm : i ∈ Live P r := (live_iff rules).2 (walk_sub (fun h => (sub h).1) path)
  have one : (P i).length = 1 := by simp [pj]
  have im : i ∈ WithArity P r 1 := Finset.mem_filter.2 ⟨lm,one⟩
  have loc := cover i im
  have iu := wide_source_is_older R order rpath loc wide
  have vweak := (Finset.mem_filter.1 (real ⟨i,im⟩).2).2
  have wi : i ≤ r := walk_le (bounded_edge rules) ((live_iff rules).1 lm)
  have wv : v ≤ r := walk_le (bounded_edge rules) ((live_iff rules).1 hv)
  have old := weaken_edge (rules i wi) one (j := j) (by simp [Edge,pj])
  have newer : ∀ k, PEqualNP.Outside.L_pcx_118.ParShape.Edge (PEqualNP.Outside.L_pcx_118.ParShape.clip P r) v k →
      ∀ a, LinClauseSat a (C k) → LinClauseSat a (C v) := by
    intro k ek
    exact weaken_edge (rules v wv) vweak (PEqualNP.Outside.L_pcx_118.ParShape.edge_clip.mp ek).2
  subst i
  have rf : FalseAt C a r := by simp [FalseAt,root,LinClauseSat]
  obtain ⟨pr,post,ax⟩ := recover_large_weak R order wide old newer sub_clip
    rf (fun e => (sub e).2) path hn hg
  exact ⟨v,pr,post,ax⟩

end PEqualNP.Outside.L_pcx_118.Recovery
namespace PEqualNP.Outside.L_pcx_118.Main

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Strip PEqualNP.Outside.L_pcx_118.Charge
open PEqualNP.Outside.L_pcx_118.Finite (Row packedCert)
open PEqualNP.Outside.L_pcx_118.Orientation (axis_sat)

theorem php_ax_sat (D : LinClause Grid) (h : D ∈ (linOfClause '' PHP 4 3)) :
    ∃ a : Grid → Bool, LinClauseSat a D := by
  obtain ⟨C, hC, rfl⟩ := h
  rcases hC with ⟨i, rfl⟩ | ⟨i,j,h,hne,rfl⟩
  · refine ⟨fun _ => true, ({(i, (0 : Fin 3))}, true), ?_, (axis_sat _ _ _).2 rfl⟩
    exact Finset.mem_image.2 ⟨((i,(0 : Fin 3)),true), by simp, rfl⟩
  · refine ⟨fun _ => false, ({(i, h)}, false), ?_, (axis_sat _ _ _).2 rfl⟩
    exact Finset.mem_image.2 ⟨((i,h),false), by simp, rfl⟩

theorem verify (rows : List Row)
    (valid : rows.all packedCert = true)
    (ids : rows.map Prod.fst = (List.range 4095).map (1 + ·))
    (π : List (LinClause Grid)) (refute : IsLinRefutation (PHP 4 3) π)
    (small : π.length ≤ 47) : False := by
  classical
  let π' := π.filter useful
  have hempty : ∅ ∈ π' := List.mem_filter.2
    ⟨refute.2, (useful_spec _).2 ⟨fun _ => false, by simp [LinClauseSat]⟩⟩
  obtain ⟨C, P, graph⟩ := build_graph (prune_taut refute.1)
  obtain ⟨r, lr, fr, prev, c, cr, d, dr, ne, introP, f, nf, br⟩ :=
    first_false graph hempty php_ax_sat
  have size : (Live P r).card ≤ 47 := by
    have hs : π'.length ≤ π.length := List.length_filter_le _ _
    exact (live_card_le P r).trans ((Nat.succ_le_of_lt lr).trans (hs.trans small))
  have rules : ∀ i ≤ r, Rule (linOfClause '' PHP 4 3) C P i :=
    fun i h => graph.1 i (h.trans_lt lr)
  by_cases high : 3 ≤ (WithArity P r 1).card
  · have ec : LocalEdge P r r c := ⟨le_rfl, by simp [Edge,introP]⟩
    have ed : LocalEdge P r r d := ⟨le_rfl, by simp [Edge,introP]⟩
    exact PEqualNP.Outside.L_pcx_118.High.high_impossible rows valid ids rules fr prev ec ed ne
      size high f nf br
  · let C' := fun i => strip (C i)
    have pu : ∀ D ∈ (linOfClause '' PHP 4 3), ∀ q ∈ D, q.1.card = 1 :=
      fun _ h => php_pure h
    have live : ∀ i ≤ r, ∃ a, FalseAt C a i :=
      fun i h => encoded_useful graph (h.trans_lt lr)
    have root : C' r = ∅ := strip_false fr
    have ss : ∀ i ≤ r, Rule (linOfClause '' PHP 4 3) C' P i :=
      strip_rules rules live pu
    have sf : ∀ a, FalseAt C' a r := by simp [FalseAt,root,LinClauseSat]
    have sl : ∀ i ≤ r, ∃ a, FalseAt C' a i := by
      intro i hi
      obtain ⟨a,ha⟩ := live i hi
      exact ⟨a, fun h => ha ((strip_sat (live i hi) a).1 h)⟩
    have recover := PEqualNP.Outside.L_pcx_118.Recovery.recover_of_few ss pu root sl (by omega)
    exact PEqualNP.Outside.L_pcx_118.Low.low_impossible ss sf (by simp [introP]) size recover

end PEqualNP.Outside.L_pcx_118.Main

theorem PEqualNP.Outside.L_pcx_118 : ¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 47) := by
  rintro ⟨π, refute, small⟩
  exact PEqualNP.Outside.L_pcx_118.Main.verify
    PEqualNP.Outside.L_pcx_118.Finite.allPivots
    PEqualNP.Outside.L_pcx_118.Finite.allPivots_checked
    PEqualNP.Outside.L_pcx_118.Finite.allPivots_ids π refute small
