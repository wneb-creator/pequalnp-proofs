import PEqualNP.Defs

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_10760_aux
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto

def SolN (R : ℕ → ℕ) (m T q t : ℕ) (S : Set ℕ) : Prop :=
  ∃ k ≤ q, ∃ u ≤ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k u S0

lemma SolN.mono {m T q t : ℕ} {S : Set ℕ} (h : SolN R m T q t S)
    {q' t' : ℕ} {S' : Set ℕ} (hq : q ≤ q') (ht : t ≤ t') (hS : S ⊆ S') :
    SolN R m T q' t' S' := by
  obtain ⟨k, hk, u, hu, S0, hs, hl⟩ := h
  exact ⟨k, hk.trans hq, u, hu.trans ht, S0, hs.trans hS, hl⟩

lemma SolN.done {m T q t : ℕ} {S : Set ℕ} (h : T ∈ S) : SolN R m T q t S :=
  ⟨0, by omega, 0, by omega, {T}, by simpa using h, .stop⟩

lemma SolN.un {m T q t a : ℕ} {S : Set ℕ}
    (ha : a ∈ S) (h : SolN R m T q t (insert (a ^^^ m) S)) :
    SolN R m T (q + 1) (t + 1) S := by
  obtain ⟨k, hk, u, hu, S1, hs, hl⟩ := h
  by_cases hg : a ^^^ m ∈ S1
  · refine ⟨k + 1, by omega, u + 1, by omega,
      insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
    intro x hx
    simp at hx
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ha
    · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, u, by omega, S1,
      fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

lemma SolN.bi {m T q t a b : ℕ} {d : Bool} {S : Set ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hal : Al R d a b)
    (h : SolN R m T q t (insert (op d a b) S)) :
    SolN R m T (q + 1) t S := by
  obtain ⟨k, hk, u, hu, S1, hs, hl⟩ := h
  by_cases hg : op d a b ∈ S1
  · by_cases hab : a = b
    · subst hab
      rw [op_self] at hs
      exact ⟨k, by omega, u, hu, S1,
        fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
    refine ⟨k + 1, by omega, u, hu,
      insert a (insert b (S1.erase (op d a b))), ?_,
      .bi hab hal (by rwa [Finset.insert_erase hg])⟩
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, u, hu, S1,
      fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

lemma SolN.toSol {m T q t : ℕ} {S : Set ℕ} (h : SolN R m T q t S) :
    Sol Z0 m T q S := by
  obtain ⟨k, hk, u, _, S0, hs, hl⟩ := h
  exact hl.sol.mono hk hs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0

def notWeight : GateOp → ℕ
  | .not => 1
  | _ => 0

lemma notWeight_zero {o : GateOp} (h : o ≠ GateOp.not) : notWeight o = 0 := by
  cases o <;> simp_all [notWeight]

def countNot : List Gate → ℕ
  | [] => 0
  | g :: gs => countNot gs + notWeight g.op

lemma countNot_tail_le (g : Gate) (gs : List Gate) : countNot gs ≤ countNot (g :: gs) := by
  simp [countNot]

lemma countNot_zero (gs : List Gate) (h : ∀ i : Fin gs.length,
    (gs.get i).op ≠ GateOp.not) : countNot gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op ≠ GateOp.not := h 0
    have ht : ∀ i : Fin gs.length, (gs.get i).op ≠ GateOp.not := fun i => h i.succ
    simp [countNot, notWeight_zero hg, ih ht]

lemma countNot_le_one (gs : List Gate)
    (h : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) : countNot gs ≤ 1 := by
  induction gs with
  | nil => simp [countNot]
  | cons g gs ih =>
    have ht : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
        (gs.get j).op = GateOp.not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (h i.succ j.succ hi hj)
    by_cases hg : g.op = GateOp.not
    · have hn : ∀ j : Fin gs.length, (gs.get j).op ≠ GateOp.not := by
        intro j hj
        have e := congrArg Fin.val (h 0 j.succ hg hj)
        simp at e
      simp [countNot, hg, notWeight, countNot_zero gs hn]
    · simpa [countNot, notWeight_zero hg] using ih ht

lemma ex_solN {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → SolN Z0 m T gs.length (countNot gs) S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → SolN Z0 m T (g :: gs).length (countNot (g :: gs)) S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) (countNot_tail_le g gs) subset_rfl
    have go : SolN Z0 m T gs.length (countNot gs) (insert (gv m w g) S) :=
      ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => simpa [countNot, notWeight] using SolN.bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => simpa [countNot, notWeight] using SolN.bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => simpa [countNot, notWeight] using SolN.un (rd i) go

lemma ex_live_one {T : ℕ} (gs : List Gate) (w : List ℕ) (S : Set ℕ)
    (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (hm : m ∈ S)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hT : ∃ i, (ex m gs w).getD i 0 = T)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) :
    ∃ k ≤ gs.length, ∃ t ≤ 1, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  obtain ⟨k, hk, t, ht, S0, hs, hl⟩ := ex_solN m gs w S hw h0 hm hg hT
  exact ⟨k, hk, t, ht.trans (countNot_le_one gs hn), S0, hs, hl⟩

end circuit
end PEqualNP.Outside.L_meta_10760_aux
