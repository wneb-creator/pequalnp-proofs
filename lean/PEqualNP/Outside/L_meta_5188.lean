import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5188

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]


def ok (gs : List Gate) : Prop := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Q (n : ℕ) (gs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  w < n + gs.length ∧ ∀ x, (run gs (List.ofFn x)).getD w false = f x

theorem q_app (n : ℕ) (gs hs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) (h : Q n gs w f) :
    Q n (gs ++ hs) w f := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [run_prefix _ _ _ _ (by simpa using h.1)]
  exact h.2 x

theorem q_in (n : ℕ) (gs : List Gate) (c : Fin n) : Q n gs c.val fun x => x c := by
  refine ⟨by have := c.isLt; omega, fun x => ?_⟩
  rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem q_op (n : ℕ) (gs : List Gate) (hok : ok gs) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (u v : ℕ) (f g : (Fin n → Bool) → Bool) (hu : Q n gs u f) (hv : Q n gs v g) :
    ok (gs ++ [⟨o, [u, v]⟩]) ∧ Q n (gs ++ [⟨o, [u, v]⟩]) (n + gs.length) fun x => o.eval [f x, g x] := by
  refine ⟨fun a ha => ?_, by simp, fun x => ?_⟩
  · rcases List.mem_append.1 ha with h | h
    · exact hok a h
    · rw [List.mem_singleton.1 h]; exact ⟨ho, le_rfl⟩
  · rw [run_snoc, getD_sn, if_pos (by rw [run_length, List.length_ofFn])]
    simp only [List.map_cons, List.map_nil, hu.2 x, hv.2 x]

theorem orN (n : ℕ) (N : Finset (Fin n)) (hN : N.Nonempty) : ∀ gs, ok gs →
    ∃ hs w, ok (gs ++ hs) ∧ hs.length + 1 = N.card ∧
      Q n (gs ++ hs) w fun x => decide (∃ u ∈ N, x u = true) := by
  induction hN using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro gs hok
    refine ⟨[], a.val, by simpa using hok, by simp, ?_⟩
    have := q_in n gs a
    simpa using this
  | cons a N ha hN ih =>
    intro gs hok
    obtain ⟨hs, w, h1, h2, h3⟩ := ih gs hok
    obtain ⟨k1, k2⟩ := q_op n (gs ++ hs) h1 GateOp.or (Or.inr rfl) a.val w _ _ (q_in n _ a) h3
    refine ⟨hs ++ [⟨GateOp.or, [a.val, w]⟩], n + (gs ++ hs).length,
      by rw [← List.append_assoc]; exact k1, by rw [Finset.card_cons, ← h2]; simp, ?_⟩
    have e : (fun x : Fin n → Bool => decide (∃ u ∈ Finset.cons a N ha, x u = true)) =
        fun x => GateOp.or.eval [x a, decide (∃ u ∈ N, x u = true)] := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [GateOp.eval]
    rw [e, ← List.append_assoc]
    exact k2

theorem star (n : ℕ) (c : Fin n) (N : Finset (Fin n)) (hN : N.Nonempty) (gs : List Gate) (hok : ok gs) :
    ∃ hs w, ok (gs ++ hs) ∧ hs.length = N.card ∧
      Q n (gs ++ hs) w fun x => x c && decide (∃ u ∈ N, x u = true) := by
  obtain ⟨hs, w, h1, h2, h3⟩ := orN n N hN gs hok
  obtain ⟨k1, k2⟩ := q_op n (gs ++ hs) h1 GateOp.and (Or.inl rfl) c.val w _ _ (q_in n _ c) h3
  refine ⟨hs ++ [⟨GateOp.and, [c.val, w]⟩], n + (gs ++ hs).length,
    by rw [← List.append_assoc]; exact k1, by rw [← h2]; simp, ?_⟩
  have e : (fun x : Fin n → Bool => x c && decide (∃ u ∈ N, x u = true)) =
      fun x => GateOp.and.eval [x c, decide (∃ u ∈ N, x u = true)] := by
    funext x
    simp [GateOp.eval]
  rw [e, ← List.append_assoc]
  exact k2

theorem addAll (n : ℕ) {ι : Type} [DecidableEq ι] (c : ι → Fin n) (N : ι → Finset (Fin n)) (k : ℕ)
    (S : Finset ι) (gs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) (hok : ok gs) (h : Q n gs w f)
    (hN : ∀ i ∈ S, (N i).card = k) (hk : 0 < k) :
    ∃ hs v, ok hs ∧ hs.length = gs.length + S.card * (k + 1) ∧
      Q n hs v fun x => f x || decide (∃ i ∈ S, x (c i) = true ∧ ∃ u ∈ N i, x u = true) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨gs, w, hok, by simp, by simpa using h⟩
  | insert a S ha ih =>
    obtain ⟨hs, v, h1, h2, h3⟩ := ih fun i hi => hN i (Finset.mem_insert_of_mem hi)
    have hca := hN a (Finset.mem_insert_self a S)
    obtain ⟨ts, u, k1, k2, k3⟩ := star n (c a) (N a) (Finset.card_pos.1 (by omega)) hs h1
    obtain ⟨l1, l2⟩ := q_op n (hs ++ ts) k1 GateOp.or (Or.inr rfl) u v _ _ k3 (q_app n hs ts v _ h3)
    refine ⟨hs ++ ts ++ [⟨GateOp.or, [u, v]⟩], n + (hs ++ ts).length, l1, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha, List.length_append, List.length_append, h2, k2, hca,
        Nat.add_mul]
      simp
      omega
    · have e : (fun x : Fin n → Bool => f x || decide (∃ i ∈ insert a S, x (c i) = true ∧
          ∃ u ∈ N i, x u = true)) = fun x => GateOp.or.eval
          [x (c a) && decide (∃ u ∈ N a, x u = true),
           f x || decide (∃ i ∈ S, x (c i) = true ∧ ∃ u ∈ N i, x u = true)] := by
        funext x
        rw [Bool.eq_iff_iff]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, Finset.exists_mem_insert]
        exact or_left_comm
      rw [e]; exact l2

end PEqualNP.Outside.L_meta_5188

open PEqualNP.Outside.L_meta_5188 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_5188 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.output < (26 : ℕ) + x2.size → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size + (40 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x6 || Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x8 ∧ x7 - x8 ∈ x1 ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true)) := by
  intro D C hC hout
  have hok : ok C.gates := fun g hg => by
    have := hC g hg
    exact ⟨by simpa using this.1, this.2⟩
  let N : Fin 13 → Finset (Fin 26) := fun l =>
    (Finset.univ.filter fun p : Fin 13 => p - l ∈ D).image fun p => (Fin.castAdd 13 p : Fin 26)
  have hN : ∀ l : Fin 13, (N l).card = 4 := by
    intro l
    simp only [N]
    rw [Finset.card_image_of_injective _ (Fin.castAdd_injective 13 13)]
    revert l
    simp only [D]
    decide +kernel
  obtain ⟨hs, v, h1, h2, h3⟩ := addAll 26 (fun l : Fin 13 => (Fin.natAdd 13 l : Fin 26)) N 4
    (Finset.univ.filter fun l : Fin 13 => 5 ≤ l.val) C.gates C.output (circuitFun 26 C) hok
    ⟨hout, fun x => rfl⟩ (fun l _ => hN l) (by omega)
  have hcard : (Finset.univ.filter fun l : Fin 13 => 5 ≤ l.val).card = 8 := by decide +kernel
  rw [hcard] at h2
  refine ⟨⟨hs, v⟩, fun g hg => ?_, ?_, fun x => ?_⟩
  · have := h1 g hg
    exact ⟨by simpa using this.1, this.2⟩
  · change hs.length ≤ C.gates.length + 40
    omega
  · refine (h3.2 x).trans ?_
    refine congrArg (fun b => circuitFun 26 C x || b) (decide_eq_decide.2 ?_)
    constructor
    · rintro ⟨l, hl, hx, u, hu, hxu⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨p, l, (Finset.mem_filter.1 hl).2, (Finset.mem_filter.1 hp).2, hxu, hx⟩
    · rintro ⟨p, l, hl, hp, hxp, hxl⟩
      exact ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩, hxl, Fin.castAdd 13 p,
        Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, rfl⟩, hxp⟩
