import Mathlib
import PEqualNP.Defs

-- The circuit builder below is from the checked L_meta_1003, moved into this namespace.

namespace PEqualNP.Outside.L_meta_5116_aux

namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end H926

namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end H926

namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

theorem orChain (k : ℕ) : ∀ m : ℕ, k + 1 ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = k ∧ out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∃ i : Fin (k + 1), w.getD i false = true) := by
  induction k with
  | zero =>
    intro m hm
    refine ⟨[], 0, by simp, rfl, by simp; omega, ?_⟩
    intro w _
    simp [wiresFrom]
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [⟨GateOp.or, [out, k + 1]⟩], m + gs.length, ?_, by simp [len], by simp, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD (k + 1) false = w.getD (k + 1) false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      have step : wiresFrom [⟨GateOp.or, [out, k + 1]⟩] v
          = v ++ [GateOp.or.eval ([out, k + 1].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [ev w hw, e1]
      simp [Fin.exists_fin_succ']

theorem or_size (n s : ℕ) :
    HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true)) s ↔ n ≤ s + 1 := by
  constructor
  · apply dep_lower
    intro i
    refine ⟨fun _ => false, ?_⟩
    simp only [Bool.not_false, ne_eq]
    have h1 : (∃ j : Fin n, Function.update (fun _ : Fin n => false) i true j = true) :=
      ⟨i, by simp⟩
    simp [h1]
  · intro h
    cases n with
    | zero =>
      refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
      intro x
      simp [Circuit.eval, Circuit.wires]
    | succ k =>
      obtain ⟨gs, out, ok, len, _, ev⟩ := orChain k (k + 1) le_rfl
      refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; omega, ?_⟩
      intro x
      have h := ev (List.ofFn x) (by simp)
      simp only [Circuit.eval, wires_eq, h, getD_ofFn]

end H926

namespace H926.EdgeUpper
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds H926

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edge_upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  apply bld_hasCircuitSize
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

end H926.EdgeUpper

namespace H926.EdgeUpper
open PEqualNP PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds H926

theorem edge_bld (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hE : ∃ i j : Fin n, G.Adj i j) (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 1) := by
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

theorem main : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∈ x4 ∨ x8 ∈ x4) → (∀ (x8 : Fin x1 → Bool), x5 x8 = Bool.true ↔ (∃ x9 ∈ x3, x8 x9 = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x5 (x3.card + x2.edgeSet.ncard + x4.card - (1 : ℕ)) := by
  classical
  intro n G A T f hE hcov hf
  have hcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hpos : 0 < G.edgeFinset.card := by
    obtain ⟨i0, j0, h0⟩ := hE
    exact Finset.card_pos.2 ⟨s(i0, j0), by simpa using h0⟩
  rw [hcard]
  have hedge := edge_bld n G T hE hcov
  apply bld_hasCircuitSize
  by_cases hA : A.Nonempty
  · have hor := bld_or (bld_anyFinset A hA) hedge
    have hAc : 0 < A.card := Finset.card_pos.2 hA
    refine bld_congr (bld_mono hor (by omega)) ?_
    intro x
    rw [Bool.eq_iff_iff, hf x]
    simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    subst hA
    refine bld_congr (bld_mono hedge (by simp)) ?_
    intro x
    rw [Bool.eq_iff_iff, hf x]
    simp

end H926.EdgeUpper

end PEqualNP.Outside.L_meta_5116_aux

theorem PEqualNP.Outside.L_meta_5116 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∈ x4 ∨ x8 ∈ x4) → (∀ (x8 : Fin x1 → Bool), x5 x8 = Bool.true ↔ (∃ x9 ∈ x3, x8 x9 = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x5 (x3.card + x2.edgeSet.ncard + x4.card - (1 : ℕ)) :=
  PEqualNP.Outside.L_meta_5116_aux.H926.EdgeUpper.main

