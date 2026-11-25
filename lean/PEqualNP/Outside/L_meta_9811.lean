import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Fin.Tuple.Basic
import PEqualNP.Defs

open PEqualNP.MetaComplexity


namespace PEqualNP.Outside.L_meta_9811_aux.Base

open PEqualNP.CircuitLowerBounds

 
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

 

lemma final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

 
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
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

end PEqualNP.Outside.L_meta_9811_aux.Base

namespace PEqualNP.Outside.L_meta_9811_aux.Base

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

 
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

 
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

 
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

 

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
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

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

 
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

 

lemma dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
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

end PEqualNP.Outside.L_meta_9811_aux.Base

namespace PEqualNP.Outside.L_meta_9811_aux.Base

open PEqualNP.CircuitLowerBounds

 
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

 
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

 
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

 

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

 
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

 

lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

 

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

 

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

 
lemma supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

lemma inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

lemma inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

 

lemma gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_9811_aux.Base

namespace PEqualNP.Outside.L_meta_9811_aux.Base

open PEqualNP.CircuitLowerBounds

 

lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

 

lemma simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

 
lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

 
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

lemma elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

 

lemma suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

lemma length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

 

lemma supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

 

 

lemma two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

 

lemma gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

 

 
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

lemma par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

 
lemma par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

 
lemma parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end PEqualNP.Outside.L_meta_9811_aux.Base

namespace PEqualNP.Outside.L_meta_9811_aux.Base

open PEqualNP.CircuitLowerBounds

 

 

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

 
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

lemma CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

lemma CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

lemma clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

lemma simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

lemma toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

 
lemma clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

 
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

 
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

lemma inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

 
lemma clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

 

lemma getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

 

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

lemma statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

lemma statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

lemma statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

lemma inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

 
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

lemma stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

 

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

lemma elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

lemma elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

 

lemma const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

 

lemma elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

 

 

lemma supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

 

lemma exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

 
lemma agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

 

 
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

lemma three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

 

lemma three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

 
lemma stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

 
lemma first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

 

lemma single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

 

lemma three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)

 

lemma par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

lemma par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

 

lemma clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this

 
lemma par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega

 
lemma parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_meta_9811_aux.Base

namespace PEqualNP.Outside.L_meta_9811_aux.Base

open PEqualNP.CircuitLowerBounds

 

 
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

lemma vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

lemma vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

lemma vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

 
lemma vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

 

lemma agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

 
lemma takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

lemma gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

lemma two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

 

lemma drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

 
lemma drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

 
lemma drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

 

 
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

 
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

 
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

lemma inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

lemma st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

lemma st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

lemma st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

 
lemma st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

lemma simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

lemma simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

lemma st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

 
lemma st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

lemma rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

lemma const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

 

lemma st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

lemma four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

 

 
def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

 

structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section ProofContext

variable {n : ℕ} {gs : List Gate} {o : ℕ}

lemma Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

lemma Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)

lemma Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩

 

lemma Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩

lemma Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])

 

lemma Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]

 
lemma Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2

lemma Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)

 
lemma Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0

 

lemma Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo

 

lemma Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa

 

lemma Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim

 
lemma Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)

 

lemma Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)

 
lemma Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega

 
lemma Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)

end ProofContext

 

 
lemma par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra

 
lemma parity_lower4 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_meta_9811_aux.Base

namespace PEqualNP.Outside.L_meta_9811_aux.Base.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

 

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

 
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

 
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

 
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

 
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

 
lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

 
lemma dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

lemma snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

 
lemma gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

 

lemma fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

end PEqualNP.Outside.L_meta_9811_aux.Base.PermInputs

namespace PEqualNP.Outside.L_meta_9811_aux.Base.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9811_aux.Base.PermInputs

 
lemma one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_9811_aux.Base.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.Outside.L_meta_9811_aux.Base.Forest

namespace PEqualNP.Outside.L_meta_9811_aux.Base.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9811_aux.Base
open PEqualNP.Outside.L_meta_9811_aux.Base.PermInputs

 

 
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

 
abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

 

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

 
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

 
def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

 
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

 
def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

 

 
structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

 
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

 

lemma dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

lemma Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

 
lemma has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

lemma reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

lemma reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

lemma vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

lemma vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

 

 
lemma exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

 

 
lemma drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

 

section ProofContext

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

 
lemma Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

 
lemma Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
lemma Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
lemma Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
lemma Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end ProofContext

 

lemma upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

lemma restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

 

lemma save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

 

section ProofContext

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.Outside.L_meta_9811_aux.Base.Readers.save n f gs o L.hcl L.hev i b hnc S hS

lemma Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

lemma Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

lemma Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

lemma rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

lemma rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

 
lemma Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

 

lemma Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end ProofContext

end PEqualNP.Outside.L_meta_9811_aux.Base.Readers

namespace PEqualNP.Outside.L_meta_9811_aux.Base.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9811_aux.Base

 
lemma gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section ProofContext

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

 
lemma Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end ProofContext

section ProofContext

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

 

lemma isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

 
lemma Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

 
lemma Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

 
lemma Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

 
lemma Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end ProofContext

end PEqualNP.Outside.L_meta_9811_aux.Base.Readers

namespace PEqualNP.Outside.L_meta_9811_aux.Base.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9811_aux.Base

 
lemma lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp

lemma set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

lemma set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

lemma set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section ProofContext

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

 
lemma Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h

 
lemma Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩

 

lemma Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end ProofContext

end PEqualNP.Outside.L_meta_9811_aux.Base.Readers

namespace PEqualNP.Outside.L_meta_9811_aux.Base.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9811_aux.Base

 

lemma fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf

 
lemma fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩

 

lemma noFunnel_of_sep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (h : ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q →
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p false q true) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q true))) : NoFunnel f := by
  intro p q hpq hdp hdq hf
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩⟩ := h p q hpq hdp hdq
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2

end PEqualNP.Outside.L_meta_9811_aux.Base.Readers

namespace PEqualNP.Outside.L_meta_9811_aux.Base

lemma readerTheorem : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ), (∃ p : Fin (n + 1), ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1), (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) → (∀ p q : Fin (n + 1), p ≠ q → (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool, f (Function.update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool, ∀ x : Fin (n + 1) → Bool, f (Function.update (Function.update x p (!a)) q b) = f (Function.update (Function.update x p a) q (!b)) ∧ f (Function.update (Function.update x p a) q (!b)) = f (Function.update (Function.update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') :=
  PEqualNP.Outside.L_meta_9811_aux.Base.Readers.fanout_step_3_4


end PEqualNP.Outside.L_meta_9811_aux.Base
namespace PEqualNP.Outside.L_meta_9811_aux
def dnf {α : Type} (cs : List (List α)) (x : α → Bool) : Bool :=
  cs.any (fun c => c.all x)

lemma dnf_eq_of_subsumption {α : Type} (S T : List (List α))
    (hST : ∀ c ∈ S, ∃ d ∈ T, ∀ a ∈ d, a ∈ c)
    (hTS : ∀ c ∈ T, ∃ d ∈ S, ∀ a ∈ d, a ∈ c)
    (x : α → Bool) : dnf S x = dnf T x := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnf, List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨c, hc, hx⟩
    obtain ⟨d, hd, hsub⟩ := hST c hc
    exact ⟨d, hd, fun a ha => hx a (hsub a ha)⟩
  · rintro ⟨c, hc, hx⟩
    obtain ⟨d, hd, hsub⟩ := hTS c hc
    exact ⟨d, hd, fun a ha => hx a (hsub a ha)⟩

lemma dnf_relabel {α β : Type} (cs : List (List α)) (ren : α → β)
    (x : β → Bool) : dnf cs (x ∘ ren) = dnf (cs.map (List.map ren)) x := by
  simp [dnf, List.any_map, List.all_map, Function.comp_def]

def pinClauses {α β : Type} [DecidableEq α] (cs : List (List α))
    (p : α) (b : Bool) (ren : α → β) : List (List β) :=
  (cs.filter (fun c => b || decide (p ∉ c))).map
    (fun c => (c.filter (fun a => decide (a ≠ p))).map ren)

lemma dnf_pin_relabel {α β : Type} [DecidableEq α] (cs : List (List α))
    (p : α) (b : Bool) (ren : α → β) (x : β → Bool) :
    dnf cs (Function.update (x ∘ ren) p b) = dnf (pinClauses cs p b ren) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnf, pinClauses, List.any_eq_true, List.all_eq_true,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨c, hc, hx⟩
    refine ⟨(c.filter (fun a => decide (a ≠ p))).map ren, ?_, ?_⟩
    · refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      by_cases hp : p ∈ c
      · have hb := hx p hp
        simp only [Function.update_self] at hb
        simp [hb]
      · simp [hp]
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hqc, hqp⟩ := List.mem_filter.mp hq
      have hne : q ≠ p := of_decide_eq_true hqp
      simpa [Function.update_of_ne hne, Function.comp_def] using hx q hqc
  · rintro ⟨d, ⟨c, ⟨hc, hcb⟩, rfl⟩, hx⟩
    refine ⟨c, hc, ?_⟩
    intro a ha
    by_cases hap : a = p
    · subst a
      have hb : b = true := by simpa [ha] using hcb
      simpa using hb
    · have hv := hx (ren a) (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using hap⟩, rfl⟩)
      simpa [Function.update_of_ne hap, Function.comp_def] using hv


lemma dep_mem_support {n : ℕ} (f : (Fin n → Bool) → Bool)
    (T : Finset (Fin n))
    (hSupp : ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) → f x = f y)
    (p : Fin n)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x) : p ∈ T := by
  by_contra hp
  obtain ⟨x, hx⟩ := hdep
  apply hx
  apply hSupp
  intro i hi
  have hip : i ≠ p := by
    intro he
    apply hp
    simpa [he] using hi
  exact Function.update_of_ne hip (!x p) x


open PEqualNP.MetaComplexity
def wi (m : Nat) (i : Fin 14) : Bool := m.testBit i.val
def f0 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 5 && x 7)
def cs0 : List (List (Fin 14)) := [[4,5],[2,6],[3,6],[5,6],[0,7],[1,7],[5,7]]
lemma d0 (x : Fin 14 → Bool) : f0 x = dnf cs0 x := by
  simp [f0, cs0, dnf]
  <;> ac_rfl
def T0 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup0 (x y : Fin 14 → Bool) (h : ∀ i ∈ T0, x i = y i) : f0 x = f0 y := by
  simp only [f0, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep0 : ∀ p ∈ T0, Base.Readers.Dep f0 p := by
  have hc : ∀ p : Fin 14, p ∈ T0 → f0 (Function.update (wi (([128,128,64,64,32,16,4,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([128,128,64,64,32,16,4,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f0 (wi (([128,128,64,64,32,16,4,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([128,128,64,64,32,16,4,1,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower0 (s : Nat) (h : HasCircuitSize 14 f0 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f0 T0 dep0 s h
  have ht : T0.card = 8 := by decide +kernel
  omega
def f1 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 5 && x 7)
def cs1 : List (List (Fin 14)) := [[0],[3,6],[4,6],[5,6],[1,7],[2,7],[5,7]]
lemma d1 (x : Fin 14 → Bool) : f1 x = dnf cs1 x := by
  simp [f1, cs1, dnf]
  <;> ac_rfl
def T1 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup1 (x y : Fin 14 → Bool) (h : ∀ i ∈ T1, x i = y i) : f1 x = f1 y := by
  simp only [f1, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep1 : ∀ p ∈ T1, Base.Readers.Dep f1 p := by
  have hc : ∀ p : Fin 14, p ∈ T1 → f1 (Function.update (wi (([0,128,128,64,64,64,8,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,128,128,64,64,64,8,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f1 (wi (([0,128,128,64,64,64,8,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,128,128,64,64,64,8,2,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower1 (s : Nat) (h : HasCircuitSize 14 f1 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f1 T1 dep1 s h
  have ht : T1.card = 8 := by decide +kernel
  omega
def f2 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 6 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 6 && x 8)
def cs2 : List (List (Fin 14)) := [[4,5],[5,6],[2,7],[3,7],[6,7],[0,8],[1,8],[6,8]]
lemma d2 (x : Fin 14 → Bool) : f2 x = dnf cs2 x := by
  simp [f2, cs2, dnf]
  <;> ac_rfl
def T2 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup2 (x y : Fin 14 → Bool) (h : ∀ i ∈ T2, x i = y i) : f2 x = f2 y := by
  simp only [f2, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep2 : ∀ p ∈ T2, Base.Readers.Dep f2 p := by
  have hc : ∀ p : Fin 14, p ∈ T2 → f2 (Function.update (wi (([256,256,128,128,32,16,32,4,1,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([256,256,128,128,32,16,32,4,1,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f2 (wi (([256,256,128,128,32,16,32,4,1,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([256,256,128,128,32,16,32,4,1,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower2 (s : Nat) (h : HasCircuitSize 14 f2 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f2 4 s
    (dep2 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 96, by decide +kernel⟩
      · exact ⟨wi 0, wi 32, by decide +kernel⟩) h
  cases b
  · have hh := lower0
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,5,6,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f2 (Function.update (x ∘ ren) 4 false)) = f0 := by
      funext x
      rw [d2, d0, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f2 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower1
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,4,0,0,5,6,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f2 (Function.update (x ∘ ren) 4 true)) = f1 := by
      funext x
      rw [d2, d1, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f2 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f3 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7)
def cs3 : List (List (Fin 14)) := [[0],[1],[2],[4,6],[5,6],[3,7],[5,7]]
lemma d3 (x : Fin 14 → Bool) : f3 x = dnf cs3 x := by
  simp [f3, cs3, dnf]
  <;> ac_rfl
def T3 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup3 (x y : Fin 14 → Bool) (h : ∀ i ∈ T3, x i = y i) : f3 x = f3 y := by
  simp only [f3, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep3 : ∀ p ∈ T3, Base.Readers.Dep f3 p := by
  have hc : ∀ p : Fin 14, p ∈ T3 → f3 (Function.update (wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f3 (wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower3 (s : Nat) (h : HasCircuitSize 14 f3 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f3 T3 dep3 s h
  have ht : T3.card = 8 := by decide +kernel
  omega
def f4 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 4 && x 5) || (x 6 && x 7)
def cs4 : List (List (Fin 14)) := [[0],[1],[2],[3],[4,5],[6,7]]
lemma d4 (x : Fin 14 → Bool) : f4 x = dnf cs4 x := by
  simp [f4, cs4, dnf]
  <;> ac_rfl
def T4 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup4 (x y : Fin 14 → Bool) (h : ∀ i ∈ T4, x i = y i) : f4 x = f4 y := by
  simp only [f4, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep4 : ∀ p ∈ T4, Base.Readers.Dep f4 p := by
  have hc : ∀ p : Fin 14, p ∈ T4 → f4 (Function.update (wi (([0,0,0,0,32,16,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,32,16,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f4 (wi (([0,0,0,0,32,16,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,32,16,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower4 (s : Nat) (h : HasCircuitSize 14 f4 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f4 T4 dep4 s h
  have ht : T4.card = 8 := by decide +kernel
  omega
def f5 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 6) || (x 4 && x 7) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8)
def cs5 : List (List (Fin 14)) := [[0],[1],[2],[5,6],[4,7],[3,8],[6,8],[7,8]]
lemma d5 (x : Fin 14 → Bool) : f5 x = dnf cs5 x := by
  simp [f5, cs5, dnf]
  <;> ac_rfl
def T5 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup5 (x y : Fin 14 → Bool) (h : ∀ i ∈ T5, x i = y i) : f5 x = f5 y := by
  simp only [f5, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep5 : ∀ p ∈ T5, Base.Readers.Dep f5 p := by
  have hc : ∀ p : Fin 14, p ∈ T5 → f5 (Function.update (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f5 (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower5 (s : Nat) (h : HasCircuitSize 14 f5 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f5 3 s
    (dep5 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower3
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,3,4,6,7,5,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f5 (Function.update (x ∘ ren) 3 false)) = f3 := by
      funext x
      rw [d5, d3, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f5 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower4
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,0,5,7,6,4,2,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f5 (Function.update (x ∘ ren) 3 true)) = f4 := by
      funext x
      rw [d5, d4, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f5 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f6 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 0 && x 9) || (x 2 && x 9) || (x 6 && x 9)
def cs6 : List (List (Fin 14)) := [[4,5],[5,6],[2,7],[3,7],[4,7],[1,8],[3,8],[6,8],[0,9],[2,9],[6,9]]
lemma d6 (x : Fin 14 → Bool) : f6 x = dnf cs6 x := by
  simp [f6, cs6, dnf]
  <;> ac_rfl
def T6 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup6 (x y : Fin 14 → Bool) (h : ∀ i ∈ T6, x i = y i) : f6 x = f6 y := by
  simp only [f6, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep6 : ∀ p ∈ T6, Base.Readers.Dep f6 p := by
  have hc : ∀ p : Fin 14, p ∈ T6 → f6 (Function.update (wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f6 (wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower6 (s : Nat) (h : HasCircuitSize 14 f6 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f6 7 s
    (dep6 7 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 4, by decide +kernel⟩) h
  cases b
  · have hh := lower2
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,1,3,0,4,5,6,0,8,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f6 (Function.update (x ∘ ren) 7 false)) = f2 := by
      funext x
      rw [d6, d2, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f6 (Function.update (x ∘ ren) 7 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower5
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,5,2,1,0,3,8,0,6,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f6 (Function.update (x ∘ ren) 7 true)) = f5 := by
      funext x
      rw [d6, d5, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f6 (Function.update (x ∘ ren) 7 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f7 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7)
def cs7 : List (List (Fin 14)) := [[0],[1],[4,6],[5,6],[2,7],[3,7],[5,7]]
lemma d7 (x : Fin 14 → Bool) : f7 x = dnf cs7 x := by
  simp [f7, cs7, dnf]
  <;> ac_rfl
def T7 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup7 (x y : Fin 14 → Bool) (h : ∀ i ∈ T7, x i = y i) : f7 x = f7 y := by
  simp only [f7, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep7 : ∀ p ∈ T7, Base.Readers.Dep f7 p := by
  have hc : ∀ p : Fin 14, p ∈ T7 → f7 (Function.update (wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f7 (wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower7 (s : Nat) (h : HasCircuitSize 14 f7 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f7 T7 dep7 s h
  have ht : T7.card = 8 := by decide +kernel
  omega
def f8 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 5 && x 6) || (x 4 && x 7) || (x 6 && x 7)
def cs8 : List (List (Fin 14)) := [[0],[1],[2],[3],[5,6],[4,7],[6,7]]
lemma d8 (x : Fin 14 → Bool) : f8 x = dnf cs8 x := by
  simp [f8, cs8, dnf]
  <;> ac_rfl
def T8 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup8 (x y : Fin 14 → Bool) (h : ∀ i ∈ T8, x i = y i) : f8 x = f8 y := by
  simp only [f8, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep8 : ∀ p ∈ T8, Base.Readers.Dep f8 p := by
  have hc : ∀ p : Fin 14, p ∈ T8 → f8 (Function.update (wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f8 (wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower8 (s : Nat) (h : HasCircuitSize 14 f8 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f8 T8 dep8 s h
  have ht : T8.card = 8 := by decide +kernel
  omega
def f9 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8)
def cs9 : List (List (Fin 14)) := [[0],[1],[4,6],[5,6],[3,7],[5,7],[2,8],[3,8],[4,8]]
lemma d9 (x : Fin 14 → Bool) : f9 x = dnf cs9 x := by
  simp [f9, cs9, dnf]
  <;> ac_rfl
def T9 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup9 (x y : Fin 14 → Bool) (h : ∀ i ∈ T9, x i = y i) : f9 x = f9 y := by
  simp only [f9, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep9 : ∀ p ∈ T9, Base.Readers.Dep f9 p := by
  have hc : ∀ p : Fin 14, p ∈ T9 → f9 (Function.update (wi (([0,0,256,128,64,64,16,8,4,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,256,128,64,64,16,8,4,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f9 (wi (([0,0,256,128,64,64,16,8,4,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,256,128,64,64,16,8,4,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower9 (s : Nat) (h : HasCircuitSize 14 f9 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f9 6 s
    (dep9 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower7
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,5,2,4,0,6,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f9 (Function.update (x ∘ ren) 6 false)) = f7 := by
      funext x
      rw [d9, d7, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f9 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower8
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,5,7,1,2,0,4,6,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f9 (Function.update (x ∘ ren) 6 true)) = f8 := by
      funext x
      rw [d9, d8, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f9 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f10 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || (x 5 && x 7) || (x 6 && x 7)
def cs10 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[5,7],[6,7]]
lemma d10 (x : Fin 14 → Bool) : f10 x = dnf cs10 x := by
  simp [f10, cs10, dnf]
  <;> ac_rfl
def T10 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup10 (x y : Fin 14 → Bool) (h : ∀ i ∈ T10, x i = y i) : f10 x = f10 y := by
  simp only [f10, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep10 : ∀ p ∈ T10, Base.Readers.Dep f10 p := by
  have hc : ∀ p : Fin 14, p ∈ T10 → f10 (Function.update (wi (([0,0,0,0,0,128,128,32,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,128,128,32,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f10 (wi (([0,0,0,0,0,128,128,32,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,128,128,32,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower10 (s : Nat) (h : HasCircuitSize 14 f10 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f10 T10 dep10 s h
  have ht : T10.card = 8 := by decide +kernel
  omega
def f11 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 5 && x 7) || (x 6 && x 7) || (x 4 && x 8) || (x 6 && x 8)
def cs11 : List (List (Fin 14)) := [[0],[1],[2],[3],[5,7],[6,7],[4,8],[6,8]]
lemma d11 (x : Fin 14 → Bool) : f11 x = dnf cs11 x := by
  simp [f11, cs11, dnf]
  <;> ac_rfl
def T11 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup11 (x y : Fin 14 → Bool) (h : ∀ i ∈ T11, x i = y i) : f11 x = f11 y := by
  simp only [f11, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep11 : ∀ p ∈ T11, Base.Readers.Dep f11 p := by
  have hc : ∀ p : Fin 14, p ∈ T11 → f11 (Function.update (wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f11 (wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower11 (s : Nat) (h : HasCircuitSize 14 f11 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f11 4 s
    (dep11 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower8
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,6,7,5,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f11 (Function.update (x ∘ ren) 4 false)) = f8 := by
      funext x
      rw [d11, d8, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f11 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower10
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,0,6,5,7,1,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f11 (Function.update (x ∘ ren) 4 true)) = f10 := by
      funext x
      rw [d11, d10, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f11 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f12 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 5) || (x 3 && x 6) || (x 2 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 4 && x 9)
def cs12 : List (List (Fin 14)) := [[0],[1],[4,5],[3,6],[2,7],[5,8],[6,8],[7,8],[2,9],[3,9],[4,9]]
lemma d12 (x : Fin 14 → Bool) : f12 x = dnf cs12 x := by
  simp [f12, cs12, dnf]
  <;> ac_rfl
def T12 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup12 (x y : Fin 14 → Bool) (h : ∀ i ∈ T12, x i = y i) : f12 x = f12 y := by
  simp only [f12, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep12 : ∀ p ∈ T12, Base.Readers.Dep f12 p := by
  have hc : ∀ p : Fin 14, p ∈ T12 → f12 (Function.update (wi (([0,0,128,64,32,16,8,4,32,4,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,64,32,16,8,4,32,4,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f12 (wi (([0,0,128,64,32,16,8,4,32,4,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,64,32,16,8,4,32,4,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower12 (s : Nat) (h : HasCircuitSize 14 f12 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f12 2 s
    (dep12 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower9
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,6,7,3,4,2,8,5,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f12 (Function.update (x ∘ ren) 2 false)) = f9 := by
      funext x
      rw [d12, d9, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f12 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower11
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,0,4,5,7,8,2,6,1,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f12 (Function.update (x ∘ ren) 2 true)) = f11 := by
      funext x
      rw [d12, d11, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f12 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f13 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 7 && x 8) || (x 0 && x 9) || (x 2 && x 9) || (x 7 && x 9) || (x 0 && x 10) || (x 1 && x 10) || (x 4 && x 10)
def cs13 : List (List (Fin 14)) := [[4,5],[2,6],[3,6],[5,7],[1,8],[3,8],[7,8],[0,9],[2,9],[7,9],[0,10],[1,10],[4,10]]
lemma d13 (x : Fin 14 → Bool) : f13 x = dnf cs13 x := by
  simp [f13, cs13, dnf]
  <;> ac_rfl
def T13 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup13 (x y : Fin 14 → Bool) (h : ∀ i ∈ T13, x i = y i) : f13 x = f13 y := by
  simp only [f13, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep13 : ∀ p ∈ T13, Base.Readers.Dep f13 p := by
  have hc : ∀ p : Fin 14, p ∈ T13 → f13 (Function.update (wi (([512,256,64,64,32,16,4,32,2,1,1,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([512,256,64,64,32,16,4,32,2,1,1,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f13 (wi (([512,256,64,64,32,16,4,32,2,1,1,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([512,256,64,64,32,16,4,32,2,1,1,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower13 (s : Nat) (h : HasCircuitSize 14 f13 s) : 13 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f13 6 s
    (dep13 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 4, by decide +kernel⟩) h
  cases b
  · have hh := lower6
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,2,1,0,4,5,0,6,9,8,7,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f13 (Function.update (x ∘ ren) 6 false)) = f6 := by
      funext x
      rw [d13, d6, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f13 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower12
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([6,7,1,0,5,4,0,9,2,3,8,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f13 (Function.update (x ∘ ren) 6 true)) = f12 := by
      funext x
      rw [d13, d12, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f13 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f14 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8)
def cs14 : List (List (Fin 14)) := [[0],[4,6],[5,6],[2,7],[3,7],[5,7],[1,8],[3,8],[4,8]]
lemma d14 (x : Fin 14 → Bool) : f14 x = dnf cs14 x := by
  simp [f14, cs14, dnf]
  <;> ac_rfl
def T14 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup14 (x y : Fin 14 → Bool) (h : ∀ i ∈ T14, x i = y i) : f14 x = f14 y := by
  simp only [f14, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep14 : ∀ p ∈ T14, Base.Readers.Dep f14 p := by
  have hc : ∀ p : Fin 14, p ∈ T14 → f14 (Function.update (wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f14 (wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower14 (s : Nat) (h : HasCircuitSize 14 f14 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f14 6 s
    (dep14 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower1
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,2,5,4,1,0,7,6,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f14 (Function.update (x ∘ ren) 6 false)) = f1 := by
      funext x
      rw [d14, d1, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f14 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower3
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,4,5,2,1,0,6,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f14 (Function.update (x ∘ ren) 6 true)) = f3 := by
      funext x
      rw [d14, d3, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f14 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f15 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7) || (x 3 && x 8) || (x 4 && x 8)
def cs15 : List (List (Fin 14)) := [[0],[1],[2],[4,6],[5,6],[3,7],[5,7],[3,8],[4,8]]
lemma d15 (x : Fin 14 → Bool) : f15 x = dnf cs15 x := by
  simp [f15, cs15, dnf]
  <;> ac_rfl
def T15 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup15 (x y : Fin 14 → Bool) (h : ∀ i ∈ T15, x i = y i) : f15 x = f15 y := by
  simp only [f15, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep15 : ∀ p ∈ T15, Base.Readers.Dep f15 p := by
  have hc : ∀ p : Fin 14, p ∈ T15 → f15 (Function.update (wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f15 (wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower15 (s : Nat) (h : HasCircuitSize 14 f15 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f15 3 s
    (dep15 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower3
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,7,6,5,4,3,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f15 (Function.update (x ∘ ren) 3 false)) = f3 := by
      funext x
      rw [d15, d3, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f15 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower10
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,4,0,5,6,7,3,2,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f15 (Function.update (x ∘ ren) 3 true)) = f10 := by
      funext x
      rw [d15, d10, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f15 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f16 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 1 && x 9) || (x 2 && x 9) || (x 4 && x 9)
def cs16 : List (List (Fin 14)) := [[0],[4,6],[5,6],[2,7],[3,7],[1,8],[3,8],[5,8],[1,9],[2,9],[4,9]]
lemma d16 (x : Fin 14 → Bool) : f16 x = dnf cs16 x := by
  simp [f16, cs16, dnf]
  <;> ac_rfl
def T16 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup16 (x y : Fin 14 → Bool) (h : ∀ i ∈ T16, x i = y i) : f16 x = f16 y := by
  simp only [f16, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep16 : ∀ p ∈ T16, Base.Readers.Dep f16 p := by
  have hc : ∀ p : Fin 14, p ∈ T16 → f16 (Function.update (wi (([0,256,128,128,64,64,16,4,2,2,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,256,128,128,64,64,16,4,2,2,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f16 (wi (([0,256,128,128,64,64,16,4,2,2,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,256,128,128,64,64,16,4,2,2,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower16 (s : Nat) (h : HasCircuitSize 14 f16 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f16 6 s
    (dep16 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower14
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,5,4,2,1,0,6,8,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f16 (Function.update (x ∘ ren) 6 false)) = f14 := by
      funext x
      rw [d16, d14, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f16 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower15
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,8,6,7,2,1,0,5,3,4,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f16 (Function.update (x ∘ ren) 6 true)) = f15 := by
      funext x
      rw [d16, d15, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f16 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f17 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
def cs17 : List (List (Fin 14)) := [[0],[1],[2],[5,6],[3,7],[4,7],[6,7]]
lemma d17 (x : Fin 14 → Bool) : f17 x = dnf cs17 x := by
  simp [f17, cs17, dnf]
  <;> ac_rfl
def T17 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup17 (x y : Fin 14 → Bool) (h : ∀ i ∈ T17, x i = y i) : f17 x = f17 y := by
  simp only [f17, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep17 : ∀ p ∈ T17, Base.Readers.Dep f17 p := by
  have hc : ∀ p : Fin 14, p ∈ T17 → f17 (Function.update (wi (([0,0,0,128,128,64,32,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,128,128,64,32,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f17 (wi (([0,0,0,128,128,64,32,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,128,128,64,32,8,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower17 (s : Nat) (h : HasCircuitSize 14 f17 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f17 T17 dep17 s h
  have ht : T17.card = 8 := by decide +kernel
  omega
def f18 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def cs18 : List (List (Fin 14)) := [[0],[1],[2],[3],[4,7],[5,7],[6,7]]
lemma d18 (x : Fin 14 → Bool) : f18 x = dnf cs18 x := by
  simp [f18, cs18, dnf]
  <;> ac_rfl
def T18 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup18 (x y : Fin 14 → Bool) (h : ∀ i ∈ T18, x i = y i) : f18 x = f18 y := by
  simp only [f18, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep18 : ∀ p ∈ T18, Base.Readers.Dep f18 p := by
  have hc : ∀ p : Fin 14, p ∈ T18 → f18 (Function.update (wi (([0,0,0,0,128,128,128,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,128,128,128,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f18 (wi (([0,0,0,0,128,128,128,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,128,128,128,16,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower18 (s : Nat) (h : HasCircuitSize 14 f18 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f18 T18 dep18 s h
  have ht : T18.card = 8 := by decide +kernel
  omega
def f19 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)
def cs19 : List (List (Fin 14)) := [[0],[1],[2],[5,7],[6,7],[3,8],[4,8],[6,8]]
lemma d19 (x : Fin 14 → Bool) : f19 x = dnf cs19 x := by
  simp [f19, cs19, dnf]
  <;> ac_rfl
def T19 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup19 (x y : Fin 14 → Bool) (h : ∀ i ∈ T19, x i = y i) : f19 x = f19 y := by
  simp only [f19, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep19 : ∀ p ∈ T19, Base.Readers.Dep f19 p := by
  have hc : ∀ p : Fin 14, p ∈ T19 → f19 (Function.update (wi (([0,0,0,256,256,128,128,32,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,256,256,128,128,32,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f19 (wi (([0,0,0,256,256,128,128,32,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,256,256,128,128,32,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower19 (s : Nat) (h : HasCircuitSize 14 f19 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f19 5 s
    (dep19 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower17
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,0,6,5,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f19 (Function.update (x ∘ ren) 5 false)) = f17 := by
      funext x
      rw [d19, d17, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f19 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower18
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,5,6,0,4,0,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f19 (Function.update (x ∘ ren) 5 true)) = f18 := by
      funext x
      rw [d19, d18, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f19 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f20 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 5 && x 9)
def cs20 : List (List (Fin 14)) := [[0],[1],[5,7],[6,7],[3,8],[4,8],[6,8],[2,9],[4,9],[5,9]]
lemma d20 (x : Fin 14 → Bool) : f20 x = dnf cs20 x := by
  simp [f20, cs20, dnf]
  <;> ac_rfl
def T20 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup20 (x y : Fin 14 → Bool) (h : ∀ i ∈ T20, x i = y i) : f20 x = f20 y := by
  simp only [f20, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep20 : ∀ p ∈ T20, Base.Readers.Dep f20 p := by
  have hc : ∀ p : Fin 14, p ∈ T20 → f20 (Function.update (wi (([0,0,512,256,256,128,128,32,8,4,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,512,256,256,128,128,32,8,4,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f20 (wi (([0,0,512,256,256,128,128,32,8,4,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,512,256,256,128,128,32,8,4,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower20 (s : Nat) (h : HasCircuitSize 14 f20 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f20 2 s
    (dep20 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower9
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,2,4,5,3,7,8,6,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f20 (Function.update (x ∘ ren) 2 false)) = f9 := by
      funext x
      rw [d20, d9, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f20 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower19
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,0,4,3,5,6,7,8,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f20 (Function.update (x ∘ ren) 2 true)) = f19 := by
      funext x
      rw [d20, d19, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f20 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f21 (x : Fin 14 → Bool) : Bool := x 0 || (x 5 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 5 && x 9) || (x 1 && x 10) || (x 2 && x 10) || (x 3 && x 10)
def cs21 : List (List (Fin 14)) := [[0],[5,7],[6,7],[3,8],[4,8],[6,8],[2,9],[4,9],[5,9],[1,10],[2,10],[3,10]]
lemma d21 (x : Fin 14 → Bool) : f21 x = dnf cs21 x := by
  simp [f21, cs21, dnf]
  <;> ac_rfl
def T21 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup21 (x y : Fin 14 → Bool) (h : ∀ i ∈ T21, x i = y i) : f21 x = f21 y := by
  simp only [f21, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep21 : ∀ p ∈ T21, Base.Readers.Dep f21 p := by
  have hc : ∀ p : Fin 14, p ∈ T21 → f21 (Function.update (wi (([0,1024,512,256,256,128,128,32,8,4,2,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,1024,512,256,256,128,128,32,8,4,2,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f21 (wi (([0,1024,512,256,256,128,128,32,8,4,2,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,1024,512,256,256,128,128,32,8,4,2,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower21 (s : Nat) (h : HasCircuitSize 14 f21 s) : 13 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f21 1 s
    (dep21 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower16
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,2,3,1,4,5,6,8,9,7,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f21 (Function.update (x ∘ ren) 1 false)) = f16 := by
      funext x
      rw [d21, d16, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f21 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower20
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,3,4,5,6,7,8,9,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f21 (Function.update (x ∘ ren) 1 true)) = f20 := by
      funext x
      rw [d21, d20, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f21 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f22 (x : Fin 14 → Bool) : Bool := (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 7 && x 9) || (x 1 && x 10) || (x 2 && x 10) || (x 3 && x 10) || (x 0 && x 11) || (x 1 && x 11) || (x 7 && x 11)
def cs22 : List (List (Fin 14)) := [[4,6],[5,6],[3,8],[5,8],[7,8],[2,9],[4,9],[7,9],[1,10],[2,10],[3,10],[0,11],[1,11],[7,11]]
lemma d22 (x : Fin 14 → Bool) : f22 x = dnf cs22 x := by
  simp [f22, cs22, dnf]
  <;> ac_rfl
def T22 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup22 (x y : Fin 14 → Bool) (h : ∀ i ∈ T22, x i = y i) : f22 x = f22 y := by
  simp only [f22, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep22 : ∀ p ∈ T22, Base.Readers.Dep f22 p := by
  have hc : ∀ p : Fin 14, p ∈ T22 → f22 (Function.update (wi (([2048,1024,512,256,64,64,16,256,8,4,2,1,0,0] : List Nat).getD p.val 0)) p (!(wi (([2048,1024,512,256,64,64,16,256,8,4,2,1,0,0] : List Nat).getD p.val 0)) p)) ≠ f22 (wi (([2048,1024,512,256,64,64,16,256,8,4,2,1,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([2048,1024,512,256,64,64,16,256,8,4,2,1,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower22 (s : Nat) (h : HasCircuitSize 14 f22 s) : 15 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f22 0 s
    (dep22 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 80, by decide +kernel⟩
      · exact ⟨wi 0, wi 2048, by decide +kernel⟩) h
  cases b
  · have hh := lower13
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,0,1,2,3,6,7,8,9,10,5,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f22 (Function.update (x ∘ ren) 0 false)) = f13 := by
      funext x
      rw [d22, d13, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f22 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower21
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,5,6,7,4,8,9,10,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f22 (Function.update (x ∘ ren) 0 true)) = f21 := by
      funext x
      rw [d22, d21, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f22 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f23 (x : Fin 14 → Bool) : Bool := (x 1 && x 3) || (x 2 && x 3) || (x 0 && x 4) || (x 2 && x 4)
def cs23 : List (List (Fin 14)) := [[1,3],[2,3],[0,4],[2,4]]
lemma d23 (x : Fin 14 → Bool) : f23 x = dnf cs23 x := by
  simp [f23, cs23, dnf]
  <;> ac_rfl
def T23 : Finset (Fin 14) := {0, 1, 2, 3, 4}
lemma sup23 (x y : Fin 14 → Bool) (h : ∀ i ∈ T23, x i = y i) : f23 x = f23 y := by
  simp only [f23, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
lemma dep23 : ∀ p ∈ T23, Base.Readers.Dep f23 p := by
  have hc : ∀ p : Fin 14, p ∈ T23 → f23 (Function.update (wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f23 (wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower23 (s : Nat) (h : HasCircuitSize 14 f23 s) : 4 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f23 T23 dep23 s h
  have ht : T23.card = 5 := by decide +kernel
  omega
def f24 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 2 && x 4) || (x 3 && x 4)
def cs24 : List (List (Fin 14)) := [[0],[1],[2,4],[3,4]]
lemma d24 (x : Fin 14 → Bool) : f24 x = dnf cs24 x := by
  simp [f24, cs24, dnf]
  <;> ac_rfl
def T24 : Finset (Fin 14) := {0, 1, 2, 3, 4}
lemma sup24 (x y : Fin 14 → Bool) (h : ∀ i ∈ T24, x i = y i) : f24 x = f24 y := by
  simp only [f24, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
lemma dep24 : ∀ p ∈ T24, Base.Readers.Dep f24 p := by
  have hc : ∀ p : Fin 14, p ∈ T24 → f24 (Function.update (wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f24 (wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower24 (s : Nat) (h : HasCircuitSize 14 f24 s) : 4 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f24 T24 dep24 s h
  have ht : T24.card = 5 := by decide +kernel
  omega
def f25 (x : Fin 14 → Bool) : Bool := (x 1 && x 3) || (x 2 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5)
def cs25 : List (List (Fin 14)) := [[1,3],[2,3],[0,4],[2,4],[0,5],[1,5]]
lemma d25 (x : Fin 14 → Bool) : f25 x = dnf cs25 x := by
  simp [f25, cs25, dnf]
  <;> ac_rfl
def T25 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup25 (x y : Fin 14 → Bool) (h : ∀ i ∈ T25, x i = y i) : f25 x = f25 y := by
  simp only [f25, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep25 : ∀ p ∈ T25, Base.Readers.Dep f25 p := by
  have hc : ∀ p : Fin 14, p ∈ T25 → f25 (Function.update (wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f25 (wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower25 (s : Nat) (h : HasCircuitSize 14 f25 s) : 6 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f25 0 s
    (dep25 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 10, by decide +kernel⟩
      · exact ⟨wi 0, wi 16, by decide +kernel⟩) h
  cases b
  · have hh := lower23
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,3,2,1,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f25 (Function.update (x ∘ ren) 0 false)) = f23 := by
      funext x
      rw [d25, d23, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f25 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower24
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,1,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f25 (Function.update (x ∘ ren) 0 true)) = f24 := by
      funext x
      rw [d25, d24, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f25 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f26 (x : Fin 14 → Bool) : Bool := x 0 || (x 2 && x 3) || (x 1 && x 4) || (x 3 && x 4)
def cs26 : List (List (Fin 14)) := [[0],[2,3],[1,4],[3,4]]
lemma d26 (x : Fin 14 → Bool) : f26 x = dnf cs26 x := by
  simp [f26, cs26, dnf]
  <;> ac_rfl
def T26 : Finset (Fin 14) := {0, 1, 2, 3, 4}
lemma sup26 (x y : Fin 14 → Bool) (h : ∀ i ∈ T26, x i = y i) : f26 x = f26 y := by
  simp only [f26, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
lemma dep26 : ∀ p ∈ T26, Base.Readers.Dep f26 p := by
  have hc : ∀ p : Fin 14, p ∈ T26 → f26 (Function.update (wi (([0,16,8,4,2,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,16,8,4,2,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f26 (wi (([0,16,8,4,2,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,16,8,4,2,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower26 (s : Nat) (h : HasCircuitSize 14 f26 s) : 4 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f26 T26 dep26 s h
  have ht : T26.card = 5 := by decide +kernel
  omega
def f27 (x : Fin 14 → Bool) : Bool := x 0 || (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 3 && x 5)
def cs27 : List (List (Fin 14)) := [[0],[2,4],[3,4],[1,5],[3,5]]
lemma d27 (x : Fin 14 → Bool) : f27 x = dnf cs27 x := by
  simp [f27, cs27, dnf]
  <;> ac_rfl
def T27 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup27 (x y : Fin 14 → Bool) (h : ∀ i ∈ T27, x i = y i) : f27 x = f27 y := by
  simp only [f27, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep27 : ∀ p ∈ T27, Base.Readers.Dep f27 p := by
  have hc : ∀ p : Fin 14, p ∈ T27 → f27 (Function.update (wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f27 (wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower27 (s : Nat) (h : HasCircuitSize 14 f27 s) : 6 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f27 1 s
    (dep27 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower26
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,3,4,2,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f27 (Function.update (x ∘ ren) 1 false)) = f26 := by
      funext x
      rw [d27, d26, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f27 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower24
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,2,4,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f27 (Function.update (x ∘ ren) 1 true)) = f24 := by
      funext x
      rw [d27, d24, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f27 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f28 (x : Fin 14 → Bool) : Bool := (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6)
def cs28 : List (List (Fin 14)) := [[2,4],[3,4],[1,5],[3,5],[0,6],[1,6],[2,6]]
lemma d28 (x : Fin 14 → Bool) : f28 x = dnf cs28 x := by
  simp [f28, cs28, dnf]
  <;> ac_rfl
def T28 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup28 (x y : Fin 14 → Bool) (h : ∀ i ∈ T28, x i = y i) : f28 x = f28 y := by
  simp only [f28, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep28 : ∀ p ∈ T28, Base.Readers.Dep f28 p := by
  have hc : ∀ p : Fin 14, p ∈ T28 → f28 (Function.update (wi (([64,32,16,16,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([64,32,16,16,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f28 (wi (([64,32,16,16,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([64,32,16,16,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower28 (s : Nat) (h : HasCircuitSize 14 f28 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f28 0 s
    (dep28 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 20, by decide +kernel⟩
      · exact ⟨wi 0, wi 64, by decide +kernel⟩) h
  cases b
  · have hh := lower25
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,2,1,3,5,4,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f28 (Function.update (x ∘ ren) 0 false)) = f25 := by
      funext x
      rw [d28, d25, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f28 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower27
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,5,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f28 (Function.update (x ∘ ren) 0 true)) = f27 := by
      funext x
      rw [d28, d27, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f28 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f29 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 2 && x 4) || (x 3 && x 4)
def cs29 : List (List (Fin 14)) := [[0],[1],[2,4],[3,4]]
lemma d29 (x : Fin 14 → Bool) : f29 x = dnf cs29 x := by
  simp [f29, cs29, dnf]
  <;> ac_rfl
def T29 : Finset (Fin 14) := {0, 1, 2, 3, 4}
lemma sup29 (x y : Fin 14 → Bool) (h : ∀ i ∈ T29, x i = y i) : f29 x = f29 y := by
  simp only [f29, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
lemma dep29 : ∀ p ∈ T29, Base.Readers.Dep f29 p := by
  have hc : ∀ p : Fin 14, p ∈ T29 → f29 (Function.update (wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f29 (wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,16,16,4,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower29 (s : Nat) (h : HasCircuitSize 14 f29 s) : 3 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f29 T29 dep29 s h
  have ht : T29.card = 5 := by decide +kernel
  omega
def f30 (x : Fin 14 → Bool) : Bool := (x 1 && x 3) || (x 2 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5)
def cs30 : List (List (Fin 14)) := [[1,3],[2,3],[0,4],[2,4],[0,5],[1,5]]
lemma d30 (x : Fin 14 → Bool) : f30 x = dnf cs30 x := by
  simp [f30, cs30, dnf]
  <;> ac_rfl
def T30 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup30 (x y : Fin 14 → Bool) (h : ∀ i ∈ T30, x i = y i) : f30 x = f30 y := by
  simp only [f30, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep30 : ∀ p ∈ T30, Base.Readers.Dep f30 p := by
  have hc : ∀ p : Fin 14, p ∈ T30 → f30 (Function.update (wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f30 (wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower30 (s : Nat) (h : HasCircuitSize 14 f30 s) : 7 ≤ s := by
  have support : ∀ p, Base.Readers.Dep f30 p → p ∈ T30 :=
    fun p hp => dep_mem_support f30 T30 sup30 p hp
  have hnc : Base.Readers.RestrNC f30 := by
    have check : ∀ (p : Fin 14), p ∈ T30 → ∀ b : Bool, f30 (Function.update (wi 0) p b) ≠ f30 (Function.update (wi (([10,16,12,8,10,8,17,2,10,1,10,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (p.val*2 + if b then 1 else 0) 0)) p b) := by decide +kernel
    intro p hp b; exact ⟨wi 0, wi (([10,16,12,8,10,8,17,2,10,1,10,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (p.val*2 + if b then 1 else 0) 0), check p (support p hp) b⟩
  have hnf : Base.Readers.NoFunnel f30 := by
    let w (p q : Fin 14) (a b : Bool) := wi (([0,0,0,0,8,8,8,8,8,8,8,8,2,2,2,2,0,0,0,4,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,8,8,0,0,0,0,16,8,8,8,0,0,0,4,1,1,1,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,8,8,16,8,8,8,0,0,0,0,0,0,0,2,0,0,0,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,0,0,0,4,0,0,0,2,0,0,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,1,1,1,1,0,0,0,1,1,1,1,1,0,0,0,0,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,1,1,1,1,1,1,1,1,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (((p.val*14+q.val)*2 + if a then 1 else 0)*2 + if b then 1 else 0) 0)
    have check : ∀ (p q : Fin 14), p ∈ T30 → q ∈ T30 → p ≠ q → ∀ a b : Bool, ¬ (f30 (Base.Readers.set2 (w p q a b) p (!a) q b) = f30 (Base.Readers.set2 (w p q a b) p a q (!b)) ∧ f30 (Base.Readers.set2 (w p q a b) p a q (!b)) = f30 (Base.Readers.set2 (w p q a b) p (!a) q (!b))) := by decide +kernel
    intro p q hpq hp hq hf
    obtain ⟨a,b,hab⟩ := hf
    exact check p q (support p hp) (support q hq) hpq a b (hab (w p q a b))
  have lo (p : Fin 14) (hp : p ∈ T30) (t : Nat)
      (hc : HasCircuitSize 14 (fun x => f30 (Function.update x p false)) t) : 4 ≤ t := by
    fin_cases p
    · have hh := lower23
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,3,2,1,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 0 false)) = f23 := by
        funext x
        rw [d30, d23, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 0 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower23
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,0,4,0,2,1,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 1 false)) = f23 := by
        funext x
        rw [d30, d23, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 1 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower23
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,4,0,0,1,2,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 2 false)) = f23 := by
        funext x
        rw [d30, d23, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 2 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower23
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,0,1,0,3,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 3 false)) = f23 := by
        funext x
        rw [d30, d23, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 3 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower23
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,3,0,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 4 false)) = f23 := by
        funext x
        rw [d30, d23, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 4 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower23
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 5 false)) = f23 := by
        funext x
        rw [d30, d23, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 5 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
  have hi (p : Fin 14) (hp : p ∈ T30) (t : Nat)
      (hc : HasCircuitSize 14 (fun x => f30 (Function.update x p true)) t) : 3 ≤ t := by
    fin_cases p
    · have hh := lower29
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,1,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 0 true)) = f29 := by
        funext x
        rw [d30, d29, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 0 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower29
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,0,3,0,4,1,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 1 true)) = f29 := by
        funext x
        rw [d30, d29, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 1 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower29
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,3,0,0,1,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 2 true)) = f29 := by
        funext x
        rw [d30, d29, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 2 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower29
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,0,1,0,3,2,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 3 true)) = f29 := by
        funext x
        rw [d30, d29, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 3 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower29
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,1,2,0,3,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 4 true)) = f29 := by
        funext x
        rw [d30, d29, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 4 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower29
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,4,2,3,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f30 (Function.update (x ∘ ren) 5 true)) = f29 := by
        funext x
        rw [d30, d29, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f30 (Function.update (x ∘ ren) 5 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
    · simp [T30] at hp
  obtain ⟨p,hp,hpays⟩ := Base.Readers.fanout_step 13 f30 s ⟨0, dep30 0 (by decide)⟩ hnc hnf h
  rcases hpays with ⟨⟨t,ht,hc⟩,_⟩ | ⟨⟨t,ht,hc⟩,_⟩ | ⟨_,⟨t,ht,hc⟩⟩
  · have := lo p (support p hp) t hc; omega
  · have := lo p (support p hp) t hc; omega
  · have := hi p (support p hp) t hc; omega
def f31 (x : Fin 14 → Bool) : Bool := x 0 || (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6)
def cs31 : List (List (Fin 14)) := [[0],[2,4],[3,4],[1,5],[3,5],[1,6],[2,6]]
lemma d31 (x : Fin 14 → Bool) : f31 x = dnf cs31 x := by
  simp [f31, cs31, dnf]
  <;> ac_rfl
def T31 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup31 (x y : Fin 14 → Bool) (h : ∀ i ∈ T31, x i = y i) : f31 x = f31 y := by
  simp only [f31, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep31 : ∀ p ∈ T31, Base.Readers.Dep f31 p := by
  have hc : ∀ p : Fin 14, p ∈ T31 → f31 (Function.update (wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f31 (wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower31 (s : Nat) (h : HasCircuitSize 14 f31 s) : 8 ≤ s := by
  by_contra hn
  have hs : s ≤ 7 := by omega
  have hbig : HasCircuitSize 14 f31 (6+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f31 0 false 6
    (dep31 0 (by decide)) ⟨wi 0, wi 20, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f31 (Function.update (x ∘ ren) 0 false)) = f30 := by
    funext x
    rw [d31, d30, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f31 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower30 6 hc
  omega
def f32 (x : Fin 14 → Bool) : Bool := (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 6 && x 7)
def cs32 : List (List (Fin 14)) := [[2,4],[3,4],[1,5],[3,5],[0,6],[1,7],[2,7],[6,7]]
lemma d32 (x : Fin 14 → Bool) : f32 x = dnf cs32 x := by
  simp [f32, cs32, dnf]
  <;> ac_rfl
def T32 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup32 (x y : Fin 14 → Bool) (h : ∀ i ∈ T32, x i = y i) : f32 x = f32 y := by
  simp only [f32, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep32 : ∀ p ∈ T32, Base.Readers.Dep f32 p := by
  have hc : ∀ p : Fin 14, p ∈ T32 → f32 (Function.update (wi (([64,32,16,16,4,2,1,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([64,32,16,16,4,2,1,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f32 (wi (([64,32,16,16,4,2,1,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([64,32,16,16,4,2,1,2,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower32 (s : Nat) (h : HasCircuitSize 14 f32 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f32 0 s
    (dep32 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 20, by decide +kernel⟩
      · exact ⟨wi 0, wi 64, by decide +kernel⟩) h
  cases b
  · have hh := lower28
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,5,0,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f32 (Function.update (x ∘ ren) 0 false)) = f28 := by
      funext x
      rw [d32, d28, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f32 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower31
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,2,4,6,0,5,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f32 (Function.update (x ∘ ren) 0 true)) = f31 := by
      funext x
      rw [d32, d31, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f32 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f33 (x : Fin 14 → Bool) : Bool := (x 1 && x 2) || (x 0 && x 3) || (x 2 && x 3)
def cs33 : List (List (Fin 14)) := [[1,2],[0,3],[2,3]]
lemma d33 (x : Fin 14 → Bool) : f33 x = dnf cs33 x := by
  simp [f33, cs33, dnf]
  <;> ac_rfl
def T33 : Finset (Fin 14) := {0, 1, 2, 3}
lemma sup33 (x y : Fin 14 → Bool) (h : ∀ i ∈ T33, x i = y i) : f33 x = f33 y := by
  simp only [f33, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
lemma dep33 : ∀ p ∈ T33, Base.Readers.Dep f33 p := by
  have hc : ∀ p : Fin 14, p ∈ T33 → f33 (Function.update (wi (([8,4,2,1,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([8,4,2,1,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f33 (wi (([8,4,2,1,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([8,4,2,1,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower33 (s : Nat) (h : HasCircuitSize 14 f33 s) : 3 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f33 T33 dep33 s h
  have ht : T33.card = 4 := by decide +kernel
  omega
def f34 (x : Fin 14 → Bool) : Bool := x 0 || (x 1 && x 3) || (x 2 && x 3)
def cs34 : List (List (Fin 14)) := [[0],[1,3],[2,3]]
lemma d34 (x : Fin 14 → Bool) : f34 x = dnf cs34 x := by
  simp [f34, cs34, dnf]
  <;> ac_rfl
def T34 : Finset (Fin 14) := {0, 1, 2, 3}
lemma sup34 (x y : Fin 14 → Bool) (h : ∀ i ∈ T34, x i = y i) : f34 x = f34 y := by
  simp only [f34, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
lemma dep34 : ∀ p ∈ T34, Base.Readers.Dep f34 p := by
  have hc : ∀ p : Fin 14, p ∈ T34 → f34 (Function.update (wi (([0,8,8,2,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,8,8,2,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f34 (wi (([0,8,8,2,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,8,8,2,0,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower34 (s : Nat) (h : HasCircuitSize 14 f34 s) : 3 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f34 T34 dep34 s h
  have ht : T34.card = 4 := by decide +kernel
  omega
def f35 (x : Fin 14 → Bool) : Bool := (x 1 && x 3) || (x 2 && x 3) || (x 0 && x 4) || (x 2 && x 4)
def cs35 : List (List (Fin 14)) := [[1,3],[2,3],[0,4],[2,4]]
lemma d35 (x : Fin 14 → Bool) : f35 x = dnf cs35 x := by
  simp [f35, cs35, dnf]
  <;> ac_rfl
def T35 : Finset (Fin 14) := {0, 1, 2, 3, 4}
lemma sup35 (x y : Fin 14 → Bool) (h : ∀ i ∈ T35, x i = y i) : f35 x = f35 y := by
  simp only [f35, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
lemma dep35 : ∀ p ∈ T35, Base.Readers.Dep f35 p := by
  have hc : ∀ p : Fin 14, p ∈ T35 → f35 (Function.update (wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f35 (wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([16,8,8,2,1,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower35 (s : Nat) (h : HasCircuitSize 14 f35 s) : 5 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f35 0 s
    (dep35 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 10, by decide +kernel⟩
      · exact ⟨wi 0, wi 16, by decide +kernel⟩) h
  cases b
  · have hh := lower33
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,2,0,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f35 (Function.update (x ∘ ren) 0 false)) = f33 := by
      funext x
      rw [d35, d33, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f35 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower34
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,3,0,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f35 (Function.update (x ∘ ren) 0 true)) = f34 := by
      funext x
      rw [d35, d34, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f35 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f36 (x : Fin 14 → Bool) : Bool := (x 1 && x 3) || (x 2 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5)
def cs36 : List (List (Fin 14)) := [[1,3],[2,3],[0,4],[2,4],[0,5],[1,5]]
lemma d36 (x : Fin 14 → Bool) : f36 x = dnf cs36 x := by
  simp [f36, cs36, dnf]
  <;> ac_rfl
def T36 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup36 (x y : Fin 14 → Bool) (h : ∀ i ∈ T36, x i = y i) : f36 x = f36 y := by
  simp only [f36, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep36 : ∀ p ∈ T36, Base.Readers.Dep f36 p := by
  have hc : ∀ p : Fin 14, p ∈ T36 → f36 (Function.update (wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f36 (wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([16,8,8,2,1,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower36 (s : Nat) (h : HasCircuitSize 14 f36 s) : 8 ≤ s := by
  have support : ∀ p, Base.Readers.Dep f36 p → p ∈ T36 :=
    fun p hp => dep_mem_support f36 T36 sup36 p hp
  have hnc : Base.Readers.RestrNC f36 := by
    have check : ∀ (p : Fin 14), p ∈ T36 → ∀ b : Bool, f36 (Function.update (wi 0) p b) ≠ f36 (Function.update (wi (([10,16,12,8,10,8,17,2,10,1,10,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (p.val*2 + if b then 1 else 0) 0)) p b) := by decide +kernel
    intro p hp b; exact ⟨wi 0, wi (([10,16,12,8,10,8,17,2,10,1,10,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (p.val*2 + if b then 1 else 0) 0), check p (support p hp) b⟩
  have hnf : Base.Readers.NoFunnel f36 := by
    let w (p q : Fin 14) (a b : Bool) := wi (([0,0,0,0,8,8,8,8,8,8,8,8,2,2,2,2,0,0,0,4,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,8,8,0,0,0,0,16,8,8,8,0,0,0,4,1,1,1,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,8,8,16,8,8,8,0,0,0,0,0,0,0,2,0,0,0,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,0,0,0,4,0,0,0,2,0,0,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,1,1,1,1,0,0,0,1,1,1,1,1,0,0,0,0,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,1,1,1,1,1,1,1,1,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (((p.val*14+q.val)*2 + if a then 1 else 0)*2 + if b then 1 else 0) 0)
    have check : ∀ (p q : Fin 14), p ∈ T36 → q ∈ T36 → p ≠ q → ∀ a b : Bool, ¬ (f36 (Base.Readers.set2 (w p q a b) p (!a) q b) = f36 (Base.Readers.set2 (w p q a b) p a q (!b)) ∧ f36 (Base.Readers.set2 (w p q a b) p a q (!b)) = f36 (Base.Readers.set2 (w p q a b) p (!a) q (!b))) := by decide +kernel
    intro p q hpq hp hq hf
    obtain ⟨a,b,hab⟩ := hf
    exact check p q (support p hp) (support q hq) hpq a b (hab (w p q a b))
  have lo (p : Fin 14) (hp : p ∈ T36) (t : Nat)
      (hc : HasCircuitSize 14 (fun x => f36 (Function.update x p false)) t) : 5 ≤ t := by
    fin_cases p
    · have hh := lower35
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,3,2,1,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 0 false)) = f35 := by
        funext x
        rw [d36, d35, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 0 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower35
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,0,4,0,2,1,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 1 false)) = f35 := by
        funext x
        rw [d36, d35, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 1 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower35
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,4,0,0,1,2,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 2 false)) = f35 := by
        funext x
        rw [d36, d35, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 2 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower35
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,0,1,0,3,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 3 false)) = f35 := by
        funext x
        rw [d36, d35, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 3 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower35
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,3,0,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 4 false)) = f35 := by
        funext x
        rw [d36, d35, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 4 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower35
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 5 false)) = f35 := by
        funext x
        rw [d36, d35, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 5 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
  have hi (p : Fin 14) (hp : p ∈ T36) (t : Nat)
      (hc : HasCircuitSize 14 (fun x => f36 (Function.update x p true)) t) : 4 ≤ t := by
    fin_cases p
    · have hh := lower24
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,1,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 0 true)) = f24 := by
        funext x
        rw [d36, d24, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 0 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower24
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,0,3,0,4,1,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 1 true)) = f24 := by
        funext x
        rw [d36, d24, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 1 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower24
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,3,0,0,1,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 2 true)) = f24 := by
        funext x
        rw [d36, d24, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 2 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower24
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,0,1,0,3,2,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 3 true)) = f24 := by
        funext x
        rw [d36, d24, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 3 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower24
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,1,2,0,3,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 4 true)) = f24 := by
        funext x
        rw [d36, d24, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 4 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower24
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,4,2,3,0,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f36 (Function.update (x ∘ ren) 5 true)) = f24 := by
        funext x
        rw [d36, d24, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f36 (Function.update (x ∘ ren) 5 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
    · simp [T36] at hp
  obtain ⟨p,hp,hpays⟩ := Base.Readers.fanout_step 13 f36 s ⟨0, dep36 0 (by decide)⟩ hnc hnf h
  rcases hpays with ⟨⟨t,ht,hc⟩,_⟩ | ⟨⟨t,ht,hc⟩,_⟩ | ⟨_,⟨t,ht,hc⟩⟩
  · have := lo p (support p hp) t hc; omega
  · have := lo p (support p hp) t hc; omega
  · have := hi p (support p hp) t hc; omega
def f37 (x : Fin 14 → Bool) : Bool := x 0 || (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6)
def cs37 : List (List (Fin 14)) := [[0],[2,4],[3,4],[1,5],[3,5],[1,6],[2,6]]
lemma d37 (x : Fin 14 → Bool) : f37 x = dnf cs37 x := by
  simp [f37, cs37, dnf]
  <;> ac_rfl
def T37 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup37 (x y : Fin 14 → Bool) (h : ∀ i ∈ T37, x i = y i) : f37 x = f37 y := by
  simp only [f37, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep37 : ∀ p ∈ T37, Base.Readers.Dep f37 p := by
  have hc : ∀ p : Fin 14, p ∈ T37 → f37 (Function.update (wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f37 (wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,32,16,16,4,2,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower37 (s : Nat) (h : HasCircuitSize 14 f37 s) : 9 ≤ s := by
  by_contra hn
  have hs : s ≤ 8 := by omega
  have hbig : HasCircuitSize 14 f37 (7+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f37 0 false 7
    (dep37 0 (by decide)) ⟨wi 0, wi 20, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f37 (Function.update (x ∘ ren) 0 false)) = f36 := by
    funext x
    rw [d37, d36, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f37 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower36 7 hc
  omega
def f38 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7)
def cs38 : List (List (Fin 14)) := [[0],[3,5],[4,5],[2,6],[4,6],[1,7],[2,7],[3,7]]
lemma d38 (x : Fin 14 → Bool) : f38 x = dnf cs38 x := by
  simp [f38, cs38, dnf]
  <;> ac_rfl
def T38 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup38 (x y : Fin 14 → Bool) (h : ∀ i ∈ T38, x i = y i) : f38 x = f38 y := by
  simp only [f38, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep38 : ∀ p ∈ T38, Base.Readers.Dep f38 p := by
  have hc : ∀ p : Fin 14, p ∈ T38 → f38 (Function.update (wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f38 (wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower38 (s : Nat) (h : HasCircuitSize 14 f38 s) : 10 ≤ s := by
  by_contra hn
  have hs : s ≤ 9 := by omega
  have hbig : HasCircuitSize 14 f38 (8+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f38 1 false 8
    (dep38 1 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,3,2,4,6,5,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f38 (Function.update (x ∘ ren) 1 false)) = f37 := by
    funext x
    rw [d38, d37, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f38 (Function.update (x ∘ ren) 1 false)) _ at hc
  rw [he] at hc
  have := lower37 8 hc
  omega
def f39 (x : Fin 14 → Bool) : Bool := (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8)
def cs39 : List (List (Fin 14)) := [[3,5],[4,5],[2,6],[4,6],[0,7],[1,7],[1,8],[2,8],[3,8]]
lemma d39 (x : Fin 14 → Bool) : f39 x = dnf cs39 x := by
  simp [f39, cs39, dnf]
  <;> ac_rfl
def T39 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup39 (x y : Fin 14 → Bool) (h : ∀ i ∈ T39, x i = y i) : f39 x = f39 y := by
  simp only [f39, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep39 : ∀ p ∈ T39, Base.Readers.Dep f39 p := by
  have hc : ∀ p : Fin 14, p ∈ T39 → f39 (Function.update (wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f39 (wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower39 (s : Nat) (h : HasCircuitSize 14 f39 s) : 12 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f39 0 s
    (dep39 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 40, by decide +kernel⟩
      · exact ⟨wi 0, wi 128, by decide +kernel⟩) h
  cases b
  · have hh := lower32
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,6,1,2,3,4,5,0,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f39 (Function.update (x ∘ ren) 0 false)) = f32 := by
      funext x
      rw [d39, d32, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f39 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower38
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,5,6,0,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f39 (Function.update (x ∘ ren) 0 true)) = f38 := by
      funext x
      rw [d39, d38, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f39 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f40 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 4 && x 9)
def cs40 : List (List (Fin 14)) := [[0],[4,6],[5,6],[3,7],[5,7],[1,8],[2,8],[2,9],[3,9],[4,9]]
lemma d40 (x : Fin 14 → Bool) : f40 x = dnf cs40 x := by
  simp [f40, cs40, dnf]
  <;> ac_rfl
def T40 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup40 (x y : Fin 14 → Bool) (h : ∀ i ∈ T40, x i = y i) : f40 x = f40 y := by
  simp only [f40, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep40 : ∀ p ∈ T40, Base.Readers.Dep f40 p := by
  have hc : ∀ p : Fin 14, p ∈ T40 → f40 (Function.update (wi (([0,256,256,128,64,64,16,8,2,4,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,256,256,128,64,64,16,8,2,4,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f40 (wi (([0,256,256,128,64,64,16,8,2,4,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,256,256,128,64,64,16,8,2,4,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower40 (s : Nat) (h : HasCircuitSize 14 f40 s) : 13 ≤ s := by
  by_contra hn
  have hs : s ≤ 12 := by omega
  have hbig : HasCircuitSize 14 f40 (11+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f40 0 false 11
    (dep40 0 (by decide)) ⟨wi 0, wi 80, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f40 (Function.update (x ∘ ren) 0 false)) = f39 := by
    funext x
    rw [d40, d39, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f40 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower39 11 hc
  omega
def f41 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 7) || (x 6 && x 7) || (x 4 && x 8) || (x 6 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 3 && x 10) || (x 4 && x 10) || (x 5 && x 10)
def cs41 : List (List (Fin 14)) := [[0],[1],[5,7],[6,7],[4,8],[6,8],[2,9],[3,9],[3,10],[4,10],[5,10]]
lemma d41 (x : Fin 14 → Bool) : f41 x = dnf cs41 x := by
  simp [f41, cs41, dnf]
  <;> ac_rfl
def T41 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup41 (x y : Fin 14 → Bool) (h : ∀ i ∈ T41, x i = y i) : f41 x = f41 y := by
  simp only [f41, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep41 : ∀ p ∈ T41, Base.Readers.Dep f41 p := by
  have hc : ∀ p : Fin 14, p ∈ T41 → f41 (Function.update (wi (([0,0,512,512,256,128,128,32,16,4,8,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,512,512,256,128,128,32,16,4,8,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f41 (wi (([0,0,512,512,256,128,128,32,16,4,8,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,512,512,256,128,128,32,16,4,8,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower41 (s : Nat) (h : HasCircuitSize 14 f41 s) : 14 ≤ s := by
  by_contra hn
  have hs : s ≤ 13 := by omega
  have hbig : HasCircuitSize 14 f41 (12+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f41 0 false 12
    (dep41 0 (by decide)) ⟨wi 0, wi 2, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f41 (Function.update (x ∘ ren) 0 false)) = f40 := by
    funext x
    rw [d41, d40, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f41 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower40 12 hc
  omega
def f42 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 6 && x 8) || (x 7 && x 8) || (x 5 && x 9) || (x 7 && x 9) || (x 3 && x 10) || (x 4 && x 10) || (x 4 && x 11) || (x 5 && x 11) || (x 6 && x 11)
def cs42 : List (List (Fin 14)) := [[0],[1],[2],[6,8],[7,8],[5,9],[7,9],[3,10],[4,10],[4,11],[5,11],[6,11]]
lemma d42 (x : Fin 14 → Bool) : f42 x = dnf cs42 x := by
  simp [f42, cs42, dnf]
  <;> ac_rfl
def T42 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup42 (x y : Fin 14 → Bool) (h : ∀ i ∈ T42, x i = y i) : f42 x = f42 y := by
  simp only [f42, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep42 : ∀ p ∈ T42, Base.Readers.Dep f42 p := by
  have hc : ∀ p : Fin 14, p ∈ T42 → f42 (Function.update (wi (([0,0,0,1024,1024,512,256,256,64,32,8,16,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,1024,1024,512,256,256,64,32,8,16,0,0] : List Nat).getD p.val 0)) p)) ≠ f42 (wi (([0,0,0,1024,1024,512,256,256,64,32,8,16,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,1024,1024,512,256,256,64,32,8,16,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower42 (s : Nat) (h : HasCircuitSize 14 f42 s) : 15 ≤ s := by
  by_contra hn
  have hs : s ≤ 14 := by omega
  have hbig : HasCircuitSize 14 f42 (13+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f42 0 false 13
    (dep42 0 (by decide)) ⟨wi 0, wi 2, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,9,10,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f42 (Function.update (x ∘ ren) 0 false)) = f41 := by
    funext x
    rw [d42, d41, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f42 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower41 13 hc
  omega
def f43 (x : Fin 14 → Bool) : Bool := (x 3 && x 4) || (x 4 && x 7) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 2 && x 9) || (x 6 && x 9) || (x 7 && x 9) || (x 1 && x 10) || (x 5 && x 10) || (x 7 && x 10) || (x 0 && x 11) || (x 2 && x 11) || (x 5 && x 11) || (x 0 && x 12) || (x 1 && x 12) || (x 6 && x 12)
def cs43 : List (List (Fin 14)) := [[3,4],[4,7],[3,8],[5,8],[6,8],[2,9],[6,9],[7,9],[1,10],[5,10],[7,10],[0,11],[2,11],[5,11],[0,12],[1,12],[6,12]]
lemma d43 (x : Fin 14 → Bool) : f43 x = dnf cs43 x := by
  simp [f43, cs43, dnf]
  <;> ac_rfl
def T43 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup43 (x y : Fin 14 → Bool) (h : ∀ i ∈ T43, x i = y i) : f43 x = f43 y := by
  simp only [f43, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep43 : ∀ p ∈ T43, Base.Readers.Dep f43 p := by
  have hc : ∀ p : Fin 14, p ∈ T43 → f43 (Function.update (wi (([2048,1024,512,16,8,256,256,16,8,4,2,1,1,0] : List Nat).getD p.val 0)) p (!(wi (([2048,1024,512,16,8,256,256,16,8,4,2,1,1,0] : List Nat).getD p.val 0)) p)) ≠ f43 (wi (([2048,1024,512,16,8,256,256,16,8,4,2,1,1,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([2048,1024,512,16,8,256,256,16,8,4,2,1,1,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower43 (s : Nat) (h : HasCircuitSize 14 f43 s) : 17 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f43 10 s
    (dep43 10 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 24, by decide +kernel⟩
      · exact ⟨wi 0, wi 2, by decide +kernel⟩) h
  cases b
  · have hh := lower22
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,5,6,3,7,4,8,9,0,10,11,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f43 (Function.update (x ∘ ren) 10 false)) = f22 := by
      funext x
      rw [d43, d22, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f43 (Function.update (x ∘ ren) 10 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower42
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([8,0,9,10,3,1,11,2,4,5,0,7,6,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f43 (Function.update (x ∘ ren) 10 true)) = f42 := by
      funext x
      rw [d43, d42, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f43 (Function.update (x ∘ ren) 10 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f44 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 3 && x 4)
def cs44 : List (List (Fin 14)) := [[0],[1],[2],[3,4]]
lemma d44 (x : Fin 14 → Bool) : f44 x = dnf cs44 x := by
  simp [f44, cs44, dnf]
  <;> ac_rfl
def T44 : Finset (Fin 14) := {0, 1, 2, 3, 4}
lemma sup44 (x y : Fin 14 → Bool) (h : ∀ i ∈ T44, x i = y i) : f44 x = f44 y := by
  simp only [f44, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
lemma dep44 : ∀ p ∈ T44, Base.Readers.Dep f44 p := by
  have hc : ∀ p : Fin 14, p ∈ T44 → f44 (Function.update (wi (([0,0,0,16,8,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,16,8,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f44 (wi (([0,0,0,16,8,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,16,8,0,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower44 (s : Nat) (h : HasCircuitSize 14 f44 s) : 4 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f44 T44 dep44 s h
  have ht : T44.card = 5 := by decide +kernel
  omega
def f45 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 5)
def cs45 : List (List (Fin 14)) := [[0],[1],[3,4],[2,5],[4,5]]
lemma d45 (x : Fin 14 → Bool) : f45 x = dnf cs45 x := by
  simp [f45, cs45, dnf]
  <;> ac_rfl
def T45 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup45 (x y : Fin 14 → Bool) (h : ∀ i ∈ T45, x i = y i) : f45 x = f45 y := by
  simp only [f45, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep45 : ∀ p ∈ T45, Base.Readers.Dep f45 p := by
  have hc : ∀ p : Fin 14, p ∈ T45 → f45 (Function.update (wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f45 (wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower45 (s : Nat) (h : HasCircuitSize 14 f45 s) : 6 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f45 2 s
    (dep45 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower24
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,2,4,3,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f45 (Function.update (x ∘ ren) 2 false)) = f24 := by
      funext x
      rw [d45, d24, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f45 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower44
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,4,3,2,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f45 (Function.update (x ∘ ren) 2 true)) = f44 := by
      funext x
      rw [d45, d44, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f45 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f46 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 3 && x 6)
def cs46 : List (List (Fin 14)) := [[0],[3,4],[2,5],[4,5],[1,6],[3,6]]
lemma d46 (x : Fin 14 → Bool) : f46 x = dnf cs46 x := by
  simp [f46, cs46, dnf]
  <;> ac_rfl
def T46 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup46 (x y : Fin 14 → Bool) (h : ∀ i ∈ T46, x i = y i) : f46 x = f46 y := by
  simp only [f46, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep46 : ∀ p ∈ T46, Base.Readers.Dep f46 p := by
  have hc : ∀ p : Fin 14, p ∈ T46 → f46 (Function.update (wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f46 (wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower46 (s : Nat) (h : HasCircuitSize 14 f46 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f46 1 s
    (dep46 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower27
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,4,3,5,2,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f46 (Function.update (x ∘ ren) 1 false)) = f27 := by
      funext x
      rw [d46, d27, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f46 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower45
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,2,5,4,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f46 (Function.update (x ∘ ren) 1 true)) = f45 := by
      funext x
      rw [d46, d45, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f46 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f47 (x : Fin 14 → Bool) : Bool := (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 6 && x 7)
def cs47 : List (List (Fin 14)) := [[3,4],[2,5],[4,5],[1,6],[3,6],[0,7],[2,7],[6,7]]
lemma d47 (x : Fin 14 → Bool) : f47 x = dnf cs47 x := by
  simp [f47, cs47, dnf]
  <;> ac_rfl
def T47 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup47 (x y : Fin 14 → Bool) (h : ∀ i ∈ T47, x i = y i) : f47 x = f47 y := by
  simp only [f47, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep47 : ∀ p ∈ T47, Base.Readers.Dep f47 p := by
  have hc : ∀ p : Fin 14, p ∈ T47 → f47 (Function.update (wi (([128,64,32,16,8,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([128,64,32,16,8,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f47 (wi (([128,64,32,16,8,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([128,64,32,16,8,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower47 (s : Nat) (h : HasCircuitSize 14 f47 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f47 0 s
    (dep47 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 24, by decide +kernel⟩
      · exact ⟨wi 0, wi 128, by decide +kernel⟩) h
  cases b
  · have hh := lower28
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,5,2,4,3,6,1,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f47 (Function.update (x ∘ ren) 0 false)) = f28 := by
      funext x
      rw [d47, d28, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f47 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower46
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,4,3,6,5,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f47 (Function.update (x ∘ ren) 0 true)) = f46 := by
      funext x
      rw [d47, d46, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f47 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f48 (x : Fin 14 → Bool) : Bool := (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 3 && x 7) || (x 6 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 7 && x 8)
def cs48 : List (List (Fin 14)) := [[3,4],[2,5],[4,5],[1,6],[3,7],[6,7],[0,8],[2,8],[7,8]]
lemma d48 (x : Fin 14 → Bool) : f48 x = dnf cs48 x := by
  simp [f48, cs48, dnf]
  <;> ac_rfl
def T48 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup48 (x y : Fin 14 → Bool) (h : ∀ i ∈ T48, x i = y i) : f48 x = f48 y := by
  simp only [f48, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep48 : ∀ p ∈ T48, Base.Readers.Dep f48 p := by
  have hc : ∀ p : Fin 14, p ∈ T48 → f48 (Function.update (wi (([256,64,32,16,8,4,2,8,1,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([256,64,32,16,8,4,2,8,1,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f48 (wi (([256,64,32,16,8,4,2,8,1,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([256,64,32,16,8,4,2,8,1,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower48 (s : Nat) (h : HasCircuitSize 14 f48 s) : 12 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f48 1 s
    (dep48 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 24, by decide +kernel⟩
      · exact ⟨wi 0, wi 64, by decide +kernel⟩) h
  cases b
  · have hh := lower47
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,2,5,4,0,7,6,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f48 (Function.update (x ∘ ren) 1 false)) = f47 := by
      funext x
      rw [d48, d47, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f48 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower38
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,6,4,5,0,2,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f48 (Function.update (x ∘ ren) 1 true)) = f38 := by
      funext x
      rw [d48, d38, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f48 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f49 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 4 && x 8) || (x 7 && x 8) || (x 1 && x 9) || (x 3 && x 9) || (x 8 && x 9)
def cs49 : List (List (Fin 14)) := [[0],[4,5],[3,6],[5,6],[2,7],[4,8],[7,8],[1,9],[3,9],[8,9]]
lemma d49 (x : Fin 14 → Bool) : f49 x = dnf cs49 x := by
  simp [f49, cs49, dnf]
  <;> ac_rfl
def T49 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup49 (x y : Fin 14 → Bool) (h : ∀ i ∈ T49, x i = y i) : f49 x = f49 y := by
  simp only [f49, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep49 : ∀ p ∈ T49, Base.Readers.Dep f49 p := by
  have hc : ∀ p : Fin 14, p ∈ T49 → f49 (Function.update (wi (([0,512,128,64,32,16,8,4,16,2,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,512,128,64,32,16,8,4,16,2,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f49 (wi (([0,512,128,64,32,16,8,4,16,2,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,512,128,64,32,16,8,4,16,2,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower49 (s : Nat) (h : HasCircuitSize 14 f49 s) : 13 ≤ s := by
  by_contra hn
  have hs : s ≤ 12 := by omega
  have hbig : HasCircuitSize 14 f49 (11+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f49 0 false 11
    (dep49 0 (by decide)) ⟨wi 0, wi 48, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f49 (Function.update (x ∘ ren) 0 false)) = f48 := by
    funext x
    rw [d49, d48, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f49 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower48 11 hc
  omega
def f50 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 6) || (x 4 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 5 && x 9) || (x 8 && x 9) || (x 2 && x 10) || (x 4 && x 10) || (x 9 && x 10)
def cs50 : List (List (Fin 14)) := [[0],[1],[5,6],[4,7],[6,7],[3,8],[5,9],[8,9],[2,10],[4,10],[9,10]]
lemma d50 (x : Fin 14 → Bool) : f50 x = dnf cs50 x := by
  simp [f50, cs50, dnf]
  <;> ac_rfl
def T50 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup50 (x y : Fin 14 → Bool) (h : ∀ i ∈ T50, x i = y i) : f50 x = f50 y := by
  simp only [f50, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep50 : ∀ p ∈ T50, Base.Readers.Dep f50 p := by
  have hc : ∀ p : Fin 14, p ∈ T50 → f50 (Function.update (wi (([0,0,1024,256,128,64,32,16,8,32,4,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,1024,256,128,64,32,16,8,32,4,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f50 (wi (([0,0,1024,256,128,64,32,16,8,32,4,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,1024,256,128,64,32,16,8,32,4,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower50 (s : Nat) (h : HasCircuitSize 14 f50 s) : 14 ≤ s := by
  by_contra hn
  have hs : s ≤ 13 := by omega
  have hbig : HasCircuitSize 14 f50 (12+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f50 0 false 12
    (dep50 0 (by decide)) ⟨wi 0, wi 2, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f50 (Function.update (x ∘ ren) 0 false)) = f49 := by
    funext x
    rw [d50, d49, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f50 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower49 12 hc
  omega
def f51 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 4 && x 9) || (x 6 && x 9) || (x 3 && x 10) || (x 5 && x 10) || (x 2 && x 11) || (x 9 && x 11) || (x 10 && x 11)
def cs51 : List (List (Fin 14)) := [[0],[1],[5,7],[6,7],[3,8],[4,8],[4,9],[6,9],[3,10],[5,10],[2,11],[9,11],[10,11]]
lemma d51 (x : Fin 14 → Bool) : f51 x = dnf cs51 x := by
  simp [f51, cs51, dnf]
  <;> ac_rfl
def T51 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup51 (x y : Fin 14 → Bool) (h : ∀ i ∈ T51, x i = y i) : f51 x = f51 y := by
  simp only [f51, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep51 : ∀ p ∈ T51, Base.Readers.Dep f51 p := by
  have hc : ∀ p : Fin 14, p ∈ T51 → f51 (Function.update (wi (([0,0,2048,256,256,128,128,32,8,16,8,4,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,2048,256,256,128,128,32,8,16,8,4,0,0] : List Nat).getD p.val 0)) p)) ≠ f51 (wi (([0,0,2048,256,256,128,128,32,8,16,8,4,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,2048,256,256,128,128,32,8,16,8,4,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower51 (s : Nat) (h : HasCircuitSize 14 f51 s) : 15 ≤ s := by
  by_contra hn
  have hs : s ≤ 14 := by omega
  have hbig : HasCircuitSize 14 f51 (13+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f51 3 false 13
    (dep51 3 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,8,7,5,6,3,9,4,10,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f51 (Function.update (x ∘ ren) 3 false)) = f50 := by
    funext x
    rw [d51, d50, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f51 (Function.update (x ∘ ren) 3 false)) _ at hc
  rw [he] at hc
  have := lower50 13 hc
  omega
def f52 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 6 && x 7) || (x 4 && x 8) || (x 5 && x 8) || (x 7 && x 9) || (x 3 && x 10) || (x 5 && x 10) || (x 9 && x 10) || (x 2 && x 11) || (x 4 && x 11) || (x 9 && x 11) || (x 2 && x 12) || (x 3 && x 12) || (x 6 && x 12)
def cs52 : List (List (Fin 14)) := [[0],[1],[6,7],[4,8],[5,8],[7,9],[3,10],[5,10],[9,10],[2,11],[4,11],[9,11],[2,12],[3,12],[6,12]]
lemma d52 (x : Fin 14 → Bool) : f52 x = dnf cs52 x := by
  simp [f52, cs52, dnf]
  <;> ac_rfl
def T52 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup52 (x y : Fin 14 → Bool) (h : ∀ i ∈ T52, x i = y i) : f52 x = f52 y := by
  simp only [f52, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep52 : ∀ p ∈ T52, Base.Readers.Dep f52 p := by
  have hc : ∀ p : Fin 14, p ∈ T52 → f52 (Function.update (wi (([0,0,2048,1024,256,256,128,64,16,128,8,4,4,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,2048,1024,256,256,128,64,16,128,8,4,4,0] : List Nat).getD p.val 0)) p)) ≠ f52 (wi (([0,0,2048,1024,256,256,128,64,16,128,8,4,4,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,2048,1024,256,256,128,64,16,128,8,4,4,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower52 (s : Nat) (h : HasCircuitSize 14 f52 s) : 16 ≤ s := by
  by_contra hn
  have hs : s ≤ 15 := by omega
  have hbig : HasCircuitSize 14 f52 (14+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f52 6 false 14
    (dep52 6 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,4,5,6,0,2,7,11,9,10,8,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f52 (Function.update (x ∘ ren) 6 false)) = f51 := by
    funext x
    rw [d52, d51, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f52 (Function.update (x ∘ ren) 6 false)) _ at hc
  rw [he] at hc
  have := lower51 14 hc
  omega
def f53 (x : Fin 14 → Bool) : Bool := (x 2 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5)
def cs53 : List (List (Fin 14)) := [[2,4],[3,4],[0,5],[1,5],[3,5]]
lemma d53 (x : Fin 14 → Bool) : f53 x = dnf cs53 x := by
  simp [f53, cs53, dnf]
  <;> ac_rfl
def T53 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup53 (x y : Fin 14 → Bool) (h : ∀ i ∈ T53, x i = y i) : f53 x = f53 y := by
  simp only [f53, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep53 : ∀ p ∈ T53, Base.Readers.Dep f53 p := by
  have hc : ∀ p : Fin 14, p ∈ T53 → f53 (Function.update (wi (([32,32,16,16,4,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([32,32,16,16,4,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f53 (wi (([32,32,16,16,4,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([32,32,16,16,4,1,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower53 (s : Nat) (h : HasCircuitSize 14 f53 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f53 T53 dep53 s h
  have ht : T53.card = 6 := by decide +kernel
  omega
def f54 (x : Fin 14 → Bool) : Bool := x 0 || (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 3 && x 5)
def cs54 : List (List (Fin 14)) := [[0],[2,4],[3,4],[1,5],[3,5]]
lemma d54 (x : Fin 14 → Bool) : f54 x = dnf cs54 x := by
  simp [f54, cs54, dnf]
  <;> ac_rfl
def T54 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup54 (x y : Fin 14 → Bool) (h : ∀ i ∈ T54, x i = y i) : f54 x = f54 y := by
  simp only [f54, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep54 : ∀ p ∈ T54, Base.Readers.Dep f54 p := by
  have hc : ∀ p : Fin 14, p ∈ T54 → f54 (Function.update (wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f54 (wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,32,16,16,4,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower54 (s : Nat) (h : HasCircuitSize 14 f54 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f54 T54 dep54 s h
  have ht : T54.card = 6 := by decide +kernel
  omega
def f55 (x : Fin 14 → Bool) : Bool := (x 2 && x 4) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6)
def cs55 : List (List (Fin 14)) := [[2,4],[1,5],[3,5],[0,6],[3,6],[4,6]]
lemma d55 (x : Fin 14 → Bool) : f55 x = dnf cs55 x := by
  simp [f55, cs55, dnf]
  <;> ac_rfl
def T55 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup55 (x y : Fin 14 → Bool) (h : ∀ i ∈ T55, x i = y i) : f55 x = f55 y := by
  simp only [f55, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep55 : ∀ p ∈ T55, Base.Readers.Dep f55 p := by
  have hc : ∀ p : Fin 14, p ∈ T55 → f55 (Function.update (wi (([64,32,16,32,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([64,32,16,32,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f55 (wi (([64,32,16,32,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([64,32,16,32,4,2,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower55 (s : Nat) (h : HasCircuitSize 14 f55 s) : 7 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f55 2 s
    (dep55 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 34, by decide +kernel⟩
      · exact ⟨wi 0, wi 16, by decide +kernel⟩) h
  cases b
  · have hh := lower53
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,0,3,1,4,5,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f55 (Function.update (x ∘ ren) 2 false)) = f53 := by
      funext x
      rw [d55, d53, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f55 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower54
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,1,0,3,0,5,4,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f55 (Function.update (x ∘ ren) 2 true)) = f54 := by
      funext x
      rw [d55, d54, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f55 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f56 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 4 && x 5)
def cs56 : List (List (Fin 14)) := [[0],[3,4],[1,5],[2,5],[4,5]]
lemma d56 (x : Fin 14 → Bool) : f56 x = dnf cs56 x := by
  simp [f56, cs56, dnf]
  <;> ac_rfl
def T56 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup56 (x y : Fin 14 → Bool) (h : ∀ i ∈ T56, x i = y i) : f56 x = f56 y := by
  simp only [f56, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep56 : ∀ p ∈ T56, Base.Readers.Dep f56 p := by
  have hc : ∀ p : Fin 14, p ∈ T56 → f56 (Function.update (wi (([0,32,32,16,8,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,32,32,16,8,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f56 (wi (([0,32,32,16,8,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,32,32,16,8,2,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower56 (s : Nat) (h : HasCircuitSize 14 f56 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f56 T56 dep56 s h
  have ht : T56.card = 6 := by decide +kernel
  omega
def f57 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)
def cs57 : List (List (Fin 14)) := [[0],[1],[2,5],[3,5],[4,5]]
lemma d57 (x : Fin 14 → Bool) : f57 x = dnf cs57 x := by
  simp [f57, cs57, dnf]
  <;> ac_rfl
def T57 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup57 (x y : Fin 14 → Bool) (h : ∀ i ∈ T57, x i = y i) : f57 x = f57 y := by
  simp only [f57, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep57 : ∀ p ∈ T57, Base.Readers.Dep f57 p := by
  have hc : ∀ p : Fin 14, p ∈ T57 → f57 (Function.update (wi (([0,0,32,32,32,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,32,32,32,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f57 (wi (([0,0,32,32,32,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,32,32,32,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower57 (s : Nat) (h : HasCircuitSize 14 f57 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f57 T57 dep57 s h
  have ht : T57.card = 6 := by decide +kernel
  omega
def f58 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6)
def cs58 : List (List (Fin 14)) := [[0],[3,5],[4,5],[1,6],[2,6],[4,6]]
lemma d58 (x : Fin 14 → Bool) : f58 x = dnf cs58 x := by
  simp [f58, cs58, dnf]
  <;> ac_rfl
def T58 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup58 (x y : Fin 14 → Bool) (h : ∀ i ∈ T58, x i = y i) : f58 x = f58 y := by
  simp only [f58, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep58 : ∀ p ∈ T58, Base.Readers.Dep f58 p := by
  have hc : ∀ p : Fin 14, p ∈ T58 → f58 (Function.update (wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f58 (wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower58 (s : Nat) (h : HasCircuitSize 14 f58 s) : 7 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f58 3 s
    (dep58 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower56
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,4,3,5,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f58 (Function.update (x ∘ ren) 3 false)) = f56 := by
      funext x
      rw [d58, d56, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f58 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower57
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,4,0,2,1,5,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f58 (Function.update (x ∘ ren) 3 true)) = f57 := by
      funext x
      rw [d58, d57, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f58 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f59 (x : Fin 14 → Bool) : Bool := (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)
def cs59 : List (List (Fin 14)) := [[2,5],[4,5],[1,6],[3,6],[0,7],[3,7],[4,7]]
lemma d59 (x : Fin 14 → Bool) : f59 x = dnf cs59 x := by
  simp [f59, cs59, dnf]
  <;> ac_rfl
def T59 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup59 (x y : Fin 14 → Bool) (h : ∀ i ∈ T59, x i = y i) : f59 x = f59 y := by
  simp only [f59, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep59 : ∀ p ∈ T59, Base.Readers.Dep f59 p := by
  have hc : ∀ p : Fin 14, p ∈ T59 → f59 (Function.update (wi (([128,64,32,64,32,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([128,64,32,64,32,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f59 (wi (([128,64,32,64,32,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([128,64,32,64,32,4,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower59 (s : Nat) (h : HasCircuitSize 14 f59 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f59 1 s
    (dep59 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 36, by decide +kernel⟩
      · exact ⟨wi 0, wi 64, by decide +kernel⟩) h
  cases b
  · have hh := lower55
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,4,3,5,2,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f59 (Function.update (x ∘ ren) 1 false)) = f55 := by
      funext x
      rw [d59, d55, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f59 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower58
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,2,4,5,0,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f59 (Function.update (x ∘ ren) 1 true)) = f58 := by
      funext x
      rw [d59, d58, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f59 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f60 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 5)
def cs60 : List (List (Fin 14)) := [[0],[1],[3,4],[2,5],[4,5]]
lemma d60 (x : Fin 14 → Bool) : f60 x = dnf cs60 x := by
  simp [f60, cs60, dnf]
  <;> ac_rfl
def T60 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup60 (x y : Fin 14 → Bool) (h : ∀ i ∈ T60, x i = y i) : f60 x = f60 y := by
  simp only [f60, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep60 : ∀ p ∈ T60, Base.Readers.Dep f60 p := by
  have hc : ∀ p : Fin 14, p ∈ T60 → f60 (Function.update (wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f60 (wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,32,16,8,4,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower60 (s : Nat) (h : HasCircuitSize 14 f60 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f60 T60 dep60 s h
  have ht : T60.card = 6 := by decide +kernel
  omega
def f61 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 3 && x 5) || (x 4 && x 5)
def cs61 : List (List (Fin 14)) := [[0],[1],[2],[3,5],[4,5]]
lemma d61 (x : Fin 14 → Bool) : f61 x = dnf cs61 x := by
  simp [f61, cs61, dnf]
  <;> ac_rfl
def T61 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup61 (x y : Fin 14 → Bool) (h : ∀ i ∈ T61, x i = y i) : f61 x = f61 y := by
  simp only [f61, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep61 : ∀ p ∈ T61, Base.Readers.Dep f61 p := by
  have hc : ∀ p : Fin 14, p ∈ T61 → f61 (Function.update (wi (([0,0,0,32,32,8,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,32,32,8,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f61 (wi (([0,0,0,32,32,8,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,32,32,8,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower61 (s : Nat) (h : HasCircuitSize 14 f61 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f61 T61 dep61 s h
  have ht : T61.card = 6 := by decide +kernel
  omega
def f62 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6)
def cs62 : List (List (Fin 14)) := [[0],[1],[3,5],[4,5],[2,6],[4,6]]
lemma d62 (x : Fin 14 → Bool) : f62 x = dnf cs62 x := by
  simp [f62, cs62, dnf]
  <;> ac_rfl
def T62 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup62 (x y : Fin 14 → Bool) (h : ∀ i ∈ T62, x i = y i) : f62 x = f62 y := by
  simp only [f62, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep62 : ∀ p ∈ T62, Base.Readers.Dep f62 p := by
  have hc : ∀ p : Fin 14, p ∈ T62 → f62 (Function.update (wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f62 (wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower62 (s : Nat) (h : HasCircuitSize 14 f62 s) : 7 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f62 2 s
    (dep62 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower60
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,3,5,4,2,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f62 (Function.update (x ∘ ren) 2 false)) = f60 := by
      funext x
      rw [d62, d60, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f62 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower61
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,0,3,4,5,0,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f62 (Function.update (x ∘ ren) 2 true)) = f61 := by
      funext x
      rw [d62, d61, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f62 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f63 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 4 && x 5)
def cs63 : List (List (Fin 14)) := [[0],[1],[2],[3],[4,5]]
lemma d63 (x : Fin 14 → Bool) : f63 x = dnf cs63 x := by
  simp [f63, cs63, dnf]
  <;> ac_rfl
def T63 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5}
lemma sup63 (x y : Fin 14 → Bool) (h : ∀ i ∈ T63, x i = y i) : f63 x = f63 y := by
  simp only [f63, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
lemma dep63 : ∀ p ∈ T63, Base.Readers.Dep f63 p := by
  have hc : ∀ p : Fin 14, p ∈ T63 → f63 (Function.update (wi (([0,0,0,0,32,16,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,32,16,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f63 (wi (([0,0,0,0,32,16,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,32,16,0,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower63 (s : Nat) (h : HasCircuitSize 14 f63 s) : 5 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f63 T63 dep63 s h
  have ht : T63.card = 6 := by decide +kernel
  omega
def f64 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def cs64 : List (List (Fin 14)) := [[0],[1],[2],[4,5],[3,6],[5,6]]
lemma d64 (x : Fin 14 → Bool) : f64 x = dnf cs64 x := by
  simp [f64, cs64, dnf]
  <;> ac_rfl
def T64 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup64 (x y : Fin 14 → Bool) (h : ∀ i ∈ T64, x i = y i) : f64 x = f64 y := by
  simp only [f64, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep64 : ∀ p ∈ T64, Base.Readers.Dep f64 p := by
  have hc : ∀ p : Fin 14, p ∈ T64 → f64 (Function.update (wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f64 (wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower64 (s : Nat) (h : HasCircuitSize 14 f64 s) : 7 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f64 3 s
    (dep64 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower61
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,3,5,4,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f64 (Function.update (x ∘ ren) 3 false)) = f61 := by
      funext x
      rw [d64, d61, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f64 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower63
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,5,4,3,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f64 (Function.update (x ∘ ren) 3 true)) = f63 := by
      funext x
      rw [d64, d63, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f64 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f65 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 4 && x 7)
def cs65 : List (List (Fin 14)) := [[0],[1],[4,5],[3,6],[5,6],[2,7],[4,7]]
lemma d65 (x : Fin 14 → Bool) : f65 x = dnf cs65 x := by
  simp [f65, cs65, dnf]
  <;> ac_rfl
def T65 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup65 (x y : Fin 14 → Bool) (h : ∀ i ∈ T65, x i = y i) : f65 x = f65 y := by
  simp only [f65, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep65 : ∀ p ∈ T65, Base.Readers.Dep f65 p := by
  have hc : ∀ p : Fin 14, p ∈ T65 → f65 (Function.update (wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f65 (wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower65 (s : Nat) (h : HasCircuitSize 14 f65 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f65 2 s
    (dep65 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower62
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,2,5,4,6,3,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f65 (Function.update (x ∘ ren) 2 false)) = f62 := by
      funext x
      rw [d65, d62, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f65 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower64
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,0,4,3,6,5,1,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f65 (Function.update (x ∘ ren) 2 true)) = f64 := by
      funext x
      rw [d65, d64, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f65 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f66 (x : Fin 14 → Bool) : Bool := (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8)
def cs66 : List (List (Fin 14)) := [[3,5],[4,5],[2,6],[4,6],[0,7],[1,7],[1,8],[2,8],[3,8]]
lemma d66 (x : Fin 14 → Bool) : f66 x = dnf cs66 x := by
  simp [f66, cs66, dnf]
  <;> ac_rfl
def T66 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup66 (x y : Fin 14 → Bool) (h : ∀ i ∈ T66, x i = y i) : f66 x = f66 y := by
  simp only [f66, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep66 : ∀ p ∈ T66, Base.Readers.Dep f66 p := by
  have hc : ∀ p : Fin 14, p ∈ T66 → f66 (Function.update (wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f66 (wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([128,128,64,32,32,8,4,1,2,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower66 (s : Nat) (h : HasCircuitSize 14 f66 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f66 5 s
    (dep66 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 68, by decide +kernel⟩
      · exact ⟨wi 0, wi 8, by decide +kernel⟩) h
  cases b
  · have hh := lower59
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,3,4,0,2,0,5,6,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f66 (Function.update (x ∘ ren) 5 false)) = f59 := by
      funext x
      rw [d66, d59, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f66 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower65
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,5,7,1,0,0,2,6,4,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f66 (Function.update (x ∘ ren) 5 true)) = f65 := by
      funext x
      rw [d66, d65, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f66 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f67 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 3 && x 6)
def cs67 : List (List (Fin 14)) := [[0],[3,4],[2,5],[4,5],[1,6],[3,6]]
lemma d67 (x : Fin 14 → Bool) : f67 x = dnf cs67 x := by
  simp [f67, cs67, dnf]
  <;> ac_rfl
def T67 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup67 (x y : Fin 14 → Bool) (h : ∀ i ∈ T67, x i = y i) : f67 x = f67 y := by
  simp only [f67, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep67 : ∀ p ∈ T67, Base.Readers.Dep f67 p := by
  have hc : ∀ p : Fin 14, p ∈ T67 → f67 (Function.update (wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f67 (wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,64,32,16,8,4,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower67 (s : Nat) (h : HasCircuitSize 14 f67 s) : 7 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f67 1 s
    (dep67 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower54
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,4,3,5,2,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f67 (Function.update (x ∘ ren) 1 false)) = f54 := by
      funext x
      rw [d67, d54, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f67 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower60
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,3,2,5,4,1,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f67 (Function.update (x ∘ ren) 1 true)) = f60 := by
      funext x
      rw [d67, d60, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f67 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f68 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 3 && x 7)
def cs68 : List (List (Fin 14)) := [[0],[3,5],[4,5],[2,6],[4,6],[1,7],[3,7]]
lemma d68 (x : Fin 14 → Bool) : f68 x = dnf cs68 x := by
  simp [f68, cs68, dnf]
  <;> ac_rfl
def T68 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup68 (x y : Fin 14 → Bool) (h : ∀ i ∈ T68, x i = y i) : f68 x = f68 y := by
  simp only [f68, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep68 : ∀ p ∈ T68, Base.Readers.Dep f68 p := by
  have hc : ∀ p : Fin 14, p ∈ T68 → f68 (Function.update (wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f68 (wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower68 (s : Nat) (h : HasCircuitSize 14 f68 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f68 1 s
    (dep68 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower67
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,2,6,4,3,5,1,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f68 (Function.update (x ∘ ren) 1 false)) = f67 := by
      funext x
      rw [d68, d67, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f68 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower62
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,3,4,5,6,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f68 (Function.update (x ∘ ren) 1 true)) = f62 := by
      funext x
      rw [d68, d62, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f68 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f69 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8)
def cs69 : List (List (Fin 14)) := [[0],[4,5],[3,6],[5,6],[2,7],[4,7],[1,8],[3,8]]
lemma d69 (x : Fin 14 → Bool) : f69 x = dnf cs69 x := by
  simp [f69, cs69, dnf]
  <;> ac_rfl
def T69 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup69 (x y : Fin 14 → Bool) (h : ∀ i ∈ T69, x i = y i) : f69 x = f69 y := by
  simp only [f69, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep69 : ∀ p ∈ T69, Base.Readers.Dep f69 p := by
  have hc : ∀ p : Fin 14, p ∈ T69 → f69 (Function.update (wi (([0,256,128,64,32,16,8,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,256,128,64,32,16,8,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f69 (wi (([0,256,128,64,32,16,8,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,256,128,64,32,16,8,4,2,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower69 (s : Nat) (h : HasCircuitSize 14 f69 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f69 1 s
    (dep69 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower68
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,6,3,5,4,7,2,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f69 (Function.update (x ∘ ren) 1 false)) = f68 := by
      funext x
      rw [d69, d68, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f69 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower65
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,2,5,4,7,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f69 (Function.update (x ∘ ren) 1 true)) = f65 := by
      funext x
      rw [d69, d65, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f69 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f70 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 2 && x 8) || (x 4 && x 8) || (x 0 && x 9) || (x 3 && x 9) || (x 8 && x 9)
def cs70 : List (List (Fin 14)) := [[4,5],[3,6],[5,6],[1,7],[2,7],[2,8],[4,8],[0,9],[3,9],[8,9]]
lemma d70 (x : Fin 14 → Bool) : f70 x = dnf cs70 x := by
  simp [f70, cs70, dnf]
  <;> ac_rfl
def T70 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup70 (x y : Fin 14 → Bool) (h : ∀ i ∈ T70, x i = y i) : f70 x = f70 y := by
  simp only [f70, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep70 : ∀ p ∈ T70, Base.Readers.Dep f70 p := by
  have hc : ∀ p : Fin 14, p ∈ T70 → f70 (Function.update (wi (([512,128,128,64,32,16,8,2,4,1,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([512,128,128,64,32,16,8,2,4,1,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f70 (wi (([512,128,128,64,32,16,8,2,4,1,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([512,128,128,64,32,16,8,2,4,1,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower70 (s : Nat) (h : HasCircuitSize 14 f70 s) : 13 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f70 0 s
    (dep70 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 512, by decide +kernel⟩) h
  cases b
  · have hh := lower66
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,5,2,6,4,7,8,3,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f70 (Function.update (x ∘ ren) 0 false)) = f66 := by
      funext x
      rw [d70, d66, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f70 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower69
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,4,1,6,3,8,7,5,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f70 (Function.update (x ∘ ren) 0 true)) = f69 := by
      funext x
      rw [d70, d69, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f70 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f71 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6) || (x 1 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 4 && x 9) || (x 7 && x 9) || (x 2 && x 10) || (x 3 && x 10) || (x 9 && x 10)
def cs71 : List (List (Fin 14)) := [[4,5],[3,6],[5,6],[1,7],[0,8],[2,8],[4,9],[7,9],[2,10],[3,10],[9,10]]
lemma d71 (x : Fin 14 → Bool) : f71 x = dnf cs71 x := by
  simp [f71, cs71, dnf]
  <;> ac_rfl
def T71 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup71 (x y : Fin 14 → Bool) (h : ∀ i ∈ T71, x i = y i) : f71 x = f71 y := by
  simp only [f71, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep71 : ∀ p ∈ T71, Base.Readers.Dep f71 p := by
  have hc : ∀ p : Fin 14, p ∈ T71 → f71 (Function.update (wi (([256,128,256,64,32,16,8,2,1,16,4,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([256,128,256,64,32,16,8,2,1,16,4,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f71 (wi (([256,128,256,64,32,16,8,2,1,16,4,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([256,128,256,64,32,16,8,2,1,16,4,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower71 (s : Nat) (h : HasCircuitSize 14 f71 s) : 15 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f71 1 s
    (dep71 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 128, by decide +kernel⟩) h
  cases b
  · have hh := lower70
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,4,3,6,5,0,7,9,8,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f71 (Function.update (x ∘ ren) 1 false)) = f70 := by
      funext x
      rw [d71, d70, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f71 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower40
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,3,6,5,7,0,8,4,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f71 (Function.update (x ∘ ren) 1 true)) = f40 := by
      funext x
      rw [d71, d40, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f71 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f72 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 5 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 7 && x 9) || (x 1 && x 10) || (x 6 && x 10) || (x 7 && x 10) || (x 0 && x 11) || (x 2 && x 11) || (x 6 && x 11)
def cs72 : List (List (Fin 14)) := [[4,5],[5,7],[3,8],[4,8],[6,8],[2,9],[3,9],[7,9],[1,10],[6,10],[7,10],[0,11],[2,11],[6,11]]
lemma d72 (x : Fin 14 → Bool) : f72 x = dnf cs72 x := by
  simp [f72, cs72, dnf]
  <;> ac_rfl
def T72 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup72 (x y : Fin 14 → Bool) (h : ∀ i ∈ T72, x i = y i) : f72 x = f72 y := by
  simp only [f72, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep72 : ∀ p ∈ T72, Base.Readers.Dep f72 p := by
  have hc : ∀ p : Fin 14, p ∈ T72 → f72 (Function.update (wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0)) p (!(wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0)) p)) ≠ f72 (wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower72 (s : Nat) (h : HasCircuitSize 14 f72 s) : 16 ≤ s := by
  by_contra hn
  have hs : s ≤ 15 := by omega
  have hbig : HasCircuitSize 14 f72 (14+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f72 6 false 14
    (dep72 6 (by decide)) ⟨wi 0, wi 48, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,5,4,0,9,6,10,7,8,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f72 (Function.update (x ∘ ren) 6 false)) = f71 := by
    funext x
    rw [d72, d71, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f72 (Function.update (x ∘ ren) 6 false)) _ at hc
  rw [he] at hc
  have := lower71 14 hc
  omega
def f73 (x : Fin 14 → Bool) : Bool := (x 3 && x 6) || (x 3 && x 7) || (x 2 && x 8) || (x 5 && x 8) || (x 7 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 6 && x 9) || (x 1 && x 10) || (x 5 && x 10) || (x 6 && x 10) || (x 1 && x 11) || (x 4 && x 11) || (x 7 && x 11) || (x 0 && x 12) || (x 4 && x 12) || (x 5 && x 12)
def cs73 : List (List (Fin 14)) := [[3,6],[3,7],[2,8],[5,8],[7,8],[2,9],[4,9],[6,9],[1,10],[5,10],[6,10],[1,11],[4,11],[7,11],[0,12],[4,12],[5,12]]
lemma d73 (x : Fin 14 → Bool) : f73 x = dnf cs73 x := by
  simp [f73, cs73, dnf]
  <;> ac_rfl
def T73 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup73 (x y : Fin 14 → Bool) (h : ∀ i ∈ T73, x i = y i) : f73 x = f73 y := by
  simp only [f73, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep73 : ∀ p ∈ T73, Base.Readers.Dep f73 p := by
  have hc : ∀ p : Fin 14, p ∈ T73 → f73 (Function.update (wi (([4096,1024,256,64,512,256,8,8,4,4,2,2,1,0] : List Nat).getD p.val 0)) p (!(wi (([4096,1024,256,64,512,256,8,8,4,4,2,2,1,0] : List Nat).getD p.val 0)) p)) ≠ f73 (wi (([4096,1024,256,64,512,256,8,8,4,4,2,2,1,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([4096,1024,256,64,512,256,8,8,4,4,2,2,1,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower73 (s : Nat) (h : HasCircuitSize 14 f73 s) : 17 ≤ s := by
  by_contra hn
  have hs : s ≤ 16 := by omega
  have hbig : HasCircuitSize 14 f73 (15+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f73 8 false 15
    (dep73 8 (by decide)) ⟨wi 0, wi 72, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,1,5,6,2,7,4,0,10,9,8,11,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f73 (Function.update (x ∘ ren) 8 false)) = f72 := by
    funext x
    rw [d73, d72, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f73 (Function.update (x ∘ ren) 8 false)) _ at hc
  rw [he] at hc
  have := lower72 15 hc
  omega
def f74 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || x 5 || (x 6 && x 7)
def cs74 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[5],[6,7]]
lemma d74 (x : Fin 14 → Bool) : f74 x = dnf cs74 x := by
  simp [f74, cs74, dnf]
  <;> ac_rfl
def T74 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup74 (x y : Fin 14 → Bool) (h : ∀ i ∈ T74, x i = y i) : f74 x = f74 y := by
  simp only [f74, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep74 : ∀ p ∈ T74, Base.Readers.Dep f74 p := by
  have hc : ∀ p : Fin 14, p ∈ T74 → f74 (Function.update (wi (([0,0,0,0,0,0,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,0,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f74 (wi (([0,0,0,0,0,0,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,0,128,64,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower74 (s : Nat) (h : HasCircuitSize 14 f74 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f74 T74 dep74 s h
  have ht : T74.card = 8 := by decide +kernel
  omega
def f75 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || (x 6 && x 7) || (x 5 && x 8) || (x 7 && x 8)
def cs75 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[6,7],[5,8],[7,8]]
lemma d75 (x : Fin 14 → Bool) : f75 x = dnf cs75 x := by
  simp [f75, cs75, dnf]
  <;> ac_rfl
def T75 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup75 (x y : Fin 14 → Bool) (h : ∀ i ∈ T75, x i = y i) : f75 x = f75 y := by
  simp only [f75, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep75 : ∀ p ∈ T75, Base.Readers.Dep f75 p := by
  have hc : ∀ p : Fin 14, p ∈ T75 → f75 (Function.update (wi (([0,0,0,0,0,256,128,64,32,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,256,128,64,32,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f75 (wi (([0,0,0,0,0,256,128,64,32,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,256,128,64,32,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower75 (s : Nat) (h : HasCircuitSize 14 f75 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f75 5 s
    (dep75 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower10
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,0,5,7,6,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f75 (Function.update (x ∘ ren) 5 false)) = f10 := by
      funext x
      rw [d75, d10, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f75 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower74
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,5,0,7,6,1,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f75 (Function.update (x ∘ ren) 5 true)) = f74 := by
      funext x
      rw [d75, d74, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f75 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f76 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 6 && x 7) || (x 5 && x 8) || (x 7 && x 8) || (x 4 && x 9) || (x 6 && x 9)
def cs76 : List (List (Fin 14)) := [[0],[1],[2],[3],[6,7],[5,8],[7,8],[4,9],[6,9]]
lemma d76 (x : Fin 14 → Bool) : f76 x = dnf cs76 x := by
  simp [f76, cs76, dnf]
  <;> ac_rfl
def T76 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup76 (x y : Fin 14 → Bool) (h : ∀ i ∈ T76, x i = y i) : f76 x = f76 y := by
  simp only [f76, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep76 : ∀ p ∈ T76, Base.Readers.Dep f76 p := by
  have hc : ∀ p : Fin 14, p ∈ T76 → f76 (Function.update (wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f76 (wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower76 (s : Nat) (h : HasCircuitSize 14 f76 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f76 4 s
    (dep76 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower11
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,7,6,8,5,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f76 (Function.update (x ∘ ren) 4 false)) = f11 := by
      funext x
      rw [d76, d11, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f76 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower75
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,0,6,5,8,7,1,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f76 (Function.update (x ∘ ren) 4 true)) = f75 := by
      funext x
      rw [d76, d75, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f76 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f77 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 6) || (x 4 && x 7) || (x 6 && x 8) || (x 7 && x 8) || (x 3 && x 9) || (x 4 && x 9) || (x 5 && x 9) || (x 2 && x 10) || (x 3 && x 10) || (x 8 && x 10)
def cs77 : List (List (Fin 14)) := [[0],[1],[5,6],[4,7],[6,8],[7,8],[3,9],[4,9],[5,9],[2,10],[3,10],[8,10]]
lemma d77 (x : Fin 14 → Bool) : f77 x = dnf cs77 x := by
  simp [f77, cs77, dnf]
  <;> ac_rfl
def T77 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup77 (x y : Fin 14 → Bool) (h : ∀ i ∈ T77, x i = y i) : f77 x = f77 y := by
  simp only [f77, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep77 : ∀ p ∈ T77, Base.Readers.Dep f77 p := by
  have hc : ∀ p : Fin 14, p ∈ T77 → f77 (Function.update (wi (([0,0,1024,512,128,64,32,16,64,8,4,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,1024,512,128,64,32,16,64,8,4,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f77 (wi (([0,0,1024,512,128,64,32,16,64,8,4,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,1024,512,128,64,32,16,64,8,4,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower77 (s : Nat) (h : HasCircuitSize 14 f77 s) : 13 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f77 6 s
    (dep77 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower20
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,4,6,3,0,7,5,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f77 (Function.update (x ∘ ren) 6 false)) = f20 := by
      funext x
      rw [d77, d20, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f77 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower76
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,5,7,9,2,0,4,1,6,8,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f77 (Function.update (x ∘ ren) 6 true)) = f76 := by
      funext x
      rw [d77, d76, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f77 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f78 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 2 && x 7) || (x 3 && x 7)
def cs78 : List (List (Fin 14)) := [[0],[1],[3,5],[4,5],[2,6],[4,6],[2,7],[3,7]]
lemma d78 (x : Fin 14 → Bool) : f78 x = dnf cs78 x := by
  simp [f78, cs78, dnf]
  <;> ac_rfl
def T78 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup78 (x y : Fin 14 → Bool) (h : ∀ i ∈ T78, x i = y i) : f78 x = f78 y := by
  simp only [f78, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep78 : ∀ p ∈ T78, Base.Readers.Dep f78 p := by
  have hc : ∀ p : Fin 14, p ∈ T78 → f78 (Function.update (wi (([0,0,64,32,32,8,4,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,64,32,32,8,4,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f78 (wi (([0,0,64,32,32,8,4,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,64,32,32,8,4,4,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower78 (s : Nat) (h : HasCircuitSize 14 f78 s) : 10 ≤ s := by
  by_contra hn
  have hs : s ≤ 9 := by omega
  have hbig : HasCircuitSize 14 f78 (8+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f78 0 false 8
    (dep78 0 (by decide)) ⟨wi 0, wi 2, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f78 (Function.update (x ∘ ren) 0 false)) = f37 := by
    funext x
    rw [d78, d37, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f78 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower37 8 hc
  omega
def f79 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7) || (x 3 && x 8) || (x 4 && x 8)
def cs79 : List (List (Fin 14)) := [[0],[1],[2],[4,6],[5,6],[3,7],[5,7],[3,8],[4,8]]
lemma d79 (x : Fin 14 → Bool) : f79 x = dnf cs79 x := by
  simp [f79, cs79, dnf]
  <;> ac_rfl
def T79 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup79 (x y : Fin 14 → Bool) (h : ∀ i ∈ T79, x i = y i) : f79 x = f79 y := by
  simp only [f79, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep79 : ∀ p ∈ T79, Base.Readers.Dep f79 p := by
  have hc : ∀ p : Fin 14, p ∈ T79 → f79 (Function.update (wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f79 (wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,128,64,64,16,8,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower79 (s : Nat) (h : HasCircuitSize 14 f79 s) : 11 ≤ s := by
  by_contra hn
  have hs : s ≤ 10 := by omega
  have hbig : HasCircuitSize 14 f79 (9+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f79 0 false 9
    (dep79 0 (by decide)) ⟨wi 0, wi 2, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f79 (Function.update (x ∘ ren) 0 false)) = f78 := by
    funext x
    rw [d79, d78, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f79 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower78 9 hc
  omega
def f80 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 5 && x 7) || (x 6 && x 7) || (x 4 && x 8) || (x 6 && x 8) || (x 4 && x 9) || (x 5 && x 9)
def cs80 : List (List (Fin 14)) := [[0],[1],[2],[3],[5,7],[6,7],[4,8],[6,8],[4,9],[5,9]]
lemma d80 (x : Fin 14 → Bool) : f80 x = dnf cs80 x := by
  simp [f80, cs80, dnf]
  <;> ac_rfl
def T80 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup80 (x y : Fin 14 → Bool) (h : ∀ i ∈ T80, x i = y i) : f80 x = f80 y := by
  simp only [f80, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep80 : ∀ p ∈ T80, Base.Readers.Dep f80 p := by
  have hc : ∀ p : Fin 14, p ∈ T80 → f80 (Function.update (wi (([0,0,0,0,256,128,128,32,16,16,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,256,128,128,32,16,16,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f80 (wi (([0,0,0,0,256,128,128,32,16,16,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,256,128,128,32,16,16,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower80 (s : Nat) (h : HasCircuitSize 14 f80 s) : 12 ≤ s := by
  by_contra hn
  have hs : s ≤ 11 := by omega
  have hbig : HasCircuitSize 14 f80 (10+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f80 0 false 10
    (dep80 0 (by decide)) ⟨wi 0, wi 2, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f80 (Function.update (x ∘ ren) 0 false)) = f79 := by
    funext x
    rw [d80, d79, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f80 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower79 10 hc
  omega
def f81 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 6 && x 8) || (x 7 && x 8) || (x 5 && x 9) || (x 7 && x 9) || (x 4 && x 10) || (x 5 && x 10) || (x 6 && x 10)
def cs81 : List (List (Fin 14)) := [[0],[1],[2],[3],[6,8],[7,8],[5,9],[7,9],[4,10],[5,10],[6,10]]
lemma d81 (x : Fin 14 → Bool) : f81 x = dnf cs81 x := by
  simp [f81, cs81, dnf]
  <;> ac_rfl
def T81 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup81 (x y : Fin 14 → Bool) (h : ∀ i ∈ T81, x i = y i) : f81 x = f81 y := by
  simp only [f81, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep81 : ∀ p ∈ T81, Base.Readers.Dep f81 p := by
  have hc : ∀ p : Fin 14, p ∈ T81 → f81 (Function.update (wi (([0,0,0,0,1024,512,256,256,64,32,16,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,1024,512,256,256,64,32,16,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f81 (wi (([0,0,0,0,1024,512,256,256,64,32,16,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,1024,512,256,256,64,32,16,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower81 (s : Nat) (h : HasCircuitSize 14 f81 s) : 13 ≤ s := by
  by_contra hn
  have hs : s ≤ 12 := by omega
  have hbig : HasCircuitSize 14 f81 (11+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f81 4 false 11
    (dep81 4 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,6,5,7,9,8,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f81 (Function.update (x ∘ ren) 4 false)) = f80 := by
    funext x
    rw [d81, d80, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f81 (Function.update (x ∘ ren) 4 false)) _ at hc
  rw [he] at hc
  have := lower80 11 hc
  omega
def f82 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 6) || (x 4 && x 7) || (x 3 && x 8) || (x 7 && x 8) || (x 3 && x 9) || (x 6 && x 9) || (x 2 && x 10) || (x 5 && x 10) || (x 8 && x 10) || (x 2 && x 11) || (x 4 && x 11) || (x 9 && x 11)
def cs82 : List (List (Fin 14)) := [[0],[1],[5,6],[4,7],[3,8],[7,8],[3,9],[6,9],[2,10],[5,10],[8,10],[2,11],[4,11],[9,11]]
lemma d82 (x : Fin 14 → Bool) : f82 x = dnf cs82 x := by
  simp [f82, cs82, dnf]
  <;> ac_rfl
def T82 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup82 (x y : Fin 14 → Bool) (h : ∀ i ∈ T82, x i = y i) : f82 x = f82 y := by
  simp only [f82, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep82 : ∀ p ∈ T82, Base.Readers.Dep f82 p := by
  have hc : ∀ p : Fin 14, p ∈ T82 → f82 (Function.update (wi (([0,0,1024,256,128,64,32,16,8,8,4,4,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,1024,256,128,64,32,16,8,8,4,4,0,0] : List Nat).getD p.val 0)) p)) ≠ f82 (wi (([0,0,1024,256,128,64,32,16,8,8,4,4,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,1024,256,128,64,32,16,8,8,4,4,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower82 (s : Nat) (h : HasCircuitSize 14 f82 s) : 15 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f82 4 s
    (dep82 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower77
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,6,3,0,7,4,2,10,9,8,5,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f82 (Function.update (x ∘ ren) 4 false)) = f77 := by
      funext x
      rw [d82, d77, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f82 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower81
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,4,8,0,5,9,1,6,7,10,2,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f82 (Function.update (x ∘ ren) 4 true)) = f81 := by
      funext x
      rw [d82, d81, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f82 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f83 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 6 && x 7) || (x 6 && x 8) || (x 4 && x 9) || (x 5 && x 9) || (x 8 && x 9) || (x 2 && x 10) || (x 3 && x 10) || (x 8 && x 10) || (x 3 && x 11) || (x 5 && x 11) || (x 7 && x 11) || (x 2 && x 12) || (x 4 && x 12) || (x 7 && x 12)
def cs83 : List (List (Fin 14)) := [[0],[1],[6,7],[6,8],[4,9],[5,9],[8,9],[2,10],[3,10],[8,10],[3,11],[5,11],[7,11],[2,12],[4,12],[7,12]]
lemma d83 (x : Fin 14 → Bool) : f83 x = dnf cs83 x := by
  simp [f83, cs83, dnf]
  <;> ac_rfl
def T83 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup83 (x y : Fin 14 → Bool) (h : ∀ i ∈ T83, x i = y i) : f83 x = f83 y := by
  simp only [f83, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep83 : ∀ p ∈ T83, Base.Readers.Dep f83 p := by
  have hc : ∀ p : Fin 14, p ∈ T83 → f83 (Function.update (wi (([0,0,1024,1024,512,512,128,64,64,16,4,8,4,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,1024,1024,512,512,128,64,64,16,4,8,4,0] : List Nat).getD p.val 0)) p)) ≠ f83 (wi (([0,0,1024,1024,512,512,128,64,64,16,4,8,4,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,1024,1024,512,512,128,64,64,16,4,8,4,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower83 (s : Nat) (h : HasCircuitSize 14 f83 s) : 16 ≤ s := by
  by_contra hn
  have hs : s ≤ 15 := by omega
  have hbig : HasCircuitSize 14 f83 (14+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f83 5 false 14
    (dep83 5 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,5,4,0,3,9,8,7,10,6,11,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f83 (Function.update (x ∘ ren) 5 false)) = f82 := by
    funext x
    rw [d83, d82, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f83 (Function.update (x ∘ ren) 5 false)) _ at hc
  rw [he] at hc
  have := lower82 14 hc
  omega
def f84 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 6) || (x 4 && x 7) || (x 3 && x 8) || (x 7 && x 8) || (x 2 && x 9) || (x 6 && x 9) || (x 4 && x 10) || (x 5 && x 10) || (x 2 && x 11) || (x 3 && x 11) || (x 10 && x 11)
def cs84 : List (List (Fin 14)) := [[0],[1],[5,6],[4,7],[3,8],[7,8],[2,9],[6,9],[4,10],[5,10],[2,11],[3,11],[10,11]]
lemma d84 (x : Fin 14 → Bool) : f84 x = dnf cs84 x := by
  simp [f84, cs84, dnf]
  <;> ac_rfl
def T84 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup84 (x y : Fin 14 → Bool) (h : ∀ i ∈ T84, x i = y i) : f84 x = f84 y := by
  simp only [f84, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep84 : ∀ p ∈ T84, Base.Readers.Dep f84 p := by
  have hc : ∀ p : Fin 14, p ∈ T84 → f84 (Function.update (wi (([0,0,512,256,128,64,32,16,8,4,16,4,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,512,256,128,64,32,16,8,4,16,4,0,0] : List Nat).getD p.val 0)) p)) ≠ f84 (wi (([0,0,512,256,128,64,32,16,8,4,16,4,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,512,256,128,64,32,16,8,4,16,4,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower84 (s : Nat) (h : HasCircuitSize 14 f84 s) : 15 ≤ s := by
  by_contra hn
  have hs : s ≤ 14 := by omega
  have hbig : HasCircuitSize 14 f84 (13+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f84 6 false 13
    (dep84 6 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,8,5,4,2,0,7,6,3,10,9,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f84 (Function.update (x ∘ ren) 6 false)) = f50 := by
    funext x
    rw [d84, d50, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f84 (Function.update (x ∘ ren) 6 false)) _ at hc
  rw [he] at hc
  have := lower50 13 hc
  omega
def f85 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 8) || (x 3 && x 9) || (x 7 && x 9) || (x 8 && x 9) || (x 1 && x 10) || (x 4 && x 10) || (x 7 && x 10) || (x 0 && x 11) || (x 2 && x 11) || (x 7 && x 11) || (x 0 && x 12) || (x 1 && x 12) || (x 8 && x 12)
def cs85 : List (List (Fin 14)) := [[4,5],[2,6],[3,6],[5,8],[3,9],[7,9],[8,9],[1,10],[4,10],[7,10],[0,11],[2,11],[7,11],[0,12],[1,12],[8,12]]
lemma d85 (x : Fin 14 → Bool) : f85 x = dnf cs85 x := by
  simp [f85, cs85, dnf]
  <;> ac_rfl
def T85 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup85 (x y : Fin 14 → Bool) (h : ∀ i ∈ T85, x i = y i) : f85 x = f85 y := by
  simp only [f85, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep85 : ∀ p ∈ T85, Base.Readers.Dep f85 p := by
  have hc : ∀ p : Fin 14, p ∈ T85 → f85 (Function.update (wi (([2048,1024,64,64,32,16,4,512,32,8,2,1,1,0] : List Nat).getD p.val 0)) p (!(wi (([2048,1024,64,64,32,16,4,512,32,8,2,1,1,0] : List Nat).getD p.val 0)) p)) ≠ f85 (wi (([2048,1024,64,64,32,16,4,512,32,8,2,1,1,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([2048,1024,64,64,32,16,4,512,32,8,2,1,1,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower85 (s : Nat) (h : HasCircuitSize 14 f85 s) : 17 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f85 5 s
    (dep85 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 68, by decide +kernel⟩
      · exact ⟨wi 0, wi 16, by decide +kernel⟩) h
  cases b
  · have hh := lower22
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,1,5,4,0,0,6,7,2,9,11,8,10,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f85 (Function.update (x ∘ ren) 5 false)) = f22 := by
      funext x
      rw [d85, d22, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f85 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower84
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,8,5,9,0,0,6,11,1,2,3,10,7,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f85 (Function.update (x ∘ ren) 5 true)) = f84 := by
      funext x
      rw [d85, d84, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f85 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f86 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 6) || (x 4 && x 7) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8)
def cs86 : List (List (Fin 14)) := [[0],[1],[2],[5,6],[4,7],[3,8],[6,8],[7,8]]
lemma d86 (x : Fin 14 → Bool) : f86 x = dnf cs86 x := by
  simp [f86, cs86, dnf]
  <;> ac_rfl
def T86 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup86 (x y : Fin 14 → Bool) (h : ∀ i ∈ T86, x i = y i) : f86 x = f86 y := by
  simp only [f86, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep86 : ∀ p ∈ T86, Base.Readers.Dep f86 p := by
  have hc : ∀ p : Fin 14, p ∈ T86 → f86 (Function.update (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f86 (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower86 (s : Nat) (h : HasCircuitSize 14 f86 s) : 8 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f86 T86 dep86 s h
  have ht : T86.card = 9 := by decide +kernel
  omega
def f87 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 5 && x 7) || (x 6 && x 7) || (x 4 && x 8) || (x 6 && x 8)
def cs87 : List (List (Fin 14)) := [[0],[1],[2],[3],[5,7],[6,7],[4,8],[6,8]]
lemma d87 (x : Fin 14 → Bool) : f87 x = dnf cs87 x := by
  simp [f87, cs87, dnf]
  <;> ac_rfl
def T87 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup87 (x y : Fin 14 → Bool) (h : ∀ i ∈ T87, x i = y i) : f87 x = f87 y := by
  simp only [f87, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep87 : ∀ p ∈ T87, Base.Readers.Dep f87 p := by
  have hc : ∀ p : Fin 14, p ∈ T87 → f87 (Function.update (wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f87 (wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,256,128,128,32,16,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower87 (s : Nat) (h : HasCircuitSize 14 f87 s) : 8 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f87 T87 dep87 s h
  have ht : T87.card = 9 := by decide +kernel
  omega
def f88 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 6) || (x 4 && x 7) || (x 3 && x 8) || (x 6 && x 9) || (x 7 && x 9) || (x 8 && x 9)
def cs88 : List (List (Fin 14)) := [[0],[1],[2],[5,6],[4,7],[3,8],[6,9],[7,9],[8,9]]
lemma d88 (x : Fin 14 → Bool) : f88 x = dnf cs88 x := by
  simp [f88, cs88, dnf]
  <;> ac_rfl
def T88 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup88 (x y : Fin 14 → Bool) (h : ∀ i ∈ T88, x i = y i) : f88 x = f88 y := by
  simp only [f88, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep88 : ∀ p ∈ T88, Base.Readers.Dep f88 p := by
  have hc : ∀ p : Fin 14, p ∈ T88 → f88 (Function.update (wi (([0,0,0,256,128,64,32,16,8,64,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,256,128,64,32,16,8,64,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f88 (wi (([0,0,0,256,128,64,32,16,8,64,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,256,128,64,32,16,8,64,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower88 (s : Nat) (h : HasCircuitSize 14 f88 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f88 3 s
    (dep88 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower86
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,4,5,6,7,3,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f88 (Function.update (x ∘ ren) 3 false)) = f86 := by
      funext x
      rw [d88, d86, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f88 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower87
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,0,4,5,7,8,0,6,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f88 (Function.update (x ∘ ren) 3 true)) = f87 := by
      funext x
      rw [d88, d87, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f88 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f89 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)
def cs89 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[5,8],[6,8],[7,8]]
lemma d89 (x : Fin 14 → Bool) : f89 x = dnf cs89 x := by
  simp [f89, cs89, dnf]
  <;> ac_rfl
def T89 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup89 (x y : Fin 14 → Bool) (h : ∀ i ∈ T89, x i = y i) : f89 x = f89 y := by
  simp only [f89, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep89 : ∀ p ∈ T89, Base.Readers.Dep f89 p := by
  have hc : ∀ p : Fin 14, p ∈ T89 → f89 (Function.update (wi (([0,0,0,0,0,256,256,256,32,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,256,256,256,32,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f89 (wi (([0,0,0,0,0,256,256,256,32,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,256,256,256,32,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower89 (s : Nat) (h : HasCircuitSize 14 f89 s) : 8 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f89 T89 dep89 s h
  have ht : T89.card = 9 := by decide +kernel
  omega
def f90 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || x 5 || (x 6 && x 8) || (x 7 && x 8)
def cs90 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[5],[6,8],[7,8]]
lemma d90 (x : Fin 14 → Bool) : f90 x = dnf cs90 x := by
  simp [f90, cs90, dnf]
  <;> ac_rfl
def T90 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup90 (x y : Fin 14 → Bool) (h : ∀ i ∈ T90, x i = y i) : f90 x = f90 y := by
  simp only [f90, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep90 : ∀ p ∈ T90, Base.Readers.Dep f90 p := by
  have hc : ∀ p : Fin 14, p ∈ T90 → f90 (Function.update (wi (([0,0,0,0,0,0,256,256,64,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,0,256,256,64,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f90 (wi (([0,0,0,0,0,0,256,256,64,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,0,256,256,64,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower90 (s : Nat) (h : HasCircuitSize 14 f90 s) : 8 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f90 T90 dep90 s h
  have ht : T90.card = 9 := by decide +kernel
  omega
def f91 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || (x 7 && x 8) || (x 5 && x 9) || (x 6 && x 9) || (x 8 && x 9)
def cs91 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[7,8],[5,9],[6,9],[8,9]]
lemma d91 (x : Fin 14 → Bool) : f91 x = dnf cs91 x := by
  simp [f91, cs91, dnf]
  <;> ac_rfl
def T91 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup91 (x y : Fin 14 → Bool) (h : ∀ i ∈ T91, x i = y i) : f91 x = f91 y := by
  simp only [f91, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep91 : ∀ p ∈ T91, Base.Readers.Dep f91 p := by
  have hc : ∀ p : Fin 14, p ∈ T91 → f91 (Function.update (wi (([0,0,0,0,0,512,512,256,128,32,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,512,512,256,128,32,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f91 (wi (([0,0,0,0,0,512,512,256,128,32,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,512,512,256,128,32,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower91 (s : Nat) (h : HasCircuitSize 14 f91 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f91 7 s
    (dep91 7 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower89
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,6,7,0,5,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f91 (Function.update (x ∘ ren) 7 false)) = f89 := by
      funext x
      rw [d91, d89, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f91 (Function.update (x ∘ ren) 7 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower90
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,4,5,6,7,0,0,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f91 (Function.update (x ∘ ren) 7 true)) = f90 := by
      funext x
      rw [d91, d90, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f91 (Function.update (x ∘ ren) 7 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f92 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 7) || (x 6 && x 7) || (x 4 && x 8) || (x 6 && x 8) || (x 3 && x 9) || (x 4 && x 10) || (x 5 && x 10) || (x 9 && x 10)
def cs92 : List (List (Fin 14)) := [[0],[1],[2],[5,7],[6,7],[4,8],[6,8],[3,9],[4,10],[5,10],[9,10]]
lemma d92 (x : Fin 14 → Bool) : f92 x = dnf cs92 x := by
  simp [f92, cs92, dnf]
  <;> ac_rfl
def T92 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup92 (x y : Fin 14 → Bool) (h : ∀ i ∈ T92, x i = y i) : f92 x = f92 y := by
  simp only [f92, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep92 : ∀ p ∈ T92, Base.Readers.Dep f92 p := by
  have hc : ∀ p : Fin 14, p ∈ T92 → f92 (Function.update (wi (([0,0,0,512,256,128,128,32,16,8,16,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,512,256,128,128,32,16,8,16,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f92 (wi (([0,0,0,512,256,128,128,32,16,8,16,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,512,256,128,128,32,16,8,16,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower92 (s : Nat) (h : HasCircuitSize 14 f92 s) : 12 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f92 6 s
    (dep92 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower88
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,6,7,0,4,5,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f92 (Function.update (x ∘ ren) 6 false)) = f88 := by
      funext x
      rw [d92, d88, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f92 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower91
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,4,7,5,6,0,1,2,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f92 (Function.update (x ∘ ren) 6 true)) = f91 := by
      funext x
      rw [d92, d91, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f92 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f93 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || (x 5 && x 6) || (x 7 && x 8)
def cs93 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[5,6],[7,8]]
lemma d93 (x : Fin 14 → Bool) : f93 x = dnf cs93 x := by
  simp [f93, cs93, dnf]
  <;> ac_rfl
def T93 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup93 (x y : Fin 14 → Bool) (h : ∀ i ∈ T93, x i = y i) : f93 x = f93 y := by
  simp only [f93, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep93 : ∀ p ∈ T93, Base.Readers.Dep f93 p := by
  have hc : ∀ p : Fin 14, p ∈ T93 → f93 (Function.update (wi (([0,0,0,0,0,64,32,256,128,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,64,32,256,128,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f93 (wi (([0,0,0,0,0,64,32,256,128,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,64,32,256,128,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower93 (s : Nat) (h : HasCircuitSize 14 f93 s) : 8 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f93 T93 dep93 s h
  have ht : T93.card = 9 := by decide +kernel
  omega
def f94 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 6 && x 7) || (x 5 && x 8) || (x 4 && x 9) || (x 7 && x 9) || (x 8 && x 9)
def cs94 : List (List (Fin 14)) := [[0],[1],[2],[3],[6,7],[5,8],[4,9],[7,9],[8,9]]
lemma d94 (x : Fin 14 → Bool) : f94 x = dnf cs94 x := by
  simp [f94, cs94, dnf]
  <;> ac_rfl
def T94 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup94 (x y : Fin 14 → Bool) (h : ∀ i ∈ T94, x i = y i) : f94 x = f94 y := by
  simp only [f94, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep94 : ∀ p ∈ T94, Base.Readers.Dep f94 p := by
  have hc : ∀ p : Fin 14, p ∈ T94 → f94 (Function.update (wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f94 (wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,512,256,128,64,32,16,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower94 (s : Nat) (h : HasCircuitSize 14 f94 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f94 4 s
    (dep94 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower87
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,5,7,8,6,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f94 (Function.update (x ∘ ren) 4 false)) = f87 := by
      funext x
      rw [d94, d87, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f94 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower93
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,4,0,6,8,7,5,2,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f94 (Function.update (x ∘ ren) 4 true)) = f93 := by
      funext x
      rw [d94, d93, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f94 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f95 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 6 && x 8) || (x 5 && x 9) || (x 7 && x 9) || (x 4 && x 10) || (x 7 && x 10) || (x 8 && x 10)
def cs95 : List (List (Fin 14)) := [[0],[1],[2],[3],[6,8],[5,9],[7,9],[4,10],[7,10],[8,10]]
lemma d95 (x : Fin 14 → Bool) : f95 x = dnf cs95 x := by
  simp [f95, cs95, dnf]
  <;> ac_rfl
def T95 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup95 (x y : Fin 14 → Bool) (h : ∀ i ∈ T95, x i = y i) : f95 x = f95 y := by
  simp only [f95, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep95 : ∀ p ∈ T95, Base.Readers.Dep f95 p := by
  have hc : ∀ p : Fin 14, p ∈ T95 → f95 (Function.update (wi (([0,0,0,0,1024,512,256,512,64,32,16,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,1024,512,256,512,64,32,16,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f95 (wi (([0,0,0,0,1024,512,256,512,64,32,16,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,1024,512,256,512,64,32,16,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower95 (s : Nat) (h : HasCircuitSize 14 f95 s) : 12 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f95 5 s
    (dep95 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower94
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,0,5,7,8,6,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f95 (Function.update (x ∘ ren) 5 false)) = f94 := by
      funext x
      rw [d95, d94, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f95 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower91
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,5,0,7,6,8,1,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f95 (Function.update (x ∘ ren) 5 true)) = f91 := by
      funext x
      rw [d95, d91, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f95 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f96 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 6 && x 8) || (x 7 && x 8) || (x 4 && x 9) || (x 5 && x 10) || (x 7 && x 10) || (x 9 && x 10) || (x 3 && x 11) || (x 5 && x 11) || (x 6 && x 11)
def cs96 : List (List (Fin 14)) := [[0],[1],[2],[6,8],[7,8],[4,9],[5,10],[7,10],[9,10],[3,11],[5,11],[6,11]]
lemma d96 (x : Fin 14 → Bool) : f96 x = dnf cs96 x := by
  simp [f96, cs96, dnf]
  <;> ac_rfl
def T96 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup96 (x y : Fin 14 → Bool) (h : ∀ i ∈ T96, x i = y i) : f96 x = f96 y := by
  simp only [f96, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep96 : ∀ p ∈ T96, Base.Readers.Dep f96 p := by
  have hc : ∀ p : Fin 14, p ∈ T96 → f96 (Function.update (wi (([0,0,0,2048,512,1024,256,256,64,16,32,8,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,2048,512,1024,256,256,64,16,32,8,0,0] : List Nat).getD p.val 0)) p)) ≠ f96 (wi (([0,0,0,2048,512,1024,256,256,64,16,32,8,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,2048,512,1024,256,256,64,16,32,8,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower96 (s : Nat) (h : HasCircuitSize 14 f96 s) : 14 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f96 3 s
    (dep96 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower92
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,3,4,6,5,7,9,10,8,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f96 (Function.update (x ∘ ren) 3 false)) = f92 := by
      funext x
      rw [d96, d92, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f96 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower95
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,0,6,4,5,7,9,8,10,1,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f96 (Function.update (x ∘ ren) 3 true)) = f95 := by
      funext x
      rw [d96, d95, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f96 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f97 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 7 && x 9) || (x 8 && x 9) || (x 5 && x 10) || (x 6 && x 10) || (x 8 && x 10) || (x 4 && x 11) || (x 6 && x 11) || (x 7 && x 11)
def cs97 : List (List (Fin 14)) := [[0],[1],[2],[3],[7,9],[8,9],[5,10],[6,10],[8,10],[4,11],[6,11],[7,11]]
lemma d97 (x : Fin 14 → Bool) : f97 x = dnf cs97 x := by
  simp [f97, cs97, dnf]
  <;> ac_rfl
def T97 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup97 (x y : Fin 14 → Bool) (h : ∀ i ∈ T97, x i = y i) : f97 x = f97 y := by
  simp only [f97, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep97 : ∀ p ∈ T97, Base.Readers.Dep f97 p := by
  have hc : ∀ p : Fin 14, p ∈ T97 → f97 (Function.update (wi (([0,0,0,0,2048,1024,1024,512,512,128,32,16,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,2048,1024,1024,512,512,128,32,16,0,0] : List Nat).getD p.val 0)) p)) ≠ f97 (wi (([0,0,0,0,2048,1024,1024,512,512,128,32,16,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,2048,1024,1024,512,512,128,32,16,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower97 (s : Nat) (h : HasCircuitSize 14 f97 s) : 14 ≤ s := by
  by_contra hn
  have hs : s ≤ 13 := by omega
  have hbig : HasCircuitSize 14 f97 (12+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f97 4 false 12
    (dep97 4 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,5,7,6,8,10,9,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f97 (Function.update (x ∘ ren) 4 false)) = f81 := by
    funext x
    rw [d97, d81, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f97 (Function.update (x ∘ ren) 4 false)) _ at hc
  rw [he] at hc
  have := lower81 12 hc
  omega
def f98 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 7 && x 9) || (x 8 && x 9) || (x 4 && x 10) || (x 6 && x 10) || (x 5 && x 11) || (x 6 && x 11) || (x 8 && x 11) || (x 3 && x 12) || (x 5 && x 12) || (x 7 && x 12)
def cs98 : List (List (Fin 14)) := [[0],[1],[2],[7,9],[8,9],[4,10],[6,10],[5,11],[6,11],[8,11],[3,12],[5,12],[7,12]]
lemma d98 (x : Fin 14 → Bool) : f98 x = dnf cs98 x := by
  simp [f98, cs98, dnf]
  <;> ac_rfl
def T98 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup98 (x y : Fin 14 → Bool) (h : ∀ i ∈ T98, x i = y i) : f98 x = f98 y := by
  simp only [f98, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep98 : ∀ p ∈ T98, Base.Readers.Dep f98 p := by
  have hc : ∀ p : Fin 14, p ∈ T98 → f98 (Function.update (wi (([0,0,0,4096,1024,2048,1024,512,512,128,16,32,8,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,4096,1024,2048,1024,512,512,128,16,32,8,0] : List Nat).getD p.val 0)) p)) ≠ f98 (wi (([0,0,0,4096,1024,2048,1024,512,512,128,16,32,8,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,4096,1024,2048,1024,512,512,128,16,32,8,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower98 (s : Nat) (h : HasCircuitSize 14 f98 s) : 16 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f98 4 s
    (dep98 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower96
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,5,9,6,7,8,4,10,11,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f98 (Function.update (x ∘ ren) 4 false)) = f96 := by
      funext x
      rw [d98, d96, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f98 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower97
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,4,0,6,5,7,8,9,0,10,11,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f98 (Function.update (x ∘ ren) 4 true)) = f97 := by
      funext x
      rw [d98, d97, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f98 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f99 (x : Fin 14 → Bool) : Bool := (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 4 && x 6)
def cs99 : List (List (Fin 14)) := [[2,5],[3,5],[4,5],[0,6],[1,6],[4,6]]
lemma d99 (x : Fin 14 → Bool) : f99 x = dnf cs99 x := by
  simp [f99, cs99, dnf]
  <;> ac_rfl
def T99 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup99 (x y : Fin 14 → Bool) (h : ∀ i ∈ T99, x i = y i) : f99 x = f99 y := by
  simp only [f99, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep99 : ∀ p ∈ T99, Base.Readers.Dep f99 p := by
  have hc : ∀ p : Fin 14, p ∈ T99 → f99 (Function.update (wi (([64,64,32,32,32,4,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([64,64,32,32,32,4,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f99 (wi (([64,64,32,32,32,4,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([64,64,32,32,32,4,1,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower99 (s : Nat) (h : HasCircuitSize 14 f99 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f99 T99 dep99 s h
  have ht : T99.card = 7 := by decide +kernel
  omega
def f100 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6)
def cs100 : List (List (Fin 14)) := [[0],[1],[3,5],[4,5],[2,6],[4,6]]
lemma d100 (x : Fin 14 → Bool) : f100 x = dnf cs100 x := by
  simp [f100, cs100, dnf]
  <;> ac_rfl
def T100 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup100 (x y : Fin 14 → Bool) (h : ∀ i ∈ T100, x i = y i) : f100 x = f100 y := by
  simp only [f100, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep100 : ∀ p ∈ T100, Base.Readers.Dep f100 p := by
  have hc : ∀ p : Fin 14, p ∈ T100 → f100 (Function.update (wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f100 (wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,64,32,32,8,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower100 (s : Nat) (h : HasCircuitSize 14 f100 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f100 T100 dep100 s h
  have ht : T100.card = 7 := by decide +kernel
  omega
def f101 (x : Fin 14 → Bool) : Bool := (x 3 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7)
def cs101 : List (List (Fin 14)) := [[3,5],[4,5],[1,6],[2,6],[4,6],[0,7],[2,7],[3,7]]
lemma d101 (x : Fin 14 → Bool) : f101 x = dnf cs101 x := by
  simp [f101, cs101, dnf]
  <;> ac_rfl
def T101 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup101 (x y : Fin 14 → Bool) (h : ∀ i ∈ T101, x i = y i) : f101 x = f101 y := by
  simp only [f101, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep101 : ∀ p ∈ T101, Base.Readers.Dep f101 p := by
  have hc : ∀ p : Fin 14, p ∈ T101 → f101 (Function.update (wi (([128,64,64,32,32,8,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([128,64,64,32,32,8,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f101 (wi (([128,64,64,32,32,8,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([128,64,64,32,32,8,2,1,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower101 (s : Nat) (h : HasCircuitSize 14 f101 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f101 5 s
    (dep101 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 66, by decide +kernel⟩
      · exact ⟨wi 0, wi 8, by decide +kernel⟩) h
  cases b
  · have hh := lower99
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,4,1,2,0,5,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f101 (Function.update (x ∘ ren) 5 false)) = f99 := by
      funext x
      rw [d101, d99, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f101 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower100
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,3,4,0,1,0,5,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f101 (Function.update (x ∘ ren) 5 true)) = f100 := by
      funext x
      rw [d101, d100, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f101 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f102 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def cs102 : List (List (Fin 14)) := [[0],[1],[2],[4,5],[3,6],[5,6]]
lemma d102 (x : Fin 14 → Bool) : f102 x = dnf cs102 x := by
  simp [f102, cs102, dnf]
  <;> ac_rfl
def T102 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup102 (x y : Fin 14 → Bool) (h : ∀ i ∈ T102, x i = y i) : f102 x = f102 y := by
  simp only [f102, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep102 : ∀ p ∈ T102, Base.Readers.Dep f102 p := by
  have hc : ∀ p : Fin 14, p ∈ T102 → f102 (Function.update (wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f102 (wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,64,32,16,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower102 (s : Nat) (h : HasCircuitSize 14 f102 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f102 T102 dep102 s h
  have ht : T102.card = 7 := by decide +kernel
  omega
def f103 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 4 && x 7)
def cs103 : List (List (Fin 14)) := [[0],[1],[4,5],[3,6],[5,6],[2,7],[4,7]]
lemma d103 (x : Fin 14 → Bool) : f103 x = dnf cs103 x := by
  simp [f103, cs103, dnf]
  <;> ac_rfl
def T103 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup103 (x y : Fin 14 → Bool) (h : ∀ i ∈ T103, x i = y i) : f103 x = f103 y := by
  simp only [f103, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep103 : ∀ p ∈ T103, Base.Readers.Dep f103 p := by
  have hc : ∀ p : Fin 14, p ∈ T103 → f103 (Function.update (wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f103 (wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower103 (s : Nat) (h : HasCircuitSize 14 f103 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f103 2 s
    (dep103 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower100
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,3,6,4,5,2,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f103 (Function.update (x ∘ ren) 2 false)) = f100 := by
      funext x
      rw [d103, d100, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f103 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower102
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,0,4,3,6,5,1,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f103 (Function.update (x ∘ ren) 2 true)) = f102 := by
      funext x
      rw [d103, d102, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f103 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f104 (x : Fin 14 → Bool) : Bool := (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 6 && x 8)
def cs104 : List (List (Fin 14)) := [[3,4],[2,5],[4,6],[5,6],[1,7],[2,7],[3,7],[0,8],[1,8],[6,8]]
lemma d104 (x : Fin 14 → Bool) : f104 x = dnf cs104 x := by
  simp [f104, cs104, dnf]
  <;> ac_rfl
def T104 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup104 (x y : Fin 14 → Bool) (h : ∀ i ∈ T104, x i = y i) : f104 x = f104 y := by
  simp only [f104, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep104 : ∀ p ∈ T104, Base.Readers.Dep f104 p := by
  have hc : ∀ p : Fin 14, p ∈ T104 → f104 (Function.update (wi (([256,128,32,16,8,4,16,2,1,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([256,128,32,16,8,4,16,2,1,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f104 (wi (([256,128,32,16,8,4,16,2,1,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([256,128,32,16,8,4,16,2,1,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower104 (s : Nat) (h : HasCircuitSize 14 f104 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f104 5 s
    (dep104 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 24, by decide +kernel⟩
      · exact ⟨wi 0, wi 4, by decide +kernel⟩) h
  cases b
  · have hh := lower101
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,0,3,5,0,4,7,6,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f104 (Function.update (x ∘ ren) 5 false)) = f101 := by
      funext x
      rw [d104, d101, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f104 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower103
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,5,0,7,2,0,1,4,6,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f104 (Function.update (x ∘ ren) 5 true)) = f103 := by
      funext x
      rw [d104, d103, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f104 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f105 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6)
def cs105 : List (List (Fin 14)) := [[0],[3,5],[4,5],[1,6],[2,6],[4,6]]
lemma d105 (x : Fin 14 → Bool) : f105 x = dnf cs105 x := by
  simp [f105, cs105, dnf]
  <;> ac_rfl
def T105 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup105 (x y : Fin 14 → Bool) (h : ∀ i ∈ T105, x i = y i) : f105 x = f105 y := by
  simp only [f105, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep105 : ∀ p ∈ T105, Base.Readers.Dep f105 p := by
  have hc : ∀ p : Fin 14, p ∈ T105 → f105 (Function.update (wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f105 (wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,64,64,32,32,8,2,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower105 (s : Nat) (h : HasCircuitSize 14 f105 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f105 T105 dep105 s h
  have ht : T105.card = 7 := by decide +kernel
  omega
def f106 (x : Fin 14 → Bool) : Bool := x 0 || (x 3 && x 5) || (x 4 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7)
def cs106 : List (List (Fin 14)) := [[0],[3,5],[4,5],[2,6],[4,6],[1,7],[2,7],[3,7]]
lemma d106 (x : Fin 14 → Bool) : f106 x = dnf cs106 x := by
  simp [f106, cs106, dnf]
  <;> ac_rfl
def T106 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup106 (x y : Fin 14 → Bool) (h : ∀ i ∈ T106, x i = y i) : f106 x = f106 y := by
  simp only [f106, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep106 : ∀ p ∈ T106, Base.Readers.Dep f106 p := by
  have hc : ∀ p : Fin 14, p ∈ T106 → f106 (Function.update (wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f106 (wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,128,64,32,32,8,4,2,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower106 (s : Nat) (h : HasCircuitSize 14 f106 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f106 6 s
    (dep106 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower105
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,4,3,5,0,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f106 (Function.update (x ∘ ren) 6 false)) = f105 := by
      funext x
      rw [d106, d105, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f106 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower102
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,2,6,1,3,0,5,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f106 (Function.update (x ∘ ren) 6 true)) = f102 := by
      funext x
      rw [d106, d102, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f106 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f107 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)
def cs107 : List (List (Fin 14)) := [[0],[1],[4,5],[2,6],[3,6],[5,6]]
lemma d107 (x : Fin 14 → Bool) : f107 x = dnf cs107 x := by
  simp [f107, cs107, dnf]
  <;> ac_rfl
def T107 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup107 (x y : Fin 14 → Bool) (h : ∀ i ∈ T107, x i = y i) : f107 x = f107 y := by
  simp only [f107, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep107 : ∀ p ∈ T107, Base.Readers.Dep f107 p := by
  have hc : ∀ p : Fin 14, p ∈ T107 → f107 (Function.update (wi (([0,0,64,64,32,16,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,64,64,32,16,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f107 (wi (([0,0,64,64,32,16,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,64,64,32,16,4,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower107 (s : Nat) (h : HasCircuitSize 14 f107 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f107 T107 dep107 s h
  have ht : T107.card = 7 := by decide +kernel
  omega
def f108 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def cs108 : List (List (Fin 14)) := [[0],[1],[2],[3,6],[4,6],[5,6]]
lemma d108 (x : Fin 14 → Bool) : f108 x = dnf cs108 x := by
  simp [f108, cs108, dnf]
  <;> ac_rfl
def T108 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup108 (x y : Fin 14 → Bool) (h : ∀ i ∈ T108, x i = y i) : f108 x = f108 y := by
  simp only [f108, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep108 : ∀ p ∈ T108, Base.Readers.Dep f108 p := by
  have hc : ∀ p : Fin 14, p ∈ T108 → f108 (Function.update (wi (([0,0,0,64,64,64,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,64,64,64,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f108 (wi (([0,0,0,64,64,64,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,64,64,64,8,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower108 (s : Nat) (h : HasCircuitSize 14 f108 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f108 T108 dep108 s h
  have ht : T108.card = 7 := by decide +kernel
  omega
def f109 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7)
def cs109 : List (List (Fin 14)) := [[0],[1],[4,6],[5,6],[2,7],[3,7],[5,7]]
lemma d109 (x : Fin 14 → Bool) : f109 x = dnf cs109 x := by
  simp [f109, cs109, dnf]
  <;> ac_rfl
def T109 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup109 (x y : Fin 14 → Bool) (h : ∀ i ∈ T109, x i = y i) : f109 x = f109 y := by
  simp only [f109, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep109 : ∀ p ∈ T109, Base.Readers.Dep f109 p := by
  have hc : ∀ p : Fin 14, p ∈ T109 → f109 (Function.update (wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f109 (wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,128,64,64,16,4,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower109 (s : Nat) (h : HasCircuitSize 14 f109 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f109 4 s
    (dep109 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower107
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,5,4,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f109 (Function.update (x ∘ ren) 4 false)) = f107 := by
      funext x
      rw [d109, d107, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f109 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower108
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,4,5,0,3,0,6,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f109 (Function.update (x ∘ ren) 4 true)) = f108 := by
      funext x
      rw [d109, d108, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f109 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f110 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 6) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8)
def cs110 : List (List (Fin 14)) := [[0],[4,6],[5,6],[2,7],[3,7],[5,7],[1,8],[3,8],[4,8]]
lemma d110 (x : Fin 14 → Bool) : f110 x = dnf cs110 x := by
  simp [f110, cs110, dnf]
  <;> ac_rfl
def T110 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup110 (x y : Fin 14 → Bool) (h : ∀ i ∈ T110, x i = y i) : f110 x = f110 y := by
  simp only [f110, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep110 : ∀ p ∈ T110, Base.Readers.Dep f110 p := by
  have hc : ∀ p : Fin 14, p ∈ T110 → f110 (Function.update (wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f110 (wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,256,128,128,64,64,16,4,2,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower110 (s : Nat) (h : HasCircuitSize 14 f110 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f110 1 s
    (dep110 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower106
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,3,4,2,6,7,5,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f110 (Function.update (x ∘ ren) 1 false)) = f106 := by
      funext x
      rw [d110, d106, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f110 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower109
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,3,2,4,5,6,7,1,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f110 (Function.update (x ∘ ren) 1 true)) = f109 := by
      funext x
      rw [d110, d109, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f110 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f111 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 0 && x 9) || (x 2 && x 9) || (x 6 && x 9)
def cs111 : List (List (Fin 14)) := [[4,5],[5,6],[2,7],[3,7],[4,7],[1,8],[3,8],[6,8],[0,9],[2,9],[6,9]]
lemma d111 (x : Fin 14 → Bool) : f111 x = dnf cs111 x := by
  simp [f111, cs111, dnf]
  <;> ac_rfl
def T111 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup111 (x y : Fin 14 → Bool) (h : ∀ i ∈ T111, x i = y i) : f111 x = f111 y := by
  simp only [f111, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep111 : ∀ p ∈ T111, Base.Readers.Dep f111 p := by
  have hc : ∀ p : Fin 14, p ∈ T111 → f111 (Function.update (wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f111 (wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower111 (s : Nat) (h : HasCircuitSize 14 f111 s) : 12 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f111 0 s
    (dep111 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 512, by decide +kernel⟩) h
  cases b
  · have hh := lower104
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,3,1,2,5,6,7,8,4,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f111 (Function.update (x ∘ ren) 0 false)) = f104 := by
      funext x
      rw [d111, d104, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f111 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower110
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,3,4,6,5,8,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f111 (Function.update (x ∘ ren) 0 true)) = f110 := by
      funext x
      rw [d111, d110, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f111 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f112 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 4 && x 6) || (x 5 && x 6)
def cs112 : List (List (Fin 14)) := [[0],[1],[2],[3],[4,6],[5,6]]
lemma d112 (x : Fin 14 → Bool) : f112 x = dnf cs112 x := by
  simp [f112, cs112, dnf]
  <;> ac_rfl
def T112 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup112 (x y : Fin 14 → Bool) (h : ∀ i ∈ T112, x i = y i) : f112 x = f112 y := by
  simp only [f112, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep112 : ∀ p ∈ T112, Base.Readers.Dep f112 p := by
  have hc : ∀ p : Fin 14, p ∈ T112 → f112 (Function.update (wi (([0,0,0,0,64,64,16,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,64,64,16,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f112 (wi (([0,0,0,0,64,64,16,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,64,64,16,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower112 (s : Nat) (h : HasCircuitSize 14 f112 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f112 T112 dep112 s h
  have ht : T112.card = 7 := by decide +kernel
  omega
def f113 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7)
def cs113 : List (List (Fin 14)) := [[0],[1],[2],[4,6],[5,6],[3,7],[5,7]]
lemma d113 (x : Fin 14 → Bool) : f113 x = dnf cs113 x := by
  simp [f113, cs113, dnf]
  <;> ac_rfl
def T113 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup113 (x y : Fin 14 → Bool) (h : ∀ i ∈ T113, x i = y i) : f113 x = f113 y := by
  simp only [f113, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep113 : ∀ p ∈ T113, Base.Readers.Dep f113 p := by
  have hc : ∀ p : Fin 14, p ∈ T113 → f113 (Function.update (wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f113 (wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,128,64,64,16,8,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower113 (s : Nat) (h : HasCircuitSize 14 f113 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f113 3 s
    (dep113 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower102
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,4,6,5,3,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f113 (Function.update (x ∘ ren) 3 false)) = f102 := by
      funext x
      rw [d113, d102, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f113 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower112
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,0,5,4,6,0,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f113 (Function.update (x ∘ ren) 3 true)) = f112 := by
      funext x
      rw [d113, d112, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f113 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f114 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || x 4 || (x 5 && x 6)
def cs114 : List (List (Fin 14)) := [[0],[1],[2],[3],[4],[5,6]]
lemma d114 (x : Fin 14 → Bool) : f114 x = dnf cs114 x := by
  simp [f114, cs114, dnf]
  <;> ac_rfl
def T114 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
lemma sup114 (x y : Fin 14 → Bool) (h : ∀ i ∈ T114, x i = y i) : f114 x = f114 y := by
  simp only [f114, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide)]
lemma dep114 : ∀ p ∈ T114, Base.Readers.Dep f114 p := by
  have hc : ∀ p : Fin 14, p ∈ T114 → f114 (Function.update (wi (([0,0,0,0,0,64,32,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,0,64,32,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f114 (wi (([0,0,0,0,0,64,32,0,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,0,64,32,0,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower114 (s : Nat) (h : HasCircuitSize 14 f114 s) : 6 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f114 T114 dep114 s h
  have ht : T114.card = 7 := by decide +kernel
  omega
def f115 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 5 && x 6) || (x 4 && x 7) || (x 6 && x 7)
def cs115 : List (List (Fin 14)) := [[0],[1],[2],[3],[5,6],[4,7],[6,7]]
lemma d115 (x : Fin 14 → Bool) : f115 x = dnf cs115 x := by
  simp [f115, cs115, dnf]
  <;> ac_rfl
def T115 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup115 (x y : Fin 14 → Bool) (h : ∀ i ∈ T115, x i = y i) : f115 x = f115 y := by
  simp only [f115, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep115 : ∀ p ∈ T115, Base.Readers.Dep f115 p := by
  have hc : ∀ p : Fin 14, p ∈ T115 → f115 (Function.update (wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f115 (wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,128,64,32,16,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower115 (s : Nat) (h : HasCircuitSize 14 f115 s) : 8 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f115 4 s
    (dep115 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower112
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,5,6,4,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f115 (Function.update (x ∘ ren) 4 false)) = f112 := by
      funext x
      rw [d115, d112, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f115 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower114
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,4,0,6,5,1,0,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f115 (Function.update (x ∘ ren) 4 true)) = f114 := by
      funext x
      rw [d115, d114, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f115 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f116 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 6) || (x 4 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 5 && x 8)
def cs116 : List (List (Fin 14)) := [[0],[1],[2],[5,6],[4,7],[6,7],[3,8],[5,8]]
lemma d116 (x : Fin 14 → Bool) : f116 x = dnf cs116 x := by
  simp [f116, cs116, dnf]
  <;> ac_rfl
def T116 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup116 (x y : Fin 14 → Bool) (h : ∀ i ∈ T116, x i = y i) : f116 x = f116 y := by
  simp only [f116, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep116 : ∀ p ∈ T116, Base.Readers.Dep f116 p := by
  have hc : ∀ p : Fin 14, p ∈ T116 → f116 (Function.update (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f116 (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower116 (s : Nat) (h : HasCircuitSize 14 f116 s) : 10 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f116 3 s
    (dep116 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower113
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,4,7,5,6,3,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f116 (Function.update (x ∘ ren) 3 false)) = f113 := by
      funext x
      rw [d116, d113, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f116 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower115
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,0,5,4,7,6,2,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f116 (Function.update (x ∘ ren) 3 true)) = f115 := by
      funext x
      rw [d116, d115, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f116 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f117 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 7) || (x 6 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 1 && x 9) || (x 2 && x 9) || (x 7 && x 9)
def cs117 : List (List (Fin 14)) := [[0],[4,5],[3,6],[5,7],[6,7],[2,8],[3,8],[4,8],[1,9],[2,9],[7,9]]
lemma d117 (x : Fin 14 → Bool) : f117 x = dnf cs117 x := by
  simp [f117, cs117, dnf]
  <;> ac_rfl
def T117 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup117 (x y : Fin 14 → Bool) (h : ∀ i ∈ T117, x i = y i) : f117 x = f117 y := by
  simp only [f117, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep117 : ∀ p ∈ T117, Base.Readers.Dep f117 p := by
  have hc : ∀ p : Fin 14, p ∈ T117 → f117 (Function.update (wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f117 (wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower117 (s : Nat) (h : HasCircuitSize 14 f117 s) : 12 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f117 6 s
    (dep117 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower110
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,1,4,6,0,5,8,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f117 (Function.update (x ∘ ren) 6 false)) = f110 := by
      funext x
      rw [d117, d110, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f117 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower116
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,4,6,0,8,3,0,1,5,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f117 (Function.update (x ∘ ren) 6 true)) = f116 := by
      funext x
      rw [d117, d116, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f117 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f118 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 1 && x 6) || (x 5 && x 7) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 4 && x 9) || (x 0 && x 10) || (x 2 && x 10) || (x 7 && x 10)
def cs118 : List (List (Fin 14)) := [[4,5],[1,6],[5,7],[3,8],[6,8],[7,8],[2,9],[3,9],[4,9],[0,10],[2,10],[7,10]]
lemma d118 (x : Fin 14 → Bool) : f118 x = dnf cs118 x := by
  simp [f118, cs118, dnf]
  <;> ac_rfl
def T118 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup118 (x y : Fin 14 → Bool) (h : ∀ i ∈ T118, x i = y i) : f118 x = f118 y := by
  simp only [f118, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep118 : ∀ p ∈ T118, Base.Readers.Dep f118 p := by
  have hc : ∀ p : Fin 14, p ∈ T118 → f118 (Function.update (wi (([1024,64,512,256,32,16,2,32,8,4,1,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([1024,64,512,256,32,16,2,32,8,4,1,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f118 (wi (([1024,64,512,256,32,16,2,32,8,4,1,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([1024,64,512,256,32,16,2,32,8,4,1,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower118 (s : Nat) (h : HasCircuitSize 14 f118 s) : 14 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f118 1 s
    (dep118 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 64, by decide +kernel⟩) h
  cases b
  · have hh := lower111
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,2,3,4,5,1,6,8,7,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f118 (Function.update (x ∘ ren) 1 false)) = f111 := by
      funext x
      rw [d118, d111, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f118 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower117
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,4,3,6,0,7,5,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f118 (Function.update (x ∘ ren) 1 true)) = f117 := by
      funext x
      rw [d118, d117, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f118 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f119 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 5 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 0 && x 9) || (x 2 && x 9) || (x 6 && x 9)
def cs119 : List (List (Fin 14)) := [[4,5],[5,6],[2,7],[3,7],[4,7],[1,8],[3,8],[6,8],[0,9],[2,9],[6,9]]
lemma d119 (x : Fin 14 → Bool) : f119 x = dnf cs119 x := by
  simp [f119, cs119, dnf]
  <;> ac_rfl
def T119 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup119 (x y : Fin 14 → Bool) (h : ∀ i ∈ T119, x i = y i) : f119 x = f119 y := by
  simp only [f119, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep119 : ∀ p ∈ T119, Base.Readers.Dep f119 p := by
  have hc : ∀ p : Fin 14, p ∈ T119 → f119 (Function.update (wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f119 (wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([512,256,128,128,32,16,32,4,2,1,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower119 (s : Nat) (h : HasCircuitSize 14 f119 s) : 13 ≤ s := by
  by_contra hn
  have hs : s ≤ 12 := by omega
  have hbig : HasCircuitSize 14 f119 (11+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f119 2 false 11
    (dep119 2 (by decide)) ⟨wi 0, wi 48, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,0,2,4,3,7,5,8,6,0,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f119 (Function.update (x ∘ ren) 2 false)) = f48 := by
    funext x
    rw [d119, d48, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f119 (Function.update (x ∘ ren) 2 false)) _ at hc
  rw [he] at hc
  have := lower48 11 hc
  omega
def f120 (x : Fin 14 → Bool) : Bool := x 0 || (x 5 && x 6) || (x 6 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 7 && x 9) || (x 1 && x 10) || (x 3 && x 10) || (x 7 && x 10)
def cs120 : List (List (Fin 14)) := [[0],[5,6],[6,7],[3,8],[4,8],[5,8],[2,9],[4,9],[7,9],[1,10],[3,10],[7,10]]
lemma d120 (x : Fin 14 → Bool) : f120 x = dnf cs120 x := by
  simp [f120, cs120, dnf]
  <;> ac_rfl
def T120 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup120 (x y : Fin 14 → Bool) (h : ∀ i ∈ T120, x i = y i) : f120 x = f120 y := by
  simp only [f120, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep120 : ∀ p ∈ T120, Base.Readers.Dep f120 p := by
  have hc : ∀ p : Fin 14, p ∈ T120 → f120 (Function.update (wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f120 (wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower120 (s : Nat) (h : HasCircuitSize 14 f120 s) : 14 ≤ s := by
  by_contra hn
  have hs : s ≤ 13 := by omega
  have hbig : HasCircuitSize 14 f120 (12+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f120 0 false 12
    (dep120 0 (by decide)) ⟨wi 0, wi 96, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,2,3,4,5,6,7,8,9,0,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f120 (Function.update (x ∘ ren) 0 false)) = f119 := by
    funext x
    rw [d120, d119, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f120 (Function.update (x ∘ ren) 0 false)) _ at hc
  rw [he] at hc
  have := lower119 12 hc
  omega
def f121 (x : Fin 14 → Bool) : Bool := (x 5 && x 6) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 8) || (x 3 && x 9) || (x 4 && x 9) || (x 8 && x 9) || (x 2 && x 10) || (x 3 && x 10) || (x 5 && x 10) || (x 0 && x 11) || (x 2 && x 11) || (x 8 && x 11)
def cs121 : List (List (Fin 14)) := [[5,6],[1,7],[4,7],[6,8],[3,9],[4,9],[8,9],[2,10],[3,10],[5,10],[0,11],[2,11],[8,11]]
lemma d121 (x : Fin 14 → Bool) : f121 x = dnf cs121 x := by
  simp [f121, cs121, dnf]
  <;> ac_rfl
def T121 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup121 (x y : Fin 14 → Bool) (h : ∀ i ∈ T121, x i = y i) : f121 x = f121 y := by
  simp only [f121, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep121 : ∀ p ∈ T121, Base.Readers.Dep f121 p := by
  have hc : ∀ p : Fin 14, p ∈ T121 → f121 (Function.update (wi (([2048,128,1024,512,128,64,32,2,64,8,4,1,0,0] : List Nat).getD p.val 0)) p (!(wi (([2048,128,1024,512,128,64,32,2,64,8,4,1,0,0] : List Nat).getD p.val 0)) p)) ≠ f121 (wi (([2048,128,1024,512,128,64,32,2,64,8,4,1,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([2048,128,1024,512,128,64,32,2,64,8,4,1,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower121 (s : Nat) (h : HasCircuitSize 14 f121 s) : 16 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f121 1 s
    (dep121 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 96, by decide +kernel⟩
      · exact ⟨wi 0, wi 128, by decide +kernel⟩) h
  cases b
  · have hh := lower118
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,2,3,6,4,5,1,7,8,9,10,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f121 (Function.update (x ∘ ren) 1 false)) = f118 := by
      funext x
      rw [d121, d118, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f121 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower120
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,3,4,2,5,6,0,7,9,8,10,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f121 (Function.update (x ∘ ren) 1 true)) = f120 := by
      funext x
      rw [d121, d120, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f121 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f122 (x : Fin 14 → Bool) : Bool := (x 0 && x 5) || (x 5 && x 6) || (x 4 && x 7) || (x 4 && x 8) || (x 3 && x 9) || (x 6 && x 9) || (x 8 && x 9) || (x 2 && x 10) || (x 6 && x 10) || (x 7 && x 10) || (x 1 && x 11) || (x 3 && x 11) || (x 7 && x 11) || (x 1 && x 12) || (x 2 && x 12) || (x 8 && x 12)
def cs122 : List (List (Fin 14)) := [[0,5],[5,6],[4,7],[4,8],[3,9],[6,9],[8,9],[2,10],[6,10],[7,10],[1,11],[3,11],[7,11],[1,12],[2,12],[8,12]]
lemma d122 (x : Fin 14 → Bool) : f122 x = dnf cs122 x := by
  simp [f122, cs122, dnf]
  <;> ac_rfl
def T122 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup122 (x y : Fin 14 → Bool) (h : ∀ i ∈ T122, x i = y i) : f122 x = f122 y := by
  simp only [f122, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep122 : ∀ p ∈ T122, Base.Readers.Dep f122 p := by
  have hc : ∀ p : Fin 14, p ∈ T122 → f122 (Function.update (wi (([32,2048,1024,512,128,1,32,16,16,8,4,2,2,0] : List Nat).getD p.val 0)) p (!(wi (([32,2048,1024,512,128,1,32,16,16,8,4,2,2,0] : List Nat).getD p.val 0)) p)) ≠ f122 (wi (([32,2048,1024,512,128,1,32,16,16,8,4,2,2,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([32,2048,1024,512,128,1,32,16,16,8,4,2,2,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower122 (s : Nat) (h : HasCircuitSize 14 f122 s) : 17 ≤ s := by
  by_contra hn
  have hs : s ≤ 16 := by omega
  have hbig : HasCircuitSize 14 f122 (15+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f122 9 false 15
    (dep122 9 (by decide)) ⟨wi 0, wi 33, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,0,6,7,4,8,5,0,9,11,10,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f122 (Function.update (x ∘ ren) 9 false)) = f121 := by
    funext x
    rw [d122, d121, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f122 (Function.update (x ∘ ren) 9 false)) _ at hc
  rw [he] at hc
  have := lower121 15 hc
  omega
def f123 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 7 && x 9) || (x 8 && x 9) || (x 5 && x 10) || (x 6 && x 10) || (x 8 && x 10) || (x 4 && x 11) || (x 6 && x 11) || (x 7 && x 11) || (x 3 && x 12) || (x 4 && x 12) || (x 5 && x 12)
def cs123 : List (List (Fin 14)) := [[0],[1],[2],[7,9],[8,9],[5,10],[6,10],[8,10],[4,11],[6,11],[7,11],[3,12],[4,12],[5,12]]
lemma d123 (x : Fin 14 → Bool) : f123 x = dnf cs123 x := by
  simp [f123, cs123, dnf]
  <;> ac_rfl
def T123 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup123 (x y : Fin 14 → Bool) (h : ∀ i ∈ T123, x i = y i) : f123 x = f123 y := by
  simp only [f123, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep123 : ∀ p ∈ T123, Base.Readers.Dep f123 p := by
  have hc : ∀ p : Fin 14, p ∈ T123 → f123 (Function.update (wi (([0,0,0,4096,2048,1024,1024,512,512,128,32,16,8,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,4096,2048,1024,1024,512,512,128,32,16,8,0] : List Nat).getD p.val 0)) p)) ≠ f123 (wi (([0,0,0,4096,2048,1024,1024,512,512,128,32,16,8,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,4096,2048,1024,1024,512,512,128,32,16,8,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower123 (s : Nat) (h : HasCircuitSize 14 f123 s) : 16 ≤ s := by
  by_contra hn
  have hs : s ≤ 15 := by omega
  have hbig : HasCircuitSize 14 f123 (14+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f123 4 false 14
    (dep123 4 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,0,4,5,7,6,8,11,9,10,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f123 (Function.update (x ∘ ren) 4 false)) = f42 := by
    funext x
    rw [d123, d42, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f123 (Function.update (x ∘ ren) 4 false)) _ at hc
  rw [he] at hc
  have := lower42 14 hc
  omega
def f124 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 5) || (x 3 && x 6) || (x 2 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def cs124 : List (List (Fin 14)) := [[0],[1],[4,5],[3,6],[2,7],[5,7],[6,7]]
lemma d124 (x : Fin 14 → Bool) : f124 x = dnf cs124 x := by
  simp [f124, cs124, dnf]
  <;> ac_rfl
def T124 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}
lemma sup124 (x y : Fin 14 → Bool) (h : ∀ i ∈ T124, x i = y i) : f124 x = f124 y := by
  simp only [f124, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
lemma dep124 : ∀ p ∈ T124, Base.Readers.Dep f124 p := by
  have hc : ∀ p : Fin 14, p ∈ T124 → f124 (Function.update (wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f124 (wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,64,32,16,8,4,0,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower124 (s : Nat) (h : HasCircuitSize 14 f124 s) : 7 ≤ s := by
  have hc := Base.PermInputs.dep_lower_set 14 f124 T124 dep124 s h
  have ht : T124.card = 8 := by decide +kernel
  omega
def f125 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 5) || (x 3 && x 6) || (x 2 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)
def cs125 : List (List (Fin 14)) := [[0],[1],[4,5],[3,6],[2,7],[5,8],[6,8],[7,8]]
lemma d125 (x : Fin 14 → Bool) : f125 x = dnf cs125 x := by
  simp [f125, cs125, dnf]
  <;> ac_rfl
def T125 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup125 (x y : Fin 14 → Bool) (h : ∀ i ∈ T125, x i = y i) : f125 x = f125 y := by
  simp only [f125, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep125 : ∀ p ∈ T125, Base.Readers.Dep f125 p := by
  have hc : ∀ p : Fin 14, p ∈ T125 → f125 (Function.update (wi (([0,0,128,64,32,16,8,4,32,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,128,64,32,16,8,4,32,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f125 (wi (([0,0,128,64,32,16,8,4,32,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,128,64,32,16,8,4,32,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower125 (s : Nat) (h : HasCircuitSize 14 f125 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f125 2 s
    (dep125 2 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower124
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,0,3,4,5,6,2,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f125 (Function.update (x ∘ ren) 2 false)) = f124 := by
      funext x
      rw [d125, d124, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f125 (Function.update (x ∘ ren) 2 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower3
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,0,3,4,6,7,0,5,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f125 (Function.update (x ∘ ren) 2 true)) = f3 := by
      funext x
      rw [d125, d3, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f125 (Function.update (x ∘ ren) 2 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f126 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || x 3 || (x 6 && x 7) || (x 4 && x 8) || (x 5 && x 8) || (x 7 && x 8)
def cs126 : List (List (Fin 14)) := [[0],[1],[2],[3],[6,7],[4,8],[5,8],[7,8]]
lemma d126 (x : Fin 14 → Bool) : f126 x = dnf cs126 x := by
  simp [f126, cs126, dnf]
  <;> ac_rfl
def T126 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup126 (x y : Fin 14 → Bool) (h : ∀ i ∈ T126, x i = y i) : f126 x = f126 y := by
  simp only [f126, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep126 : ∀ p ∈ T126, Base.Readers.Dep f126 p := by
  have hc : ∀ p : Fin 14, p ∈ T126 → f126 (Function.update (wi (([0,0,0,0,256,256,128,64,16,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,0,256,256,128,64,16,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f126 (wi (([0,0,0,0,256,256,128,64,16,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,0,256,256,128,64,16,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower126 (s : Nat) (h : HasCircuitSize 14 f126 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f126 6 s
    (dep126 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower18
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,3,4,6,0,5,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f126 (Function.update (x ∘ ren) 6 false)) = f18 := by
      funext x
      rw [d126, d18, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f126 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower10
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,3,4,5,6,0,0,7,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f126 (Function.update (x ∘ ren) 6 true)) = f10 := by
      funext x
      rw [d126, d10, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f126 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f127 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 4 && x 6) || (x 5 && x 6) || (x 3 && x 7) || (x 5 && x 7) || (x 2 && x 8) || (x 3 && x 9) || (x 4 && x 9) || (x 8 && x 9)
def cs127 : List (List (Fin 14)) := [[0],[1],[4,6],[5,6],[3,7],[5,7],[2,8],[3,9],[4,9],[8,9]]
lemma d127 (x : Fin 14 → Bool) : f127 x = dnf cs127 x := by
  simp [f127, cs127, dnf]
  <;> ac_rfl
def T127 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup127 (x y : Fin 14 → Bool) (h : ∀ i ∈ T127, x i = y i) : f127 x = f127 y := by
  simp only [f127, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep127 : ∀ p ∈ T127, Base.Readers.Dep f127 p := by
  have hc : ∀ p : Fin 14, p ∈ T127 → f127 (Function.update (wi (([0,0,256,128,64,64,16,8,4,8,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,256,128,64,64,16,8,4,8,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f127 (wi (([0,0,256,128,64,64,16,8,4,8,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,256,128,64,64,16,8,4,8,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower127 (s : Nat) (h : HasCircuitSize 14 f127 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f127 5 s
    (dep127 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower125
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,5,7,0,2,4,6,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f127 (Function.update (x ∘ ren) 5 false)) = f125 := by
      funext x
      rw [d127, d125, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f127 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower126
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,6,4,5,0,1,2,7,8,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f127 (Function.update (x ∘ ren) 5 true)) = f126 := by
      funext x
      rw [d127, d126, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f127 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f128 (x : Fin 14 → Bool) : Bool := (x 3 && x 4) || (x 2 && x 5) || (x 5 && x 6) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 1 && x 9) || (x 2 && x 9) || (x 7 && x 9) || (x 0 && x 10) || (x 6 && x 10) || (x 7 && x 10)
def cs128 : List (List (Fin 14)) := [[3,4],[2,5],[5,6],[4,7],[1,8],[3,8],[6,8],[1,9],[2,9],[7,9],[0,10],[6,10],[7,10]]
lemma d128 (x : Fin 14 → Bool) : f128 x = dnf cs128 x := by
  simp [f128, cs128, dnf]
  <;> ac_rfl
def T128 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup128 (x y : Fin 14 → Bool) (h : ∀ i ∈ T128, x i = y i) : f128 x = f128 y := by
  simp only [f128, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep128 : ∀ p ∈ T128, Base.Readers.Dep f128 p := by
  have hc : ∀ p : Fin 14, p ∈ T128 → f128 (Function.update (wi (([1024,256,32,16,8,4,32,16,2,2,1,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([1024,256,32,16,8,4,32,16,2,2,1,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f128 (wi (([1024,256,32,16,8,4,32,16,2,2,1,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([1024,256,32,16,8,4,32,16,2,2,1,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower128 (s : Nat) (h : HasCircuitSize 14 f128 s) : 13 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f128 5 s
    (dep128 5 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 24, by decide +kernel⟩
      · exact ⟨wi 0, wi 4, by decide +kernel⟩) h
  cases b
  · have hh := lower6
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,2,0,4,5,0,3,6,7,9,8,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f128 (Function.update (x ∘ ren) 5 false)) = f6 := by
      funext x
      rw [d128, d6, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f128 (Function.update (x ∘ ren) 5 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower127
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,7,0,6,4,0,1,9,5,3,8,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f128 (Function.update (x ∘ ren) 5 true)) = f127 := by
      funext x
      rw [d128, d127, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f128 (Function.update (x ∘ ren) 5 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f129 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || x 2 || (x 5 && x 6) || (x 4 && x 7) || (x 6 && x 7) || (x 3 && x 8) || (x 5 && x 8)
def cs129 : List (List (Fin 14)) := [[0],[1],[2],[5,6],[4,7],[6,7],[3,8],[5,8]]
lemma d129 (x : Fin 14 → Bool) : f129 x = dnf cs129 x := by
  simp [f129, cs129, dnf]
  <;> ac_rfl
def T129 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8}
lemma sup129 (x y : Fin 14 → Bool) (h : ∀ i ∈ T129, x i = y i) : f129 x = f129 y := by
  simp only [f129, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide)]
lemma dep129 : ∀ p ∈ T129, Base.Readers.Dep f129 p := by
  have hc : ∀ p : Fin 14, p ∈ T129 → f129 (Function.update (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f129 (wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,0,256,128,64,32,16,8,0,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower129 (s : Nat) (h : HasCircuitSize 14 f129 s) : 9 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f129 3 s
    (dep129 3 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower3
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,2,0,3,6,5,7,4,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f129 (Function.update (x ∘ ren) 3 false)) = f3 := by
      funext x
      rw [d129, d3, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f129 (Function.update (x ∘ ren) 3 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower8
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,0,5,4,7,6,2,0,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f129 (Function.update (x ∘ ren) 3 true)) = f8 := by
      funext x
      rw [d129, d8, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f129 (Function.update (x ∘ ren) 3 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f130 (x : Fin 14 → Bool) : Bool := x 0 || (x 4 && x 5) || (x 3 && x 6) || (x 5 && x 7) || (x 6 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 1 && x 9) || (x 2 && x 9) || (x 7 && x 9)
def cs130 : List (List (Fin 14)) := [[0],[4,5],[3,6],[5,7],[6,7],[2,8],[3,8],[4,8],[1,9],[2,9],[7,9]]
lemma d130 (x : Fin 14 → Bool) : f130 x = dnf cs130 x := by
  simp [f130, cs130, dnf]
  <;> ac_rfl
def T130 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
lemma sup130 (x y : Fin 14 → Bool) (h : ∀ i ∈ T130, x i = y i) : f130 x = f130 y := by
  simp only [f130, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]
lemma dep130 : ∀ p ∈ T130, Base.Readers.Dep f130 p := by
  have hc : ∀ p : Fin 14, p ∈ T130 → f130 (Function.update (wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f130 (wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,512,256,64,32,16,8,32,4,2,0,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower130 (s : Nat) (h : HasCircuitSize 14 f130 s) : 11 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f130 6 s
    (dep130 6 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower14
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,3,1,4,6,0,5,8,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f130 (Function.update (x ∘ ren) 6 false)) = f14 := by
      funext x
      rw [d130, d14, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f130 (Function.update (x ∘ ren) 6 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower129
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,6,1,8,3,0,2,5,7,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f130 (Function.update (x ∘ ren) 6 true)) = f129 := by
      funext x
      rw [d130, d129, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f130 (Function.update (x ∘ ren) 6 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f131 (x : Fin 14 → Bool) : Bool := x 0 || (x 5 && x 6) || (x 6 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 7 && x 9) || (x 1 && x 10) || (x 3 && x 10) || (x 7 && x 10)
def cs131 : List (List (Fin 14)) := [[0],[5,6],[6,7],[3,8],[4,8],[5,8],[2,9],[4,9],[7,9],[1,10],[3,10],[7,10]]
lemma d131 (x : Fin 14 → Bool) : f131 x = dnf cs131 x := by
  simp [f131, cs131, dnf]
  <;> ac_rfl
def T131 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
lemma sup131 (x y : Fin 14 → Bool) (h : ∀ i ∈ T131, x i = y i) : f131 x = f131 y := by
  simp only [f131, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
lemma dep131 : ∀ p ∈ T131, Base.Readers.Dep f131 p := by
  have hc : ∀ p : Fin 14, p ∈ T131 → f131 (Function.update (wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0)) p)) ≠ f131 (wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,1024,512,256,256,64,32,64,8,4,2,0,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower131 (s : Nat) (h : HasCircuitSize 14 f131 s) : 13 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f131 1 s
    (dep131 1 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 1, by decide +kernel⟩
      · exact ⟨wi 0, wi 1, by decide +kernel⟩) h
  cases b
  · have hh := lower130
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,1,4,2,3,6,7,8,9,5,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f131 (Function.update (x ∘ ren) 1 false)) = f130 := by
      funext x
      rw [d131, d130, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f131 (Function.update (x ∘ ren) 1 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower20
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,0,2,3,4,6,7,5,8,9,0,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f131 (Function.update (x ∘ ren) 1 true)) = f20 := by
      funext x
      rw [d131, d20, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f131 (Function.update (x ∘ ren) 1 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f132 (x : Fin 14 → Bool) : Bool := (x 4 && x 5) || (x 5 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 7 && x 9) || (x 1 && x 10) || (x 6 && x 10) || (x 7 && x 10) || (x 0 && x 11) || (x 2 && x 11) || (x 6 && x 11)
def cs132 : List (List (Fin 14)) := [[4,5],[5,7],[3,8],[4,8],[6,8],[2,9],[3,9],[7,9],[1,10],[6,10],[7,10],[0,11],[2,11],[6,11]]
lemma d132 (x : Fin 14 → Bool) : f132 x = dnf cs132 x := by
  simp [f132, cs132, dnf]
  <;> ac_rfl
def T132 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup132 (x y : Fin 14 → Bool) (h : ∀ i ∈ T132, x i = y i) : f132 x = f132 y := by
  simp only [f132, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep132 : ∀ p ∈ T132, Base.Readers.Dep f132 p := by
  have hc : ∀ p : Fin 14, p ∈ T132 → f132 (Function.update (wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0)) p (!(wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0)) p)) ≠ f132 (wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([2048,1024,512,256,32,16,256,32,8,4,2,1,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower132 (s : Nat) (h : HasCircuitSize 14 f132 s) : 15 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f132 0 s
    (dep132 0 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 48, by decide +kernel⟩
      · exact ⟨wi 0, wi 2048, by decide +kernel⟩) h
  cases b
  · have hh := lower128
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,3,1,2,5,7,6,9,8,10,4,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f132 (Function.update (x ∘ ren) 0 false)) = f128 := by
      funext x
      rw [d132, d128, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f132 (Function.update (x ∘ ren) 0 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower131
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,1,3,5,6,4,7,8,10,9,0,0,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f132 (Function.update (x ∘ ren) 0 true)) = f131 := by
      funext x
      rw [d132, d131, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f132 (Function.update (x ∘ ren) 0 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f133 (x : Fin 14 → Bool) : Bool := x 0 || x 1 || (x 5 && x 6) || (x 4 && x 7) || (x 2 && x 8) || (x 6 && x 9) || (x 7 && x 9) || (x 3 && x 10) || (x 8 && x 10) || (x 9 && x 10) || (x 3 && x 11) || (x 4 && x 11) || (x 5 && x 11)
def cs133 : List (List (Fin 14)) := [[0],[1],[5,6],[4,7],[2,8],[6,9],[7,9],[3,10],[8,10],[9,10],[3,11],[4,11],[5,11]]
lemma d133 (x : Fin 14 → Bool) : f133 x = dnf cs133 x := by
  simp [f133, cs133, dnf]
  <;> ac_rfl
def T133 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
lemma sup133 (x y : Fin 14 → Bool) (h : ∀ i ∈ T133, x i = y i) : f133 x = f133 y := by
  simp only [f133, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]
lemma dep133 : ∀ p ∈ T133, Base.Readers.Dep f133 p := by
  have hc : ∀ p : Fin 14, p ∈ T133 → f133 (Function.update (wi (([0,0,256,1024,128,64,32,16,4,64,8,8,0,0] : List Nat).getD p.val 0)) p (!(wi (([0,0,256,1024,128,64,32,16,4,64,8,8,0,0] : List Nat).getD p.val 0)) p)) ≠ f133 (wi (([0,0,256,1024,128,64,32,16,4,64,8,8,0,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([0,0,256,1024,128,64,32,16,4,64,8,8,0,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower133 (s : Nat) (h : HasCircuitSize 14 f133 s) : 15 ≤ s := by
  by_contra hn
  have hs : s ≤ 14 := by omega
  have hbig : HasCircuitSize 14 f133 (13+1) := by
    obtain ⟨C,hc,hz,hv⟩ := h
    exact ⟨C,hc,by omega,hv⟩
  have hc := Base.Forest.one_gate_at 13 f133 4 false 13
    (dep133 4 (by decide)) ⟨wi 0, wi 1, by decide +kernel⟩ hbig
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,1,3,5,0,7,4,2,8,10,9,6,0,0] : List (Fin 14)).getD i.val 0)
  have he : (fun x : Fin 14 → Bool => f133 (Function.update (x ∘ ren) 4 false)) = f50 := by
    funext x
    rw [d133, d50, dnf_pin_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  have hc := Base.PermInputs.relabel_size ren _ _ hc
  change HasCircuitSize 14 (fun x => f133 (Function.update (x ∘ ren) 4 false)) _ at hc
  rw [he] at hc
  have := lower50 13 hc
  omega
def f134 (x : Fin 14 → Bool) : Bool := (x 3 && x 4) || (x 2 && x 5) || (x 4 && x 7) || (x 5 && x 8) || (x 3 && x 9) || (x 6 && x 9) || (x 8 && x 9) || (x 1 && x 10) || (x 7 && x 10) || (x 8 && x 10) || (x 1 && x 11) || (x 2 && x 11) || (x 6 && x 11) || (x 0 && x 12) || (x 6 && x 12) || (x 7 && x 12)
def cs134 : List (List (Fin 14)) := [[3,4],[2,5],[4,7],[5,8],[3,9],[6,9],[8,9],[1,10],[7,10],[8,10],[1,11],[2,11],[6,11],[0,12],[6,12],[7,12]]
lemma d134 (x : Fin 14 → Bool) : f134 x = dnf cs134 x := by
  simp [f134, cs134, dnf]
  <;> ac_rfl
def T134 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
lemma sup134 (x y : Fin 14 → Bool) (h : ∀ i ∈ T134, x i = y i) : f134 x = f134 y := by
  simp only [f134, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide)]
lemma dep134 : ∀ p ∈ T134, Base.Readers.Dep f134 p := by
  have hc : ∀ p : Fin 14, p ∈ T134 → f134 (Function.update (wi (([4096,1024,32,16,8,4,512,16,32,8,2,2,1,0] : List Nat).getD p.val 0)) p (!(wi (([4096,1024,32,16,8,4,512,16,32,8,2,2,1,0] : List Nat).getD p.val 0)) p)) ≠ f134 (wi (([4096,1024,32,16,8,4,512,16,32,8,2,2,1,0] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([4096,1024,32,16,8,4,512,16,32,8,2,2,1,0] : List Nat).getD p.val 0), hc p hp⟩
lemma lower134 (s : Nat) (h : HasCircuitSize 14 f134 s) : 17 ≤ s := by
  obtain ⟨b,t,ht,hc⟩ := Base.PermInputs.gate_elim_at 13 f134 4 s
    (dep134 4 (by decide)) (by
      intro b; cases b
      · exact ⟨wi 0, wi 36, by decide +kernel⟩
      · exact ⟨wi 0, wi 8, by decide +kernel⟩) h
  cases b
  · have hh := lower132
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,4,1,0,5,6,2,7,10,9,8,11,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f134 (Function.update (x ∘ ren) 4 false)) = f132 := by
      funext x
      rw [d134, d132, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f134 (Function.update (x ∘ ren) 4 false)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
  · have hh := lower133
    let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([2,6,7,1,0,4,10,0,11,3,5,9,8,0] : List (Fin 14)).getD i.val 0)
    have he : (fun x : Fin 14 → Bool => f134 (Function.update (x ∘ ren) 4 true)) = f133 := by
      funext x
      rw [d134, d133, dnf_pin_relabel]
      exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
    have hc := Base.PermInputs.relabel_size ren _ _ hc
    change HasCircuitSize 14 (fun x => f134 (Function.update (x ∘ ren) 4 true)) _ at hc
    rw [he] at hc
    have := hh t hc
    omega
def f135 (x : Fin 14 → Bool) : Bool := (x 2 && x 3) || (x 5 && x 6) || (x 4 && x 7) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8) || (x 2 && x 9) || (x 4 && x 9) || (x 5 && x 9) || (x 1 && x 10) || (x 7 && x 10) || (x 1 && x 11) || (x 6 && x 11) || (x 0 && x 12) || (x 5 && x 12) || (x 10 && x 12) || (x 0 && x 13) || (x 4 && x 13) || (x 11 && x 13)
def cs135 : List (List (Fin 14)) := [[2,3],[5,6],[4,7],[3,8],[6,8],[7,8],[2,9],[4,9],[5,9],[1,10],[7,10],[1,11],[6,11],[0,12],[5,12],[10,12],[0,13],[4,13],[11,13]]
lemma d135 (x : Fin 14 → Bool) : f135 x = dnf cs135 x := by
  simp [f135, cs135, dnf]
  <;> ac_rfl
def T135 : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}
lemma sup135 (x y : Fin 14 → Bool) (h : ∀ i ∈ T135, x i = y i) : f135 x = f135 y := by
  simp only [f135, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide)]
lemma dep135 : ∀ p ∈ T135, Base.Readers.Dep f135 p := by
  have hc : ∀ p : Fin 14, p ∈ T135 → f135 (Function.update (wi (([4096,1024,8,4,128,64,32,16,8,4,2,2,1,1] : List Nat).getD p.val 0)) p (!(wi (([4096,1024,8,4,128,64,32,16,8,4,2,2,1,1] : List Nat).getD p.val 0)) p)) ≠ f135 (wi (([4096,1024,8,4,128,64,32,16,8,4,2,2,1,1] : List Nat).getD p.val 0)) := by decide +kernel
  intro p hp
  exact ⟨wi (([4096,1024,8,4,128,64,32,16,8,4,2,2,1,1] : List Nat).getD p.val 0), hc p hp⟩
set_option maxHeartbeats 0 in
lemma lower135 (s : Nat) (h : HasCircuitSize 14 f135 s) : 20 ≤ s := by
  have support : ∀ p, Base.Readers.Dep f135 p → p ∈ T135 :=
    fun p hp => dep_mem_support f135 T135 sup135 p hp
  have hnc : Base.Readers.RestrNC f135 := by
    have check : ∀ (p : Fin 14), p ∈ T135 → ∀ b : Bool, f135 (Function.update (wi 0) p b) ≠ f135 (Function.update (wi (([12,4096,12,1024,96,8,96,4,12,128,12,64,12,32,12,16,12,8,12,4,12,2,12,2,12,1,12,1] : List Nat).getD (p.val*2 + if b then 1 else 0) 0)) p b) := by decide +kernel
    intro p hp b; exact ⟨wi 0, wi (([12,4096,12,1024,96,8,96,4,12,128,12,64,12,32,12,16,12,8,12,4,12,2,12,2,12,1,12,1] : List Nat).getD (p.val*2 + if b then 1 else 0) 0), check p (support p hp) b⟩
  have hnf : Base.Readers.NoFunnel f135 := by
    let w (p q : Fin 14) (a b : Bool) := wi (([0,0,0,0,1024,1024,1024,1024,8,8,8,8,4,4,4,4,128,128,128,128,64,64,64,64,32,32,32,32,16,16,16,16,8,8,8,8,4,4,4,4,2,2,2,2,2,2,2,2,0,0,0,32,0,0,0,16,1024,1024,1024,1024,0,0,0,0,8,8,8,8,4,4,4,4,128,128,128,128,64,64,64,64,32,32,32,32,16,16,16,16,8,8,8,8,4,4,4,4,0,0,0,128,0,0,0,64,1,1,1,1,1,1,1,1,8,8,8,8,8,8,8,8,0,0,0,0,0,0,0,256,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,64,8,8,8,0,0,0,8,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,4,4,4,4,4,4,4,4,0,0,0,256,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,0,0,0,4,16,4,4,4,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,128,128,128,128,128,128,128,128,8,8,8,8,4,4,4,4,0,0,0,0,64,64,64,64,32,32,32,32,0,0,0,256,8,8,8,8,0,0,0,4,2,2,2,2,2,2,2,2,1,1,1,1,0,0,0,1,64,64,64,64,64,64,64,64,8,8,8,8,4,4,4,4,64,64,64,64,0,0,0,0,0,0,0,256,16,16,16,16,8,8,8,8,0,0,0,4,2,2,2,2,2,2,2,2,0,0,0,1,1,1,1,1,32,32,32,32,32,32,32,32,8,8,8,8,4,4,4,4,32,32,32,32,0,0,0,256,0,0,0,0,16,16,16,16,0,0,0,8,4,4,4,4,2,2,2,2,0,0,0,2,1,1,1,1,1,1,1,1,16,16,16,16,16,16,16,16,8,8,8,8,4,4,4,4,0,0,0,256,16,16,16,16,16,16,16,16,0,0,0,0,0,0,0,8,4,4,4,4,0,0,0,2,2,2,2,2,1,1,1,1,1,1,1,1,8,8,8,8,8,8,8,8,64,8,8,8,0,0,0,4,8,8,8,8,8,8,8,8,0,0,0,8,0,0,0,8,0,0,0,0,4,4,4,4,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,4,4,4,4,4,4,4,4,0,0,0,8,16,4,4,4,0,0,0,4,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4,4,0,0,0,0,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,0,0,0,128,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,0,0,0,2,2,2,2,2,2,2,2,2,0,0,0,0,64,2,2,2,0,0,0,1,1,1,1,1,2,2,2,2,0,0,0,64,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,0,0,0,2,2,2,2,2,2,2,2,2,2,2,2,2,64,2,2,2,0,0,0,0,1,1,1,1,0,0,0,1,0,0,0,32,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,1,1,1,1,0,0,0,0,16,1,1,1,0,0,0,16,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,16,1,1,1,0,0,0,0] : List Nat).getD (((p.val*14+q.val)*2 + if a then 1 else 0)*2 + if b then 1 else 0) 0)
    have check : ∀ (p q : Fin 14), p ∈ T135 → q ∈ T135 → p ≠ q → ∀ a b : Bool, ¬ (f135 (Base.Readers.set2 (w p q a b) p (!a) q b) = f135 (Base.Readers.set2 (w p q a b) p a q (!b)) ∧ f135 (Base.Readers.set2 (w p q a b) p a q (!b)) = f135 (Base.Readers.set2 (w p q a b) p (!a) q (!b))) := by decide +kernel
    intro p q hpq hp hq hf
    obtain ⟨a,b,hab⟩ := hf
    exact check p q (support p hp) (support q hq) hpq a b (hab (w p q a b))
  have lo (p : Fin 14) (hp : p ∈ T135) (t : Nat)
      (hc : HasCircuitSize 14 (fun x => f135 (Function.update x p false)) t) : 17 ≤ t := by
    fin_cases p
    · have hh := lower43
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,4,3,10,9,6,5,8,7,11,12,2,1] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 0 false)) = f43 := by
        funext x
        rw [d135, d43, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 0 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower43
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,0,3,4,5,6,9,10,7,8,1,2,12,11] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 1 false)) = f43 := by
        funext x
        rw [d135, d43, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 1 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower73
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,1,0,0,8,9,4,5,12,2,10,11,6,7] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 2 false)) = f73 := by
        funext x
        rw [d135, d73, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 2 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower73
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,3,0,0,4,5,8,9,2,12,6,7,10,11] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 3 false)) = f73 := by
        funext x
        rw [d135, d73, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 3 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower85
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([5,1,6,2,0,9,7,0,11,3,12,10,8,4] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 4 false)) = f85 := by
        funext x
        rw [d135, d85, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 4 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower85
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([5,1,6,2,9,0,0,7,11,3,10,12,4,8] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 5 false)) = f85 := by
        funext x
        rw [d135, d85, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 5 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower85
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,5,2,6,7,0,0,9,3,11,8,4,12,10] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 6 false)) = f85 := by
        funext x
        rw [d135, d85, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 6 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower85
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,5,2,6,0,7,9,0,3,11,4,8,10,12] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 7 false)) = f85 := by
        funext x
        rw [d135, d85, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 7 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower122
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,1,5,0,9,10,2,3,0,6,11,12,7,8] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 8 false)) = f122 := by
        funext x
        rw [d135, d122, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 8 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower122
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([1,4,0,5,2,3,9,10,6,0,7,8,11,12] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 9 false)) = f122 := by
        funext x
        rw [d135, d122, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 9 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower134
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,0,5,2,10,9,6,1,11,8,0,12,3,7] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 10 false)) = f134 := by
        funext x
        rw [d135, d134, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 10 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower134
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([4,0,5,2,9,10,1,6,11,8,12,0,7,3] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 11 false)) = f134 := by
        funext x
        rw [d135, d134, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 11 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower134
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,2,5,6,1,10,9,8,11,3,7,0,12] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 12 false)) = f134 := by
        funext x
        rw [d135, d134, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 12 false)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower134
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,4,2,5,1,6,9,10,8,11,7,3,12,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 13 false)) = f134 := by
        funext x
        rw [d135, d134, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 13 false)) _ at hc
      rw [he] at hc
      exact hh t hc
  have hi (p : Fin 14) (hp : p ∈ T135) (t : Nat)
      (hc : HasCircuitSize 14 (fun x => f135 (Function.update x p true)) t) : 16 ≤ t := by
    fin_cases p
    · have hh := lower52
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,8,6,7,2,3,10,11,9,12,4,5,1,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 0 true)) = f52 := by
        funext x
        rw [d135, d52, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 0 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower52
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([8,0,7,6,10,11,2,3,12,9,0,1,4,5] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 1 true)) = f52 := by
        funext x
        rw [d135, d52, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 1 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower83
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([5,6,0,0,4,3,10,12,2,1,7,8,11,9] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 2 true)) = f83 := by
        funext x
        rw [d135, d83, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 2 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower83
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([6,2,0,0,11,9,4,3,1,5,10,12,8,7] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 3 true)) = f83 := by
        funext x
        rw [d135, d83, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 3 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower98
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,9,4,10,0,5,11,1,6,2,7,8,12,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 4 true)) = f98 := by
        funext x
        rw [d135, d98, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 4 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower98
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,9,4,10,5,0,1,11,6,2,8,7,0,12] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 5 true)) = f98 := by
        funext x
        rw [d135, d98, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 5 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower98
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([9,3,10,4,11,1,0,5,0,6,12,2,7,8] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 6 true)) = f98 := by
        funext x
        rw [d135, d98, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 6 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower98
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([9,3,10,4,0,11,5,0,1,6,2,12,8,7] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 7 true)) = f98 := by
        funext x
        rw [d135, d98, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 7 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower123
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([6,9,3,0,4,5,1,2,0,12,8,7,10,11] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 8 true)) = f123 := by
        funext x
        rw [d135, d123, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 8 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower123
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([9,6,0,3,1,2,4,5,12,0,10,11,8,7] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 9 true)) = f123 := by
        funext x
        rw [d135, d123, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 9 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower123
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,0,7,9,4,6,10,2,8,11,0,5,1,12] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 10 true)) = f123 := by
        funext x
        rw [d135, d123, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 10 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower123
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([3,1,7,9,6,4,2,10,8,11,5,0,12,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 11 true)) = f123 := by
        funext x
        rw [d135, d123, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 11 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower123
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,9,8,11,1,5,6,10,7,2,12,0,4] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 12 true)) = f123 := by
        funext x
        rw [d135, d123, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 12 true)) _ at hc
      rw [he] at hc
      exact hh t hc
    · have hh := lower123
      let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,3,9,8,1,11,6,5,10,7,12,2,4,0] : List (Fin 14)).getD i.val 0)
      have he : (fun x : Fin 14 → Bool => f135 (Function.update (x ∘ ren) 13 true)) = f123 := by
        funext x
        rw [d135, d123, dnf_pin_relabel]
        exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
      have hc := Base.PermInputs.relabel_size ren _ _ hc
      change HasCircuitSize 14 (fun x => f135 (Function.update (x ∘ ren) 13 true)) _ at hc
      rw [he] at hc
      exact hh t hc
  obtain ⟨p,hp,hpays⟩ := Base.Readers.fanout_step 13 f135 s ⟨0, dep135 0 (by decide)⟩ hnc hnf h
  rcases hpays with ⟨⟨t,ht,hc⟩,_⟩ | ⟨⟨t,ht,hc⟩,_⟩ | ⟨_,⟨t,ht,hc⟩⟩
  · have := lo p (support p hp) t hc; omega
  · have := lo p (support p hp) t hc; omega
  · have := hi p (support p hp) t hc; omega
def lowerTarget9811 (x : Fin 14 → Bool) : Bool := (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8) || (x 5 && x 9) || (x 6 && x 9) || (x 0 && x 10) || (x 4 && x 10) || (x 5 && x 10) || (x 3 && x 11) || (x 4 && x 11) || (x 6 && x 11) || (x 2 && x 12) || (x 3 && x 12) || (x 5 && x 12) || (x 1 && x 13) || (x 2 && x 13) || (x 4 && x 13)
def cstarget : List (List (Fin 14)) := [[1,7],[3,7],[0,8],[2,8],[6,8],[5,9],[6,9],[0,10],[4,10],[5,10],[3,11],[4,11],[6,11],[2,12],[3,12],[5,12],[1,13],[2,13],[4,13]]
lemma dtarget (x : Fin 14 → Bool) : lowerTarget9811 x = dnf cstarget x := by
  simp [lowerTarget9811, cstarget, dnf]
  <;> ac_rfl
lemma lowerBound20 (s : Nat) (h : HasCircuitSize 14 lowerTarget9811 s) : 20 ≤ s := by
  let ren : Fin 14 → Fin 14 := (fun i : Fin 14 => ([0,2,4,8,5,10,11,3,13,1,12,6,7,9] : List (Fin 14)).getD i.val 0)
  have hh := Base.PermInputs.relabel_size ren lowerTarget9811 s h
  have he : (fun x : Fin 14 → Bool => lowerTarget9811 (x ∘ ren)) = f135 := by
    funext x
    rw [dtarget, d135, dnf_relabel]
    exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x
  rw [he] at hh
  exact lower135 s hh
end PEqualNP.Outside.L_meta_9811_aux

namespace PEqualNP.Outside.L_meta_9811

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeFn (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 13) ||
  (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) ||
  (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) ||
  (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) ||
  (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)

def starCircuit : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.and, [0, 14]⟩,
    ⟨.or, [7, 13]⟩, ⟨.and, [1, 16]⟩,
    ⟨.or, [8, 12]⟩, ⟨.or, [18, 13]⟩, ⟨.and, [2, 19]⟩,
    ⟨.or, [7, 11]⟩, ⟨.or, [21, 12]⟩, ⟨.and, [3, 22]⟩,
    ⟨.or, [10, 11]⟩, ⟨.or, [24, 13]⟩, ⟨.and, [4, 25]⟩,
    ⟨.or, [9, 10]⟩, ⟨.or, [27, 12]⟩, ⟨.and, [5, 28]⟩,
    ⟨.or, [8, 9]⟩, ⟨.or, [30, 11]⟩, ⟨.and, [6, 31]⟩,
    ⟨.or, [15, 17]⟩, ⟨.or, [33, 20]⟩, ⟨.or, [34, 23]⟩,
    ⟨.or, [35, 26]⟩, ⟨.or, [36, 29]⟩, ⟨.or, [37, 32]⟩], 38⟩

lemma starCircuit_fanIn : FanInTwo starCircuit := by
  simp [FanInTwo, starCircuit]

lemma starCircuit_size : starCircuit.size = 25 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma starCircuit_eval (x : Fin 14 → Bool) :
    starCircuit.eval (List.ofFn x) = edgeFn x := by
  simp [Circuit.eval, Circuit.wires, starCircuit, GateOp.eval, List.ofFn_succ,
    edgeFn, Bool.and_or_distrib_left, Bool.or_assoc]

lemma upperBound : HasCircuitSize 14 edgeFn 25 :=
  ⟨starCircuit, starCircuit_fanIn, Nat.le_of_eq starCircuit_size, starCircuit_eval⟩

end PEqualNP.Outside.L_meta_9811
