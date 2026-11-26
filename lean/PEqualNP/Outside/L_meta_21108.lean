import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.MetaComplexity


namespace PEqualNP.Outside.L_meta_21108.Logic

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

end PEqualNP.Outside.L_meta_21108.Logic

namespace PEqualNP.Outside.L_meta_21108.Logic

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

end PEqualNP.Outside.L_meta_21108.Logic

namespace PEqualNP.Outside.L_meta_21108.Logic

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

end PEqualNP.Outside.L_meta_21108.Logic

namespace PEqualNP.Outside.L_meta_21108.Transfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_21108.Logic

lemma simplify_mono (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr] at hg <;> (subst hg; simp)

lemma elim_mono (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ (elim n gs acc).2,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_mono _ _ _ (hgs g List.mem_cons_self) g' (by simpa using h1)

lemma monotone_gate_elim (n : ℕ) (C : Circuit) (b : Bool) (s : ℕ)
    (hmono : Monotone2 C) (hsz : C.size ≤ s + 1)
    (hdep : ∃ x : Fin (n + 1) → Bool,
      C.eval (List.ofFn (Function.update x (Fin.last n) (!x (Fin.last n)))) ≠
        C.eval (List.ofFn x))
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧
      ∀ y : Fin n → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  have hsz' : C.gates.length ≤ s + 1 := hsz
  have hnok : ∀ g ∈ C.gates, NOk g := by
    intro g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := (hmono g hg).1
    have hlen := (hmono g hg).2
    refine ⟨⟨?_, hlen⟩, ?_⟩
    · rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hop with h | h <;> rw [h] <;> simp
  have hevg : ∀ x : Fin (n + 1) → Bool,
      (wiresFrom C.gates (List.ofFn x)).getD C.output false = C.eval (List.ofFn x) :=
    fun _ => rfl
  set acc := elim n C.gates (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom C.gates (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) C.gates _ _
      (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ C.gates, n ∈ g.inputs
      · have := elim_len_lt n n C.gates (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ C.gates _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n C.gates (inputSupps (n + 1)) hread
          (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x
          C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, ?_, hlen, ?_⟩
    · exact elim_mono n C.gates (fun g hg => (hmono g hg).1) _ (by simp)
    · intro y
      have := hval y
      rw [hst] at this
      exact this

end PEqualNP.Outside.L_meta_21108.Transfer

namespace PEqualNP.Outside.L_meta_21108.Dependency
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

lemma op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : Le w w')
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hv⟩

lemma append_mono (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y)
    (a b : Bool) (hab : a = true → b = true) : Le (x ++ [a]) (y ++ [b]) := by
  intro i hi
  by_cases h : i < x.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hxy i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
    cases hn : i - x.length with
    | zero => simpa [hn] using hab (by simpa [hn] using hi)
    | succ k => simp [hn, List.getD_eq_getElem?_getD] at hi

lemma wires_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) :
    Le (Circuit.wires ⟨gs, 0⟩ x) (Circuit.wires ⟨gs, 0⟩ y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih (fun g' hg' => hm g' (by simp [hg']))
    · simpa using hl
    · exact append_mono x y hl hxy _ _ (op_mono g (hm g (by simp)) x y hxy)

lemma eval_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (hxy : Le x y) (hx : C.eval x = true) : C.eval y = true :=
  wires_mono C.gates (fun g hg => (hm g hg).1) x y hl hxy C.output hx

lemma dependency (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun (u : Fin 4) (v : Fin 5) => (35067 : Nat).testBit (5*u.val+v.val)) C) :
    ∃ x : Fin 9 → Bool,
      circuitFun 9 C (Function.update x (Fin.last 8) (!x (Fin.last 8))) ≠ circuitFun 9 C x := by
  let x : Fin 9 → Bool := fun i => decide (i.val = 0)
  have hneg : C.eval (oneEach (0 : Fin 4) (2 : Fin 5)) = false := (hr 0 2).trans (by decide)
  have hpos : C.eval (oneEach (0 : Fin 4) (4 : Fin 5)) = true := (hr 0 4).trans (by decide)
  have hxy : Le (List.ofFn x) (oneEach (0 : Fin 4) (2 : Fin 5)) := by
    intro i
    by_cases hi : i < 9
    · interval_cases i <;> decide
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp
  have hbase : C.eval (List.ofFn x) = false := by
    cases he : C.eval (List.ofFn x) with
    | false => rfl
    | true =>
      have ht := eval_mono C hm _ _ (by simp [oneEach]) hxy he
      rw [hneg] at ht
      contradiction
  refine ⟨x, ?_⟩
  have hp : List.ofFn (Function.update x (Fin.last 8) (!x (Fin.last 8))) =
      oneEach (0 : Fin 4) (4 : Fin 5) := by decide
  change C.eval _ ≠ C.eval _
  rw [hp, hpos, hbase]
  decide

lemma restricted_nonconstant (C : Circuit)
    (hr : Represents (fun (u : Fin 4) (v : Fin 5) => (35067 : Nat).testBit (5*u.val+v.val)) C) :
    ∃ y y' : Fin 8 → Bool,
      circuitFun 9 C (Fin.snoc y false) ≠ circuitFun 9 C (Fin.snoc y' false) := by
  let y : Fin 8 → Bool := fun i => decide (i.val = 0 ∨ i.val = 4)
  let y' : Fin 8 → Bool := fun i => decide (i.val = 0 ∨ i.val = 6)
  have hp : List.ofFn (Fin.snoc y false : Fin 9 → Bool) = oneEach (0 : Fin 4) (0 : Fin 5) := by decide
  have hn : List.ofFn (Fin.snoc y' false : Fin 9 → Bool) = oneEach (0 : Fin 4) (2 : Fin 5) := by decide
  refine ⟨y, y', ?_⟩
  change C.eval _ ≠ C.eval _
  rw [hp, hn, hr 0 0, hr 0 2]
  decide

end PEqualNP.Outside.L_meta_21108.Dependency

namespace PEqualNP.Outside.L_meta_21108.Connection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def corePoint (u v : Fin 4) : Fin 8 → Bool :=
  fun i => if i.val < 4 then decide (i.val = u.val) else decide (i.val = 4 + v.val)

def retainedColumn (v : Fin 4) : Fin 5 := ⟨v.val, by omega⟩

lemma corePoint_eq : ∀ u v : Fin 4,
    List.ofFn (corePoint u v) = oneEach u v := by
  decide +kernel

lemma corePoint_snoc_eq : ∀ u v : Fin 4,
    List.ofFn (Fin.snoc (corePoint u v) false : Fin 9 → Bool) =
      oneEach u (retainedColumn v) := by
  decide +kernel

lemma restricted_mask_eq : ∀ u v : Fin 4,
    (35067 : ℕ).testBit (5 * u.val + (retainedColumn v).val) =
      (4731 : ℕ).testBit (4 * u.val + v.val) := by
  decide +kernel

lemma represents_restriction (C D : Circuit)
    (hrepr : Represents (fun (u : Fin 4) (v : Fin 5) =>
      (35067 : ℕ).testBit (5 * u.val + v.val)) C)
    (heval : ∀ y : Fin 8 → Bool,
      D.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false : Fin 9 → Bool))) :
    Represents (fun (u v : Fin 4) => (4731 : ℕ).testBit (4 * u.val + v.val)) D := by
  intro u v
  rw [← corePoint_eq u v, heval, corePoint_snoc_eq u v]
  exact (hrepr u (retainedColumn v)).trans (restricted_mask_eq u v)

end PEqualNP.Outside.L_meta_21108.Connection

namespace PEqualNP.Outside.L_meta_21108.Connection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
lemma transfer :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) =>
      (35067 : ℕ).testBit (5 * u.val + v.val)) 10 →
    RepSizeAtMost (fun (u v : Fin 4) =>
      (4731 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  rintro ⟨C, hmono, hsize, hrepr⟩
  obtain ⟨D, hDmono, hDsize, hDeval⟩ :=
    PEqualNP.Outside.L_meta_21108.Transfer.monotone_gate_elim 8 C false 9 hmono hsize
      (PEqualNP.Outside.L_meta_21108.Dependency.dependency C hmono hrepr)
      (PEqualNP.Outside.L_meta_21108.Dependency.restricted_nonconstant C hrepr)
  exact ⟨D, hDmono, hDsize, represents_restriction C D hrepr hDeval⟩
end PEqualNP.Outside.L_meta_21108.Connection

namespace PEqualNP.Outside.L_meta_21108.Core

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [4, 5]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [8, 6]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [15, 16]⟩], 17⟩

lemma upper :
    RepSizeAtMost (fun u v : Fin 4 => (4731 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  simp [Monotone2, witness]

abbrev Mask := BitVec 16
def target : Mask := 4731
def sources : List Mask := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def allBits : Mask := BitVec.allOnes 16

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def act (isOr : Bool) (x y : Mask) : Mask :=
  if isOr then x ||| y else x &&& y

lemma act_bits (o : Bool) (a b : Mask) (i : Fin 16) :
    (act o a b)[i.val] = if o then a[i.val] || b[i.val] else a[i.val] && b[i.val] := by
  cases o <;> simp [act]

def gateMask (g : Gate) (w : List Mask) : Mask :=
  match g.inputs with
  | [] => if isAnd g.op then allBits else 0
  | [a] => w.getD a 0
  | a :: b :: _ => act (!(isAnd g.op)) (w.getD a 0) (w.getD b 0)

lemma gateMask_bits (g : Gate) (w : List Mask) (i : Fin 16)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    (gateMask g w)[i.val] =
      g.op.eval (g.inputs.map fun a => (w.map (fun v : Mask => v[i.val])).getD a false) := by
  have bitGet (a : ℕ) : (w.getD a 0)[i.val] = (w.map (fun v : Mask => v[i.val])).getD a false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    change (w[a]?.getD (0 : Mask)).getLsbD i.val = _
    generalize w[a]? = q
    cases q <;> simp
  rcases g with ⟨o,l⟩
  simp only at op arity
  rcases op with rfl | rfl <;>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, gateMask, isAnd, ite_true, ite_false,
       Bool.not_true, Bool.not_false, act, GateOp.eval, List.map_cons, List.map_nil,
       List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
       Bool.or_false, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, bitGet] at arity ⊢
  all_goals first
    | omega
    | exact BitVec.getElem_allOnes _ i.isLt
    | simp
  have fromSome (q : Option Mask) :
      (q.getD (0#16)).getLsbD i.val = (q.map (fun v : Mask => v.getLsbD i.val)).getD false := by
    cases q <;> simp
  simp only [← BitVec.getLsbD_eq_getElem i.isLt, fromSome]

def stage (w : List Mask) (g : Gate) := w ++ [gateMask g w]

lemma wireProjection (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List Mask) (i : Fin 16) :
    ((gs.foldl stage w).map (fun v : Mask => v[i.val])) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
        (w.map (fun v : Mask => v[i.val])) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hm => mono h (List.mem_cons_of_mem _ hm))]
    simp only [stage, List.map_append, List.map_cons, List.map_nil]
    rw [gateMask_bits g w i (mono g (by simp)).1 (mono g (by simp)).2]

def row (i : Fin 16) : List Bool :=
  oneEach (⟨i.val / 4, by omega⟩ : Fin 4) (⟨i.val % 4, by omega⟩ : Fin 4)

lemma source_projection : ∀ i : Fin 16, sources.map (fun v : Mask => v[i.val]) = row i := by
  decide

lemma evalMask (C : Circuit) (mono : Monotone2 C) (i : Fin 16) :
    ((C.gates.foldl stage sources).getD C.output 0)[i.val] = C.eval (row i) := by
  rw [Circuit.eval, Circuit.wires, ← source_projection i, ← wireProjection]
  · cases h : (C.gates.foldl stage sources)[C.output]? <;>
      simp [List.getD_eq_getElem?_getD, h]
  · intro g hg
    simpa using mono g hg

lemma evalTarget (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun u v : Fin 4 => (4731 : ℕ).testBit (4*u.val+v.val)) C) :
    (C.gates.foldl stage sources).getD C.output 0 = target := by
  apply BitVec.eq_of_getElem_eq
  intro i ilt
  rw [evalMask C mono ⟨i,ilt⟩]
  change C.eval (oneEach (⟨i / 4, by omega⟩ : Fin 4) (⟨i % 4, by omega⟩ : Fin 4)) = _
  rw [computes]
  have eq : 4*(i/4)+i % 4 = i := by omega
  change (4731 : ℕ).testBit (4 * (i / 4) + i % 4) = _
  rw [eq]
  rfl

inductive Build : Finset Mask → ℕ → Prop
  | done {W} : target ∈ W → Build W 0
  | advance {W a b o k} : a ∈ W → b ∈ W → act o a b ∉ W →
      act o a b ≠ 0 → act o a b ≠ allBits →
      Build (insert (act o a b) W) k → Build W (k+1)

lemma basicGate (g : Gate) (w : List Mask)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    gateMask g w = 0 ∨ gateMask g w = allBits ∨ gateMask g w ∈ w ∨
      ∃ a ∈ w, ∃ b ∈ w, ∃ o : Bool, gateMask g w = act o a b := by
  have getMem (j : ℕ) : w.getD j 0 = 0 ∨ w.getD j 0 ∈ w := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : w[j]? with
    | none => simp
    | some v => exact Or.inr (List.mem_of_getElem? h)
  rcases g with ⟨op', l⟩
  change op' = .and ∨ op' = .or at op
  change l.length ≤ 2 at arity
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  · rcases op with rfl | rfl <;> simp [gateMask, isAnd]
  · rcases getMem a with z | m
    · exact Or.inl z
    · exact Or.inr (Or.inr (Or.inl m))
  · simp only [gateMask]
    rcases getMem a with ha | ha <;> rcases getMem b with hb | hb
    · rw [ha,hb]
      rcases op with rfl | rfl <;> simp [act, isAnd]
    · rw [ha]
      rcases op with rfl | rfl
      · simp [act, isAnd]
      · exact Or.inr (Or.inr (Or.inl (by
        change ((0 : Mask) ||| w.getD b 0) ∈ w
        rw [show (0 : Mask) ||| w.getD b 0 = w.getD b 0 from BitVec.zero_or]
        exact hb)))
    · rw [hb]
      rcases op with rfl | rfl
      · simp [act, isAnd]
      · exact Or.inr (Or.inr (Or.inl (by
        change (w.getD a 0 ||| (0 : Mask)) ∈ w
        rw [show w.getD a 0 ||| (0 : Mask) = w.getD a 0 from BitVec.or_zero]
        exact ha)))
    · exact Or.inr (Or.inr (Or.inr ⟨_,ha,_,hb,_,rfl⟩))
  · simp at arity

lemma buildFrom (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List Mask) (W : Finset Mask)
    (inv : ∀ v ∈ w, v = 0 ∨ v = allBits ∨ v ∈ W)
    (endMem : target ∈ gs.foldl stage w) :
    ∃ k ≤ gs.length, Build W k := by
  induction gs generalizing w W with
  | nil =>
    have h : target ∈ w := endMem
    rcases inv target h with z | t | mem
    · contradiction
    · contradiction
    · exact ⟨0, by simp, .done mem⟩
  | cons g gs ih =>
    have mono' : ∀ h ∈ gs, (h.op = .and ∨ h.op = .or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => mono h (List.mem_cons_of_mem _ hh)
    by_cases already : gateMask g w = 0 ∨ gateMask g w = allBits ∨ gateMask g w ∈ W
    · have extend : ∀ v ∈ stage w g, v = 0 ∨ v = allBits ∨ v ∈ W := by
        intro v hv
        simp only [stage, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact inv _ hv
        · exact already
      obtain ⟨k,hk,b⟩ := ih mono' _ W extend endMem
      exact ⟨k, by simp; omega, b⟩
    · obtain ⟨a,ha,b,hb,o,eq⟩ : ∃ a ∈ w, ∃ b ∈ w, ∃ o : Bool,
          gateMask g w = act o a b := by
        have gate := mono g (by simp)
        rcases basicGate g w gate.1 gate.2 with z | t | mem | ex
        · exact (already (Or.inl z)).elim
        · exact (already (Or.inr (Or.inl t))).elim
        · exact (already (inv _ mem)).elim
        · exact ex
      have hz : act o a b ≠ 0 := fun h => already (Or.inl (eq.trans h))
      have ht : act o a b ≠ allBits := fun h => already (Or.inr (Or.inl (eq.trans h)))
      have hm : act o a b ∉ W := fun h => already (Or.inr (Or.inr (eq ▸ h)))
      have aw : a ∈ W := by
        rcases inv a ha with h | h | h
        · subst a
          cases o
          · exact (hz (by simp [act])).elim
          · have e : gateMask g w = b := eq.trans (by simp [act])
            exact (already (e ▸ inv _ hb)).elim
        · subst a
          cases o
          · have e : gateMask g w = b := eq.trans (by exact BitVec.allOnes_and)
            exact (already (e ▸ inv _ hb)).elim
          · exact (ht (by exact BitVec.allOnes_or)).elim
        · exact h
      have bw : b ∈ W := by
        rcases inv b hb with h | h | h
        · subst b
          cases o
          · exact (hz (by simp [act])).elim
          · have e : gateMask g w = a := eq.trans (by simp [act])
            exact (already (e ▸ inv _ ha)).elim
        · subst b
          cases o
          · have e : gateMask g w = a := eq.trans (by exact BitVec.and_allOnes)
            exact (already (e ▸ inv _ ha)).elim
          · exact (ht (by exact BitVec.or_allOnes)).elim
        · exact h
      have extend : ∀ v ∈ stage w g, v = 0 ∨ v = allBits ∨ v ∈ insert (act o a b) W := by
        intro v hv
        simp only [stage, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact (inv _ hv).imp_right (Or.imp_right (fun h => Finset.mem_insert_of_mem h))
        · simp [eq]
      obtain ⟨k,hk,d⟩ := ih mono' _ _ extend endMem
      exact ⟨k+1, by simpa using hk, .advance aw bw hm hz ht d⟩

lemma representsBuild (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun u v : Fin 4 => (4731 : ℕ).testBit (4*u.val+v.val)) C) :
    ∃ k ≤ C.size, Build sources.toFinset k := by
  have targetOutput := evalTarget C mono computes
  have targetMem : target ∈ C.gates.foldl stage sources := by
    simp only [List.getD_eq_getElem?_getD] at targetOutput
    cases h : (C.gates.foldl stage sources)[C.output]? with
    | none => simp [h, target] at targetOutput
    | some x =>
      simp only [h, Option.getD_some] at targetOutput
      exact targetOutput ▸ List.mem_of_getElem? h
  exact buildFrom C.gates (by intro g hg; simpa using mono g hg) _ _
    (by intro v hv; exact Or.inr (Or.inr (List.mem_toFinset.mpr hv))) targetMem

inductive Reach : Finset Mask → ℕ → Prop
  | done : Reach {target} 0
  | advance {W R a b o k} : a ∈ W → b ∈ W → act o a b ∉ W →
      act o a b ≠ 0 → act o a b ≠ allBits →
      R ⊆ W → W ⊆ insert a (insert b R) →
      Reach (insert (act o a b) R) k → Reach W (k+1)

lemma buildReach {W : Finset Mask} {k : ℕ} (b : Build W k) :
    ∃ U ⊆ W, ∃ j ≤ k, Reach U j := by
  induction b with
  | done h => exact ⟨{target}, by simpa, 0, le_rfl, .done⟩
  | @advance W a b o k aw bw fresh nz nt _ ih =>
    obtain ⟨D, sub, j, jle, reach⟩ := ih
    let v := act o a b
    by_cases hv : v ∈ D
    · let R := D.erase v
      let U := insert a (insert b R)
      have rsub : R ⊆ W := by
        intro x hx
        have xx := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (sub xx.2)).resolve_left xx.1
      have usub : U ⊆ W := Finset.insert_subset_iff.mpr ⟨aw,
        Finset.insert_subset_iff.mpr ⟨bw,rsub⟩⟩
      have dEq : insert v R = D := Finset.insert_erase hv
      refine ⟨U,usub,j+1,Nat.succ_le_succ jle,.advance (R := R) (a := a) (b := b) (o := o) (by simp [U]) (by simp [U])
        (fun h => fresh (usub h)) nz nt (fun x hx => by simp [U,hx]) (by rfl) ?_⟩
      exact dEq ▸ reach
    · refine ⟨D, ?_, j, by omega, reach⟩
      intro x hx
      exact (Finset.mem_insert.mp (sub hx)).resolve_left (fun e => hv (e ▸ hx : act o a b ∈ D))

lemma reachCard {W : Finset Mask} {k : ℕ} (h : Reach W k) : W.card ≤ k+1 := by
  induction h with
  | done => simp
  | @advance W R a b o k _ _ fresh _ _ sub small _ ih =>
    rw [Finset.card_insert_of_notMem (fun h => fresh (sub h))] at ih
    have ub := (Finset.card_le_card small).trans
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _)))
    omega

def Separates (W : Finset Mask) : Prop :=
  ∀ p n : Fin 16, target[p.val] = true → target[n.val] = false →
    ∃ w ∈ W, w[p.val] = true ∧ w[n.val] = false

lemma splitSeparation {o : Bool} {a b : Mask} {p n : Fin 16}
    (yes : (act o a b)[p.val] = true) (no : (act o a b)[n.val] = false) :
    (a[p.val] = true ∧ a[n.val] = false) ∨ (b[p.val] = true ∧ b[n.val] = false) := by
  rw [act_bits] at yes no
  cases o <;> simp_all only [ite_true, ite_false, Bool.false_eq_true,
    Bool.and_eq_true, Bool.and_eq_false_iff, Bool.or_eq_true, Bool.or_eq_false_iff] <;> tauto

lemma reachSeparates {W : Finset Mask} {k : ℕ} (h : Reach W k) : Separates W := by
  intro p n hp hn
  induction h with
  | done => exact ⟨target, by simp, hp, hn⟩
  | @advance W R a b o k am bm _ _ _ sub _ _ ih =>
    obtain ⟨w, hw, yes, no⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | old
    · rcases splitSeparation yes no with h | h
      · exact ⟨a,am,h⟩
      · exact ⟨b,bm,h⟩
    · exact ⟨w,sub old,yes,no⟩

def criticalPairs : List (Fin 16 × Fin 16) :=
  [(0,8), (4,8), (9,13), (12,8), (0,2), (1,2), (6,7), (3,2)]

lemma essentialData : ∀ i : Fin 8,
    let (p,n) := criticalPairs[i.val]'(by exact i.isLt)
    target[p.val] = true ∧ target[n.val] = false ∧
    ∀ j : Fin 8, (sources[j.val]'(by exact j.isLt))[p.val] = true →
      (sources[j.val]'(by exact j.isLt))[n.val] = false → j = i := by
  decide +kernel

lemma allSources (W : Finset Mask) (hW : W ⊆ sources.toFinset)
    (sep : Separates W) : W = sources.toFinset := by
  apply Finset.Subset.antisymm hW
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
  let j : Fin 8 := ⟨i, by simpa [sources] using hi⟩
  have key := essentialData j
  obtain ⟨v, hv, yes, no⟩ := sep _ _ key.1 key.2.1
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp (hW hv))
  let q : Fin 8 := ⟨t, by simpa [sources] using ht⟩
  have equal := key.2.2 q yes no
  have hv' : sources[q.val]'q.isLt ∈ W := hv
  change sources[j.val]'j.isLt ∈ W
  exact (congrArg (fun i : Fin 8 => sources[i.val]'i.isLt) equal) ▸ hv'

def positive (i : Fin 8) : ℕ := ([0,1,3,4,5,6,9,12] : List ℕ)[i.val]'i.isLt
def negative (i : Fin 8) : ℕ := ([2,7,8,10,11,13,14,15] : List ℕ)[i.val]'i.isLt

def active (b : Bool) (w : BitVec 64) : BitVec 64 := if b then w else 0

lemma active_bit (b : Bool) (w : BitVec 64) (i : ℕ) :
    (active b w).getLsbD i = (b && w.getLsbD i) := by cases b <;> simp [active]

def spreadYes (x : Mask) : BitVec 64 :=
  active (x.getLsbD 0) 255 |||
  active (x.getLsbD 1) 65280 |||
  active (x.getLsbD 3) 16711680 |||
  active (x.getLsbD 4) 4278190080 |||
  active (x.getLsbD 5) 1095216660480 |||
  active (x.getLsbD 6) 280375465082880 |||
  active (x.getLsbD 9) 71776119061217280 |||
  active (x.getLsbD 12) 18374686479671623680

def spreadNo (x : Mask) : BitVec 64 :=
  active (!x.getLsbD 2) 72340172838076673 |||
  active (!x.getLsbD 7) 144680345676153346 |||
  active (!x.getLsbD 8) 289360691352306692 |||
  active (!x.getLsbD 10) 578721382704613384 |||
  active (!x.getLsbD 11) 1157442765409226768 |||
  active (!x.getLsbD 13) 2314885530818453536 |||
  active (!x.getLsbD 14) 4629771061636907072 |||
  active (!x.getLsbD 15) 9259542123273814144

def spread (x : Mask) : BitVec 64 := spreadYes x &&& spreadNo x

lemma active_get (b : Bool) (w : BitVec 64) (i : ℕ) (h : i < 64) :
    (active b w)[i] = (b && w[i]) := by
  cases b <;> simp [active]

lemma yes_bit (x : Mask) (i j : Fin 8) :
    (spreadYes x).getLsbD (8*i.val+j.val) = x.getLsbD (positive i) := by
  fin_cases i <;> fin_cases j <;>
    simp [spreadYes, positive, active_bit, active_get, BitVec.getLsbD_or]

lemma no_bit (x : Mask) (i j : Fin 8) :
    (spreadNo x).getLsbD (8*i.val+j.val) = !(x.getLsbD (negative j)) := by
  fin_cases i <;> fin_cases j <;>
    simp [spreadNo, negative, active_bit, active_get, BitVec.getLsbD_or]

def coverage : List Mask → BitVec 64 :=
  List.rec 0 (fun a _ cov => spread a ||| cov)

lemma coverageBit (W : List Mask) (i j : Fin 8) :
    (coverage W).getLsbD (8*i.val+j.val) = true ↔
      ∃ w ∈ W, w.getLsbD (positive i) = true ∧ w.getLsbD (negative j) = false := by
  induction W with
  | nil => simp [coverage]
  | cons a W ih =>
    change ((spread a ||| coverage W).getLsbD (8*i.val+j.val) = true) ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    rw [show (spread a).getLsbD (8*i.val+j.val) =
        (a.getLsbD (positive i) && !a.getLsbD (negative j)) by
      simp only [spread, BitVec.getLsbD_and, yes_bit, no_bit]]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.mem_cons]
    constructor
    · rintro (ha | ⟨v,vm,hv⟩)
      · exact ⟨a,Or.inl rfl,ha⟩
      · exact ⟨v,Or.inr vm,hv⟩
    · rintro ⟨v, rfl | vm, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨v,vm,hv⟩

lemma listedPositions : ∀ i j : Fin 8,
    positive i < 16 ∧ negative j < 16 ∧
      target.getLsbD (positive i) = true ∧ target.getLsbD (negative j) = false := by decide

lemma covered {W : List Mask} (sep : Separates W.toFinset) :
    coverage W = BitVec.allOnes 64 := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  let i : Fin 8 := ⟨k/8, by omega⟩
  let j : Fin 8 := ⟨k % 8, by omega⟩
  have h := listedPositions i j
  have p := h.2.2.1
  have n := h.2.2.2
  rw [BitVec.getLsbD_eq_getElem h.1] at p
  rw [BitVec.getLsbD_eq_getElem h.2.1] at n
  obtain ⟨w,wm,a,b⟩ := sep ⟨positive i,h.1⟩ ⟨negative j,h.2.1⟩ p n
  have hit := (coverageBit W i j).mpr ⟨w,List.mem_toFinset.mp wm,
    by rw [BitVec.getLsbD_eq_getElem h.1]; exact a,
    by rw [BitVec.getLsbD_eq_getElem h.2.1]; exact b⟩
  change (coverage W).getLsbD (8*(k/8)+k % 8) = true at hit
  rw [show 8*(k/8)+k % 8 = k by omega, BitVec.getLsbD_eq_getElem hk] at hit
  rw [hit, BitVec.getElem_allOnes]

lemma act_comm (o : Bool) (a b : Mask) : act o a b = act o b a := by
  cases o <;> simp [act, BitVec.and_comm, BitVec.or_comm]

lemma act_self (o : Bool) (a : Mask) : act o a a = a := by
  cases o <;> simp [act]

inductive Keys where
  | leaf (keys : List ℕ)
  | branch (boundary : ℕ) (left right : Keys)

noncomputable def Keys.all (T : Keys) (test : ℕ → Bool) : Bool :=
  Keys.rec (fun xs => xs.all test) (fun _ _ _ a b => a && b) T

noncomputable def Keys.find (T : Keys) (q : ℕ) : Bool :=
  Keys.rec (fun xs => xs.any (Nat.beq q))
    (fun b _ _ left right => if q < b then left else right) T

lemma searched {T : Keys} {test : ℕ → Bool} {q : ℕ}
    (pass : T.all test = true) (hit : T.find q = true) :
    test q = true := by
  induction T with
  | leaf xs =>
    obtain ⟨k,mem,found⟩ := List.any_eq_true.mp hit
    have eq : q = k := Nat.eq_of_beq_eq_true found
    exact eq ▸ List.all_eq_true.mp pass k mem
  | branch b l r il ir =>
    have passes : l.all test = true ∧ r.all test = true := by simpa only [Keys.all, Keys.rec, Bool.and_eq_true] using pass
    by_cases cut : q < b
    · exact il passes.1 (by simpa [Keys.find, cut] using hit)
    · exact ir passes.2 (by simpa [Keys.find, cut] using hit)

def key (W : List Mask) : ℕ :=
  W.foldr (fun x k => x.toNat + 65536 * k) 1

def decodeFixed : ℕ → ℕ → List Mask :=
  Nat.rec (fun _ => []) (fun _ rec x =>
    if x ≤ 1 then [] else BitVec.ofNat 16 (x % 65536) :: rec (x / 65536))

def decodeKey (x : ℕ) : List Mask := decodeFixed 10 x

def insertW (a : Mask) : List Mask → List Mask :=
  List.rec [a] (fun b bs put => Bool.rec (b :: put) (a :: b :: bs) (Nat.ble a.toNat b.toNat))

def sortW : List Mask → List Mask :=
  List.rec [] (fun a _ ws => insertW a ws)

lemma insertMem (x a : Mask) (ws : List Mask) : x ∈ insertW a ws ↔ x = a ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertW]
  | cons b bs ih =>
    change x ∈ Bool.rec (motive := fun _ => List Mask) (b :: insertW a bs) (a :: b :: bs) (Nat.ble a.toNat b.toNat) ↔ _
    cases Nat.ble a.toNat b.toNat
    · simp only [Bool.rec, List.mem_cons, ih]
      tauto
    · simp [List.mem_cons]

lemma sortFinset (W : List Mask) : (sortW W).toFinset = W.toFinset := by
  ext x
  simp only [List.mem_toFinset]
  induction W with
  | nil => rfl
  | cons w W ih =>
    change x ∈ insertW w (sortW W) ↔ _
    simp only [insertMem, ih, List.mem_cons]

def Rejects (k : ℕ) (T : Keys) : Prop :=
  ∀ q, T.find q = true → ∀ j ≤ k, ¬ Reach (decodeKey q).toFinset j

def automPositions : List (List (Fin 16)) := [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15],[1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11],[1,5,13,9,0,4,12,8,2,6,14,10,3,7,15,11],[4,0,8,12,5,1,9,13,7,3,11,15,6,2,10,14],[4,5,7,6,0,1,3,2,8,9,11,10,12,13,15,14],[5,1,13,9,4,0,12,8,7,3,15,11,6,2,14,10],[5,4,7,6,1,0,3,2,13,12,15,14,9,8,11,10]]

def coord (s : Fin 8) (i : Fin 16) : Fin 16 :=
  (automPositions[s.val]'s.isLt)[i.val]'(by fin_cases s <;> exact i.isLt)

lemma coordInj : ∀ (s : Fin 8) (i j : Fin 16), coord s i = coord s j → i = j := by
  decide +kernel

def remap (s : Fin 8) (x : Mask) : Mask :=
  (BitVec.ofBoolListLE (List.ofFn fun i => x[(coord s i).val])).cast (by simp)

lemma remapBit (s : Fin 8) (x : Mask) (i : Fin 16) :
    (remap s x)[i.val] = x[(coord s i).val] := by
  rw [← BitVec.getLsbD_eq_getElem i.isLt, remap, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]

lemma remapInj (s : Fin 8) : Function.Injective (remap s) := by
  intro x y e
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp (coordInj s)) ⟨j,hj⟩
  have b := congrArg (fun a : Mask => a[i.val]) e
  simpa only [remapBit, hi] using b

lemma remapAct (s : Fin 8) (o : Bool) (a b : Mask) :
    remap s (act o a b) = act o (remap s a) (remap s b) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  change (remap s (act o a b))[(⟨j,hj⟩ : Fin 16).val] =
    (act o (remap s a) (remap s b))[(⟨j,hj⟩ : Fin 16).val]
  let i : Fin 16 := ⟨j,hj⟩
  rw [remapBit s (act o a b) i, act_bits o a b (coord s i), act_bits o _ _ i,
    remapBit s a i, remapBit s b i]

lemma remapFixed :
    ∀ s : Fin 8, remap s target = target ∧ remap s 0 = 0 ∧ remap s allBits = allBits := by
  decide +kernel

lemma mappedReach (s : Fin 8) {W : Finset Mask} {k : ℕ} (h : Reach W k) :
    Reach (W.image (remap s)) k := by
  induction h with
  | done =>
    simpa only [Finset.image_singleton, (remapFixed s).1] using Reach.done
  | @advance W R a b o k am bm fresh nz nt sub bound h ih =>
    have result := remapAct s o a b
    rw [Finset.image_insert, result] at ih
    apply Reach.advance (Finset.mem_image_of_mem _ am) (Finset.mem_image_of_mem _ bm)
      (R := R.image (remap s)) (o := o) _ _ _ (Finset.image_subset_image sub) _ ih
    · rw [← result]
      intro h
      obtain ⟨x,xm,eq⟩ := Finset.mem_image.mp h
      exact fresh ((remapInj s eq) ▸ xm)
    · rw [← result, ← (remapFixed s).2.1]
      exact fun h => nz (remapInj s h)
    · rw [← result, ← (remapFixed s).2.2]
      exact fun h => nt (remapInj s h)
    · simpa only [Finset.image_insert] using Finset.image_subset_image (f := remap s) bound

noncomputable def Keys.findAlias (T : Keys) (q : ℕ) : Bool :=
  Keys.rec (fun xs => xs.any (fun e => Nat.beq q (e / 8)))
    (fun b _ _ left right => Bool.rec right left (Nat.blt q b)) T

lemma searchedAlias {T : Keys} {test : ℕ → Bool} {q : ℕ}
    (pass : T.all test = true) (hit : T.findAlias q = true) :
    ∃ e, e / 8 = q ∧ test e = true := by
  induction T with
  | leaf xs =>
    obtain ⟨e,mem,found⟩ := List.any_eq_true.mp hit
    exact ⟨e,(Nat.eq_of_beq_eq_true found).symm,List.all_eq_true.mp pass e mem⟩
  | branch b l r il ir =>
    have both : l.all test = true ∧ r.all test = true := by
      simpa only [Keys.all, Keys.rec, Bool.and_eq_true] using pass
    cases cut : Nat.blt q b
    · exact ir both.2 (by simpa only [Keys.findAlias, Keys.rec, cut, Bool.rec] using hit)
    · exact il both.1 (by simpa only [Keys.findAlias, Keys.rec, cut, Bool.rec] using hit)

def remapFast (s : Fin 8) (x : Mask) : Mask :=
  match s.val with
  | 0 => (x &&& 65535)
  | 1 => ((x &&& 4096) >>> (9 : ℕ)) ||| ((x &&& 8448) >>> (6 : ℕ)) ||| ((x &&& 16912) >>> (3 : ℕ)) ||| (x &&& 33825) ||| ((x &&& 2114) <<< (3 : ℕ)) ||| ((x &&& 132) <<< (6 : ℕ)) ||| ((x &&& 8) <<< (9 : ℕ))
  | 2 => ((x &&& 8192) >>> (5 : ℕ)) ||| ((x &&& 49152) >>> (4 : ℕ)) ||| ((x &&& 4096) >>> (3 : ℕ)) ||| ((x &&& 34) >>> (1 : ℕ)) ||| (x &&& 204) ||| ((x &&& 17) <<< (1 : ℕ)) ||| ((x &&& 512) <<< (3 : ℕ)) ||| ((x &&& 3072) <<< (4 : ℕ)) ||| ((x &&& 256) <<< (5 : ℕ))
  | 3 => ((x &&& 8192) >>> (11 : ℕ)) ||| ((x &&& 4608) >>> (6 : ℕ)) ||| ((x &&& 16416) >>> (4 : ℕ)) ||| ((x &&& 33026) >>> (1 : ℕ)) ||| ((x &&& 1040) <<< (1 : ℕ)) ||| ((x &&& 64) <<< (3 : ℕ)) ||| ((x &&& 2049) <<< (4 : ℕ)) ||| ((x &&& 132) <<< (6 : ℕ)) ||| ((x &&& 8) <<< (9 : ℕ))
  | 4 => ((x &&& 4096) >>> (9 : ℕ)) ||| ((x &&& 8448) >>> (6 : ℕ)) ||| ((x &&& 32784) >>> (4 : ℕ)) ||| ((x &&& 512) >>> (3 : ℕ)) ||| ((x &&& 2080) >>> (1 : ℕ)) ||| ((x &&& 16513) <<< (1 : ℕ)) ||| ((x &&& 1026) <<< (4 : ℕ)) ||| ((x &&& 72) <<< (6 : ℕ)) ||| ((x &&& 4) <<< (11 : ℕ))
  | 5 => ((x &&& 128) >>> (5 : ℕ)) ||| ((x &&& 48) >>> (4 : ℕ)) ||| ((x &&& 64) >>> (3 : ℕ)) ||| ((x &&& 34816) >>> (1 : ℕ)) ||| (x &&& 13056) ||| ((x &&& 17408) <<< (1 : ℕ)) ||| ((x &&& 8) <<< (3 : ℕ)) ||| ((x &&& 3) <<< (4 : ℕ)) ||| ((x &&& 4) <<< (5 : ℕ))
  | 6 => ((x &&& 8192) >>> (11 : ℕ)) ||| ((x &&& 4608) >>> (6 : ℕ)) ||| ((x &&& 32800) >>> (5 : ℕ)) ||| ((x &&& 256) >>> (1 : ℕ)) ||| (x &&& 18450) ||| ((x &&& 128) <<< (1 : ℕ)) ||| ((x &&& 1025) <<< (5 : ℕ)) ||| ((x &&& 72) <<< (6 : ℕ)) ||| ((x &&& 4) <<< (11 : ℕ))
  | _ => ((x &&& 41120) >>> (5 : ℕ)) ||| ((x &&& 20560) >>> (3 : ℕ)) ||| ((x &&& 2570) <<< (3 : ℕ)) ||| ((x &&& 1285) <<< (5 : ℕ))

lemma remapFast_bit (s : Fin 8) (x : Mask) (j : Fin 16) :
    (remapFast s x).getLsbD j.val = x.getLsbD (coord s j).val := by
  fin_cases s <;> fin_cases j <;>
    simp [remapFast, coord, automPositions, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_and]

lemma remapFast_eq (s : Fin 8) (x : Mask) : remapFast s x = remap s x := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let i : Fin 16 := ⟨j,hj⟩
  calc
    (remapFast s x)[j] = (remapFast s x).getLsbD j := (BitVec.getLsbD_eq_getElem hj).symm
    _ = x.getLsbD (coord s i).val := remapFast_bit s x i
    _ = x[(coord s i).val] := BitVec.getLsbD_eq_getElem (coord s i).isLt
    _ = (remap s x)[j] := (remapBit s x i).symm

noncomputable def checkAlias (T : Keys) (e : ℕ) : Bool :=
  let W := decodeKey (e / 8)
  let V := sortW (W.map (remapFast (Fin.ofNat 8 e)))
  let q := key V
  T.find q && decodeKey q == V

def RejectsAlias (k : ℕ) (T : Keys) : Prop :=
  ∀ q, T.findAlias q = true → ∀ j ≤ k, ¬ Reach (decodeKey q).toFinset j

lemma verifyAliases (k : ℕ) (T U : Keys) (pr : Rejects k T)
    (check : U.all (checkAlias T) = true) : RejectsAlias k U := by
  intro q hit j le reach
  obtain ⟨e,eq,v⟩ := searchedAlias check hit
  simp only [checkAlias, eq, remapFast_eq, Bool.and_eq_true, beq_iff_eq] at v
  obtain ⟨found,eqMatch⟩ := v
  have h := mappedReach (Fin.ofNat 8 e) reach
  apply pr _ found j le
  rw [eqMatch, sortFinset, show remapFast (Fin.ofNat 8 e) = remap (Fin.ofNat 8 e) from funext (remapFast_eq _)]
  have eqSet : ((decodeKey q).map (remap (Fin.ofNat 8 e))).toFinset =
      (decodeKey q).toFinset.image (remap (Fin.ofNat 8 e)) := by
    ext a
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  exact eqSet.symm ▸ h

lemma rejectAliasNil : RejectsAlias 0 (.leaf []) := by intro q h; contradiction

abbrev Wire := ℕ × ℕ × ℕ

def natAct (o : Bool) (a b : ℕ) : ℕ := Bool.rec (Nat.land a b) (Nat.lor a b) o

def fuse (o : Bool) (a b : Wire) : Wire :=
  (natAct o a.1 b.1, natAct o a.2.1 b.2.1, natAct (!o) a.2.2 b.2.2)

def mark (x : ℕ) : Wire :=
  let m := BitVec.ofNat 16 x
  (x, (spreadYes m).toNat, (spreadNo m).toNat)

def coverWire (w : Wire) : ℕ := Nat.land w.2.1 w.2.2
def all64 : ℕ := 18446744073709551615

def stripAB (a b : ℕ) : List Wire → List Wire × ℕ :=
  List.rec ([], 0) (fun w _ p =>
    Bool.rec (w :: p.1, Nat.lor (coverWire w) p.2) p
       (Nat.beq a w.1 || Nat.beq b w.1))

def includeWire (x : Wire) (keep : Bool) (xs : List Wire) : List Wire :=
  Bool.rec xs (x :: xs) keep

def coverExtra (x : Wire) (keep : Bool) (c : ℕ) : ℕ :=
  Bool.rec c (Nat.lor (coverWire x) c) keep

noncomputable def matchKey (T : Keys) (xs : List Wire) : Bool :=
  let sorted := sortW (xs.map (fun w => BitVec.ofNat 16 w.1))
  let q := key sorted
  T.findAlias q && (decodeKey q == sorted)

noncomputable def fastChild (k : ℕ) (T : Keys) (W : List Wire)
    (a b g : Wire) (strip : List Wire × ℕ) (ka kb : Bool) : Bool :=
  let c := Nat.lor (coverWire g) (coverExtra a ka (coverExtra b kb strip.2))
  Bool.rec false
    (let V := g :: includeWire a ka (includeWire b kb strip.1)
     if V.length > k+1 then false
     else if V.any (fun w => Nat.beq w.1 4731) then true
     else if k == 0 then false
     else !(matchKey T V))
    (Nat.beq c all64)

noncomputable def fastAct (k : ℕ) (T : Keys) (W : List Wire)
    (a b : Wire) (strip : List Wire × ℕ) (o : Bool) : Bool :=
  let g := fuse o a b
  Bool.rec
    (fastChild k T W a b g strip false false ||
     fastChild k T W a b g strip false true ||
     fastChild k T W a b g strip true false ||
     fastChild k T W a b g strip true true)
    false (Nat.beq g.1 0 || Nat.beq g.1 65535 || W.any (fun w => Nat.beq w.1 g.1))

noncomputable def fastPair (k : ℕ) (T : Keys) (W : List Wire) (a b : Wire) : Bool :=
  Bool.rec false
    (let strip := stripAB a.1 b.1 W
     fastAct k T W a b strip false || fastAct k T W a b strip true)
    (Nat.blt a.1 b.1)

noncomputable def checkFast (k : ℕ) (T : Keys) (q : ℕ) : Bool :=
  let L := decodeKey q
  let W := L.map (fun w => mark w.toNat)
  decide L.Nodup && !(W.any (fun w => Nat.beq w.1 4731) ||
    W.any (fun a => W.any (fastPair k T W a)))

def marked (m : Mask) : Wire := mark m.toNat

lemma marked_form (m : Mask) :
    marked m = (m.toNat, (spreadYes m).toNat, (spreadNo m).toNat) := by
  simp [marked, mark]

lemma bit64Matrix (k : ℕ) (hk : k < 64) :
    ∃ i j : Fin 8, 8*i.val+j.val = k :=
  ⟨⟨k/8, by omega⟩, ⟨k % 8, by omega⟩, by change 8*(k/8)+k % 8 = k; omega⟩

lemma spreadYesAct (o : Bool) (a b : Mask) :
    spreadYes (act o a b) =
      if o then spreadYes a ||| spreadYes b else spreadYes a &&& spreadYes b := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  obtain ⟨i,j,rfl⟩ := bit64Matrix k hk
  simp only [← BitVec.getLsbD_eq_getElem hk]
  cases o <;> simp only [Bool.false_eq_true, ite_true, ite_false, yes_bit, act,
    BitVec.getLsbD_or, BitVec.getLsbD_and]

lemma spreadNoAct (o : Bool) (a b : Mask) :
    spreadNo (act o a b) =
      if o then spreadNo a &&& spreadNo b else spreadNo a ||| spreadNo b := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  obtain ⟨i,j,rfl⟩ := bit64Matrix k hk
  simp only [← BitVec.getLsbD_eq_getElem hk]
  cases o <;> simp only [Bool.false_eq_true, ite_true, ite_false, no_bit, act,
    BitVec.getLsbD_or, BitVec.getLsbD_and, Bool.not_and, Bool.not_or]

lemma fuse_mark (o : Bool) (a b : Mask) :
    fuse o (marked a) (marked b) = marked (act o a b) := by
  rw [marked_form a, marked_form b, marked_form (act o a b), spreadYesAct, spreadNoAct]
  cases o <;> simp [fuse, natAct, act, BitVec.toNat_and, BitVec.toNat_or]

def coverN : List Wire → ℕ :=
  List.rec 0 (fun w _ c => Nat.lor (coverWire w) c)

lemma cover_marked (L : List Mask) : coverN (L.map marked) = (coverage L).toNat := by
  induction L with
  | nil => rfl
  | cons m L ih =>
    change Nat.lor (coverWire (marked m)) (coverN (L.map marked)) =
      (spread m ||| coverage L).toNat
    rw [ih]
    simp [coverWire, marked_form, spread, BitVec.toNat_and, BitVec.toNat_or]

lemma strip_spec (a b : ℕ) (W : List Wire) :
    (stripAB a b W).1 = W.filter (fun x => !(Nat.beq a x.1 || Nat.beq b x.1)) ∧
    (stripAB a b W).2 = coverN (stripAB a b W).1 := by
  induction W with
  | nil => exact ⟨rfl,rfl⟩
  | cons x W ih =>
    let p := stripAB a b W
    let out := Bool.rec (motive := fun _ => List Wire × ℕ)
      (x :: p.1, Nat.lor (coverWire x) p.2) p (Nat.beq a x.1 || Nat.beq b x.1)
    change out.1 = _ ∧ out.2 = coverN out.1
    cases h : (Nat.beq a x.1 || Nat.beq b x.1)
    · have L : out.1 = x :: p.1 := by simp only [out,h,Bool.rec]
      have c : out.2 = Nat.lor (coverWire x) p.2 := by simp only [out,h,Bool.rec]
      rw [L,c,List.filter_cons, h]
      exact ⟨congrArg (x :: ·) ih.1, congrArg (Nat.lor (coverWire x)) ih.2⟩
    · have L : out.1 = p.1 := by simp only [out,h,Bool.rec]
      have c : out.2 = p.2 := by simp only [out,h,Bool.rec]
      rw [L,c,List.filter_cons,h]
      exact ih

def addIf {α : Type} (a : α) (b : Bool) (L : List α) : List α :=
  Bool.rec L (a :: L) b

lemma addIf_map {α β : Type} (f : α → β) (a : α) (b : Bool) (L : List α) :
    (addIf a b L).map f = addIf (f a) b (L.map f) := by cases b <;> rfl

lemma coverExtra_eq (a : Wire) (b : Bool) (L : List Wire) :
    coverExtra a b (coverN L) = coverN (includeWire a b L) := by cases b <;> rfl

lemma naturalMask (m : Mask) : BitVec.ofNat 16 (marked m).1 = m := by simp [marked_form]
lemma markedNat (m : Mask) : (marked m).1 = m.toNat := by simp [marked_form]

lemma targetMarked (L : List Mask) :
    ((L.map marked).any (fun w => Nat.beq w.1 4731)) = true ↔ target ∈ L := by
  simp only [List.any_eq_true, List.mem_map, target, markedNat]
  constructor
  · rintro ⟨w, ⟨m,hm,rfl⟩,he⟩
    exact (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true he :
      m.toNat = (4731 : Mask).toNat)) ▸ hm
  · intro h
    exact ⟨marked 4731,⟨4731,h,rfl⟩,rfl⟩

lemma match_rejects (k : ℕ) (T : Keys) (pr : RejectsAlias k T) (L : List Mask)
    (j : ℕ) (le : j ≤ k) (reach : Reach L.toFinset j) :
    matchKey T (L.map marked) = false := by
  apply Bool.eq_false_iff.mpr
  have m : ((L.map marked).map (fun w => BitVec.ofNat 16 w.1)) = L := by
    clear reach
    induction L with
    | nil => rfl
    | cons a L ih => simp only [List.map_cons, naturalMask, ih]
  unfold matchKey
  simp only [m, Bool.and_eq_true, beq_iff_eq]
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨found,eq⟩ := h
  apply pr _ found j le
  rwa [eq, sortFinset]

lemma fastChild_true {k : ℕ} {T : Keys} (pr : RejectsAlias k T)
    (W : List Wire) (a b g : Wire) (strip : List Wire × ℕ)
    (ha : strip.2 = coverN strip.1) (ka kb : Bool) (L : List Mask)
    (eq : g :: includeWire a ka (includeWire b kb strip.1) = L.map marked)
    (distinct : L.Nodup) (j : ℕ) (le : j ≤ k) (reach : Reach L.toFinset j) :
    fastChild k T W a b g strip ka kb = true := by
  have m := covered (reachSeparates reach)
  have digest :
      Nat.lor (coverWire g) (coverExtra a ka (coverExtra b kb strip.2)) = all64 := by
    rw [ha, coverExtra_eq, coverExtra_eq]
    change coverN (g :: includeWire a ka (includeWire b kb strip.1)) = all64
    rw [eq, cover_marked, m]
    rfl
  have bound : L.length ≤ k+1 := by
    rw [← List.toFinset_card_of_nodup distinct]
    exact (reachCard reach).trans (by omega)
  unfold fastChild
  simp only [digest, show Nat.beq all64 all64 = true from rfl, Bool.rec, eq, List.length_map,
    bound.not_gt, ite_false]
  by_cases mem : target ∈ L
  · rw [if_pos ((targetMarked L).mpr mem)]
  have lacks : ((L.map marked).any (fun w => Nat.beq w.1 4731)) = false :=
    Bool.eq_false_iff.mpr (fun h => mem ((targetMarked L).mp h))
  have nk : k ≠ 0 := by
    intro z
    have jz : j = 0 := by omega
    subst j
    generalize hs : L.toFinset = U at reach
    cases reach
    apply mem
    apply List.mem_toFinset.mp
    rw [hs]
    exact Finset.mem_singleton_self _
  rw [lacks]
  simp only [Bool.false_eq_true, ite_false, beq_eq_false_iff_ne.mpr nk,
    match_rejects k T pr L j le reach, Bool.not_false]

def withoutAB (L : List Mask) (a b : Mask) : List Mask :=
  L.filter (fun x => !(Nat.beq a.toNat x.toNat || Nat.beq b.toNat x.toNat))

lemma without_mem (L : List Mask) (a b x : Mask) :
    x ∈ withoutAB L a b ↔ x ∈ L ∧ x ≠ a ∧ x ≠ b := by
  simp only [withoutAB, List.mem_filter, Bool.not_eq_true', Bool.or_eq_false_iff,
    show ∀ a b : ℕ, a.beq b = false ↔ a ≠ b from by
      intro a b
      constructor
      · exact Nat.ne_of_beq_eq_false
      · intro ne
        apply Bool.eq_false_iff.mpr
        exact fun eq => ne (Nat.eq_of_beq_eq_true eq),
    show ∀ p q : Mask, p.toNat ≠ q.toNat ↔ p ≠ q from fun p q =>
      not_congr ⟨BitVec.eq_of_toNat_eq, congrArg BitVec.toNat⟩, ne_comm]

lemma strip_marked (L : List Mask) (a b : Mask) :
    (stripAB a.toNat b.toNat (L.map marked)).1 = (withoutAB L a b).map marked := by
  rw [(strip_spec _ _ _).1]
  induction L with
  | nil => rfl
  | cons v L ih =>
    unfold withoutAB at *
    simp only [List.map_cons, List.filter_cons, markedNat, ih]
    split <;> rfl

lemma filteredRest (L : List Mask) (R : Finset Mask) (a b : Mask)
    (am : a ∈ L) (bm : b ∈ L) (ab : a ≠ b) (distinct : L.Nodup)
    (sub : R ⊆ L.toFinset) (bound : L.toFinset ⊆ insert a (insert b R)) :
    let K := addIf a (decide (a ∈ R)) (addIf b (decide (b ∈ R)) (withoutAB L a b))
    K.toFinset = R ∧ K.Nodup ∧ ∀ x ∈ K, x ∈ L := by
  let base := withoutAB L a b
  have baseND : base.Nodup := distinct.filter _
  have offA : a ∉ base := fun h => (without_mem L a b a).mp h |>.2.1 rfl
  have offB : b ∉ base := fun h => (without_mem L a b b).mp h |>.2.2 rfl
  have oldOnly (x : Mask) : x ∈ base → x ∈ R := by
    intro h
    obtain ⟨m,xneA,xneB⟩ := (without_mem L a b x).mp h
    have hm := bound (List.mem_toFinset.mpr m)
    exact (Finset.mem_insert.mp ((Finset.mem_insert.mp hm).resolve_left xneA)).resolve_left xneB
  have ca (x : Mask) (hx : x ∈ R) : x ∈ L := List.mem_toFinset.mp (sub hx)
  change (addIf a _ (addIf b _ base)).toFinset = R ∧ (addIf a _ (addIf b _ base)).Nodup ∧ _
  constructor
  · ext x
    rw [List.mem_toFinset]
    simp only [addIf]
    by_cases aa : a ∈ R <;> by_cases bb : b ∈ R
    all_goals
      simp only [aa, bb, decide_true, decide_false, Bool.rec, List.mem_cons]
      constructor
      · intro h
        first
        | exact oldOnly x h
        | rcases h with rfl | rfl | h <;> first | assumption | exact oldOnly x h
        | rcases h with rfl | h <;> first | assumption | exact oldOnly x h
      · intro hx
        by_cases xa : x = a
        · subst x
          first | exact Or.inl rfl | exact (aa hx).elim
        by_cases xb : x = b
        · subst x
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact (bb hx).elim
        have hb : x ∈ base := (without_mem L a b x).mpr ⟨ca x hx,xa,xb⟩
        first | exact hb | exact Or.inr hb | exact Or.inr (Or.inr hb)
  · by_cases aa : a ∈ R <;> by_cases bb : b ∈ R <;>
      simp only [addIf, aa, bb, decide_true, decide_false, Bool.rec]
    all_goals
      constructor
      · simp [List.nodup_cons, offA, offB, ab, baseND]
      · intro x hx
        try simp only [List.mem_cons] at hx
        first
        | exact ((without_mem L a b x).mp hx).1
        | rcases hx with rfl | rfl | h <;> first | assumption | exact ((without_mem L a b x).mp h).1
        | rcases hx with rfl | h <;> first | assumption | exact ((without_mem L a b x).mp h).1

lemma fastPair_true {k : ℕ} {T : Keys} (pr : RejectsAlias k T)
    (L : List Mask) (R : Finset Mask) (distinct : L.Nodup) (a b : Mask)
    (am : a ∈ L) (bm : b ∈ L) (ord : a.toNat < b.toNat) (o : Bool)
    (fresh : act o a b ∉ L) (nz : act o a b ≠ 0) (nt : act o a b ≠ allBits)
    (sub : R ⊆ L.toFinset) (bound : L.toFinset ⊆ insert a (insert b R))
    (j : ℕ) (le : j ≤ k) (reach : Reach (insert (act o a b) R) j) :
    fastPair k T (L.map marked) (marked a) (marked b) = true := by
  let g := act o a b
  have ab : a ≠ b := fun e => (show ¬ a.toNat < a.toNat from Nat.lt_irrefl _) (e ▸ ord)
  let ka := decide (a ∈ R)
  let kb := decide (b ∈ R)
  let K := addIf a ka (addIf b kb (withoutAB L a b))
  obtain ⟨Kset,Knd,Ksub⟩ := filteredRest L R a b am bm ab distinct sub bound
  let Tgt := g :: K
  have TgtNd : Tgt.Nodup := List.nodup_cons.mpr ⟨fun h => fresh (Ksub _ h),Knd⟩
  have TgtEq : Tgt.toFinset = insert (act o a b) R := by
    rw [show Tgt = g :: K from rfl,List.toFinset_cons]
    rw [Kset]
  have child :=
    fastChild_true pr (L.map marked) (marked a) (marked b) (marked g)
      (stripAB a.toNat b.toNat (L.map marked)) (strip_spec _ _ _).2 ka kb Tgt
      (by rw [strip_marked, show Tgt = g :: K from rfl, List.map_cons]
          change _ = marked g :: (addIf a ka (addIf b kb (withoutAB L a b))).map marked
          simp only [addIf_map]
          cases ka <;> cases kb <;> rfl)
      TgtNd j le (TgtEq.symm ▸ reach)
  have cmp := (Nat.blt_eq.mpr ord : Nat.blt a.toNat b.toNat = true)
  have clear (x : Mask) (hx : g ≠ x) : Nat.beq g.toNat x.toNat = false :=
    beq_eq_false_iff_ne.mpr (fun e => hx (BitVec.eq_of_toNat_eq e))
  have none : ((L.map marked).any (fun w => Nat.beq w.1 g.toNat)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [List.any_eq_true, List.mem_map] at h
    obtain ⟨x,⟨v,vm,rfl⟩,hit⟩ := h
    have n : v.toNat = g.toNat := Nat.eq_of_beq_eq_true hit
    have e : v = g := BitVec.eq_of_toNat_eq n
    apply fresh
    change g ∈ L
    simpa only [e] using vm
  have oneGate : fastAct k T (L.map marked) (marked a) (marked b)
      (stripAB a.toNat b.toNat (L.map marked)) o = true := by
    unfold fastAct
    simp only [fuse_mark, ← show g = act o a b from rfl, markedNat]
    have z : Nat.beq g.toNat 0 = false := clear 0 nz
    have n : Nat.beq g.toNat 65535 = false := clear allBits nt
    simp only [z, n, none, Bool.false_or, Bool.rec]
    cases hka : ka <;> cases hkb : kb
    all_goals
      rw [hka,hkb] at child
      simp only [Bool.or_eq_true]
      first
      | exact Or.inl (Or.inl (Or.inl child))
      | exact Or.inl (Or.inl (Or.inr child))
      | exact Or.inl (Or.inr child)
      | exact Or.inr child
  unfold fastPair
  simp only [markedNat, cmp, Bool.rec]
  cases o
  · rw [Bool.or_eq_true]
    exact Or.inl oneGate
  · rw [Bool.or_eq_true]
    exact Or.inr oneGate

lemma verifyFast (k : ℕ) (T U : Keys) (ih : RejectsAlias k T)
    (ok : U.all (checkFast k T) = true) : Rejects (k+1) U := by
  intro q hit j le reach
  let W := decodeKey q
  have passed := searched ok hit
  let t0 := (W.map marked).any (fun w => Nat.beq w.1 4731)
  let t1 := (W.map marked).any (fun a => (W.map marked).any (fastPair k T (W.map marked) a))
  have record : W.Nodup ∧ (t0 || t1) = false := by
    change (decide W.Nodup && !(t0 || t1)) = true at passed
    simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] using passed
  have noTarget : target ∉ W := fun h => by
    have ht : t0 = true := (targetMarked W).mpr h
    have impossible := record.2
    rw [ht, Bool.true_or] at impossible
    exact Bool.noConfusion impossible
  generalize e : W.toFinset = S at reach
  cases reach with
  | done =>
    exact noTarget (List.mem_toFinset.mp (e.symm ▸ Finset.mem_singleton_self _))
  | @advance _ R a b o t am bm fresh nz nt sub bound prior =>
    have aW : a ∈ W := List.mem_toFinset.mp (e.symm ▸ am)
    have bW : b ∈ W := List.mem_toFinset.mp (e.symm ▸ bm)
    have ab : a ≠ b := by
      rintro rfl
      rw [act_self] at fresh
      exact fresh am
    have ordered (a' b' : Mask) (ap : a' ∈ W) (bp : b' ∈ W)
        (ord : a'.toNat < b'.toNat) (value : act o a' b' = act o a b)
        (bound' : S ⊆ insert a' (insert b' R)) : False := by
      have m : act o a' b' ∉ W := fun x => fresh (by rwa [← value, ← e, List.mem_toFinset])
      have yes := fastPair_true ih W R record.1 a' b' ap bp ord o m
        (value ▸ nz) (value ▸ nt) (e.symm ▸ sub) (e.symm ▸ bound') t (by omega)
        (value ▸ prior)
      have full : t1 = true := List.any_eq_true.mpr ⟨marked a',List.mem_map_of_mem ap,
        List.any_eq_true.mpr ⟨marked b',List.mem_map_of_mem bp,yes⟩⟩
      rw [full, Bool.or_true] at record
      exact Bool.noConfusion record.2
    rcases lt_or_gt_of_ne (fun z : a.toNat = b.toNat =>
      ab (BitVec.eq_of_toNat_eq z)) with lt | gt
    · exact ordered a b aW bW lt rfl bound
    · exact ordered b a bW aW gt (act_comm _ _ _) (by simpa [Finset.insert_comm] using bound)

lemma allBranch (b : ℕ) (l r : Keys) (f : ℕ → Bool) :
    (Keys.branch b l r).all f = (l.all f && r.all f) := rfl

def a0 : Keys := .leaf []
def r1p0 : Keys := .leaf [
]
def r1 : Keys := r1p0

def a1p0 : Keys := .leaf [
]
def a1 : Keys := a1p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr1p0 : r1p0.all (checkFast 0 a0) = true := by
  decide +kernel

lemma badR1 : Rejects 1 r1 :=
  verifyFast 0 a0 r1 rejectAliasNil (by
    unfold r1
    simp only [allBranch, Bool.and_true, goodr1p0])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda1p0 : a1p0.all (checkAlias r1) = true := by
  decide +kernel

lemma badA1 : RejectsAlias 1 a1 :=
  verifyAliases 1 r1 a1 badR1 (by
    unfold a1
    simp only [allBranch, Bool.and_true, gooda1p0])
def r2p0 : Keys := .leaf [
0x1f2621f1900ff,0x1f26a1f1100ff,0x1fafa1771000f]
def r2 : Keys := r2p0

def a2p0 : Keys := .leaf [
0xc47c2b279999c,0xc57c2a2799999,0xc87cafaf91116,0xcc7c23279999b,0xcd7c222799999,0xcffca82f91113,0xcffcb9390007a,0xd915afaf80787,0xf9110fac807fa,0xf9150fa8807fa,0xf9310f8c807f8,0xf9350f88807f8,0xfb378888857d4,0xfb378d8d80785,0xfd7d088883379,0xfd7d0bb880078]
def a2 : Keys := a2p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr2p0 : r2p0.all (checkFast 1 a1) = true := by
  decide +kernel

lemma badR2 : Rejects 2 r2 :=
  verifyFast 1 a1 r2 badA1 (by
    unfold r2
    simp only [allBranch, Bool.and_true, goodr2p0])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda2p0 : a2p0.all (checkAlias r2) = true := by
  decide +kernel

lemma badA2 : RejectsAlias 2 a2 :=
  verifyAliases 2 r2 a2 badR2 (by
    unfold a2
    simp only [allBranch, Bool.and_true, gooda2p0])
def r3p0 : Keys := .leaf [
0x188f856443333000f,0x18f88727211f1000f,0x198f846443333000f,0x1999972720ff0000f]
def r3p1 : Keys := .leaf [
0x199f972720f00000f,0x19af844443333000f,0x1f22211510f0800ff,0x1f22211590f0000ff]
def r3p2 : Keys := .leaf [
0x1f2221f1100f8004f,0x1f2221f1100ff0048,0x1f22288881ff1005f,0x1f22288f81771000f]
def r3p3 : Keys := .leaf [
0x1f26211190f0000ff,0x1f2621f1100f8000f,0x1f2621f1100ff0008,0x1f2621f1900f0000f]
def r3p4 : Keys := .leaf [
0x1f26a1f1100f0000f,0x1f2f288881771000f,0x1f2f288881f71000f,0x1f66611110afa000f]
def r3p5 : Keys := .leaf [
0x1faaa177100f0000f,0x1fafa11110660000f]
def r3 : Keys := .branch 0x1f26211190f0000ff (.branch 0x199f972720f00000f (r3p0) (.branch 0x1f2221f1100f8004f (r3p1) (r3p2))) (.branch 0x1f26a1f1100f0000f (r3p3) (.branch 0x1faaa177100f0000f (r3p4) (r3p5)))

def a3p0 : Keys := .leaf [
0xc4442227999989784,0xc4442327999988784,0xc444282f91110ff8e,0xc4442a27999981786,0xc4442b27999980785,0xc44439390ff88007a,0xc47c2222199989079,0xc47c2227991109889,0xc47c2227999989001,0xc47c232219998807b,0xc47c232799110888c,0xc47c2327999988004,0xc47c282f91110f88b,0xc47c2a22199981079,0xc47c2a2791110988e,0xc47c2a27999981006,0xc47c2aaf991187803,0xc47c2b22199980078,0xc47c2b2791110888c,0xc47c39390f888007a,0xc5442227999988786,0xc5442a27999980785,0xc57c2222199988079,0xc57c2227991108889,0xc57c2227999988001,0xc57c2a2219998007a,0xc57c2a27911108889,0xc7c4282f911108f8e,0xc7c4393908f880078,0xc7fc282f91110888b,0xc7fc3939088880079,0xc804afaf911100786]
def a3p1 : Keys := .leaf [
0xc87ca22211110f8fb,0xc87ca22791110f88e,0xc87ca7a21111088fb,0xc87ca7a791110888e,0xc87caaaa91110787b,0xc87caaaf911107806,0xc87cafaa91110007a,0xcc442227999981784,0xcc442327999980787,0xcc7c222219998107b,0xcc7c222791110988b,0xcc7c2227999981003,0xcc7c2322199980078,0xcc7c232791110888b,0xcc7caaaf911107806,0xcccca82f911107f86,0xccccb93907f800078,0xccfca227991907806,0xccfca82f911107803,0xccfcaa2f911107803,0xccfcb939078000078,0xcd442227999980785,0xcd7c2222199980078,0xcd7c2227911108889,0xcfcca82f911100787,0xcfccb93900780007a,0xcffca82811110007a,0xd915a2220f8f80787,0xd915a2278f8880787,0xd915a7a2088f80785,0xd915a7a7888880784,0xd915aaaa878780785]
def a3p2 : Keys := .leaf [
0xd915aaaf878000785,0xd915afaa80780007f,0xf80011110fac807fb,0xf80011150fa8807fa,0xf80011310f8c807ff,0xf80011350f88807fa,0xf80033378888857d4,0xf80033378d8d80787,0xf800447c333789899,0xf800457d33378888c,0xf800557d088883379,0xf800557d0bb88007a,0xf800557d22278998c,0xf800557d233788889,0xf80411110fa8807fe,0xf80411310f88807fa,0xf807b3330888857d1,0xf807b3330d8d80787,0xf82011110f8c807fb,0xf82011150f88807ff,0xf82411110f88807fb,0xf878555508888337c,0xf87855550bb88007a,0xf911088887a4007f9,0xf911088c87a0007fd,0xf91108a88784007f8,0xf91108ac8780007f8,0xf9110f88807c00278,0xf9110f88807f80240,0xf9110f8c80780027f,0xf9110f8c807f80207,0xf9110fa8807c0007a]
def a3p3 : Keys := .leaf [
0xf9110fa8807f80042,0xf9110fac80780007a,0xf91122220f8f807cd,0xf91122278888857d4,0xf91122278d8d80785,0xf91144440ff8802f8,0xf911447c088883379,0xf911447c0bb880078,0xf915088887a0007f9,0xf91508a88780007fd,0xf9150f8880780027d,0xf9150f88807f80205,0xf9150fa880780007a,0xf915a2220f8f80787,0xf917a2220888857d1,0xf917a2220d8d80785,0xf917a2220f88807d7,0xf917a2220f8d80785,0xf93108888784007fc,0xf931088c8780007f8,0xf9310f88807c00078,0xf9310f88807f80040,0xf9310f8c807800078,0xf93508888780007f9,0xf9350f88807800078,0xf93944440ff88007a,0xf979444408888337c,0xf97944440bb880078,0xf97944440f888037a,0xf97944440fb880078,0xfa2211178888857d1,0xfa2211178d8d80787]
def a3p4 : Keys := .leaf [
0xfa2791110888857d4,0xfa2791110d8d80786,0xfb330888857d00078,0xfb330d8d80780007d,0xfb378888850500784,0xfc44117908888337c,0xfc4411790bb88007a,0xfc7c1111088883379,0xfc7c11110bb88007b,0xfd550888833780785,0xfd550bb8807800078,0xfd7d0888833000078]
def a3 : Keys := .branch 0x1b22b555f0f0000f0 (.branch 0x190f9444422221f1f (a3p0) (a3p1)) (.branch 0x1f2221f5100ff0008 (a3p2) (.branch 0x1f44f222211110afa (a3p3) (a3p4)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr3p0 : r3p0.all (checkFast 2 a2) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr3p1 : r3p1.all (checkFast 2 a2) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr3p2 : r3p2.all (checkFast 2 a2) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr3p3 : r3p3.all (checkFast 2 a2) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr3p4 : r3p4.all (checkFast 2 a2) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr3p5 : r3p5.all (checkFast 2 a2) = true := by
  decide +kernel

lemma badR3 : Rejects 3 r3 :=
  verifyFast 2 a2 r3 badA2 (by
    unfold r3
    simp only [allBranch, Bool.and_true, goodr3p0, goodr3p1, goodr3p2, goodr3p3, goodr3p4, goodr3p5])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda3p0 : a3p0.all (checkAlias r3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda3p1 : a3p1.all (checkAlias r3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda3p2 : a3p2.all (checkAlias r3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda3p3 : a3p3.all (checkAlias r3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda3p4 : a3p4.all (checkAlias r3) = true := by
  decide +kernel

lemma badA3 : RejectsAlias 3 a3 :=
  verifyAliases 3 r3 a3 badR3 (by
    unfold a3
    simp only [allBranch, Bool.and_true, gooda3p0, gooda3p1, gooda3p2, gooda3p3, gooda3p4])
def r4p0 : Keys := .leaf [
0x14f443222111100f8000f,0x14f443222111900f0000f,0x14f44322a111100f0000f,0x188884444333312f0000f]
def r4p1 : Keys := .leaf [
0x1888844443f3312f0000f,0x188885444333302f0000f,0x18888727211f10f00000f,0x188f8322211510f00000f]
def r4p2 : Keys := .leaf [
0x188f8444432221311000f,0x188f8444433331200000f,0x188f8555532230f00000f,0x18f884444323211f1000f]
def r4p3 : Keys := .leaf [
0x198884444333302f0000f,0x198884644333300f0000f,0x198f8666633330f00000f,0x198f9555522220f00000f]
def r4p4 : Keys := .leaf [
0x199f9444432320f00000f,0x199f9545422220f00000f,0x19a884444333300f0000f,0x1b22b4f44111100f0000f]
def r4p5 : Keys := .leaf [
0x1b22b55550f0000f0000f,0x1baaa76661f1100f0000f,0x1f000226211190f0000ff,0x1f000666611110afa000f]
def r4p6 : Keys := .leaf [
0x1f0f0aaaa11110660000f,0x1f22211110f4000f8000f,0x1f22211110f4000ff0008,0x1f22211110f4800f0000f]
def r4p7 : Keys := .leaf [
0x1f22211510f0000f8000f,0x1f22211510f0000ff0008,0x1f22211510f0800f0000f,0x1f22211590f0000f0000f]
def r4p8 : Keys := .leaf [
0x1f2221f1100f00048000f,0x1f2221f1100f0004f0008,0x1f2221f1100ff00400008,0x1f2224444111102f8000f]
def r4p9 : Keys := .leaf [
0x1f222444411110afa000f,0x1f2224444111902f0000f,0x1f2224444131100f8000f,0x1f2224444131900f0000f]
def r4p10 : Keys := .leaf [
0x1f22244441f1100f0000b,0x1f22244441f1100f8000f,0x1f22244441f1100f9000f,0x1f22244441f1f00f00009]
def r4p11 : Keys := .leaf [
0x1f222444c1f1100f8000f,0x1f222444f1f1100f8000f,0x1f2224f441f1100f8000f,0x1f22255551f1100f8000f]
def r4p12 : Keys := .leaf [
0x1f2225f551f1100f8000f,0x1f2228888115102f0000f,0x1f222888811510f0f00ff,0x1f222888811f10f00005f]
def r4p13 : Keys := .leaf [
0x1f2228888177100f0000f,0x1f22288f811110660000f,0x1f22288f811510ff0000f,0x1f22288f811710f00000f]
def r4p14 : Keys := .leaf [
0x1f22288f815510ff0000f,0x1f22288f844441331000f,0x1f22288f8444f1f1100ff,0x1f22288f866661311000f]
def r4p15 : Keys := .leaf [
0x1f22288f866661711000f,0x1f22288f877771f11000f,0x1f2229999555502f0000f,0x1f22a4444111102f0000f]
def r4p16 : Keys := .leaf [
0x1f22a4444131100f0000f,0x1f22a44441f1100f0000f,0x1f22a44441f1100f8000f,0x1f22a44441f1900f0000f]
def r4p17 : Keys := .leaf [
0x1f22a444c1f1100f0000f,0x1f22a444f1f1100f0000f,0x1f22a4f441f1100f0000f,0x1f22a55551f1100f0000f]
def r4p18 : Keys := .leaf [
0x1f22a5f551f1100f0000f,0x1f22a66661f1100f0000f,0x1f22a666e1f1100f0000f,0x1f22b44441f1100f0000f]
def r4p19 : Keys := .leaf [
0x1f26211110f0000f8000f,0x1f26211110f0000ff0008,0x1f26211110f0800f0000f,0x1f26211190f0000f0000f]
def r4p20 : Keys := .leaf [
0x1f2621f1100f0000f0008,0x1f2628888111102f0000f,0x1f26288881f1100ff000f,0x1f26288f811110ff0000f]
def r4p21 : Keys := .leaf [
0x1f26a11110f0000f0000f,0x1f272888811f10f00000f,0x1f2f2888811110660000f,0x1f2f2888811710f00000f]
def r4p22 : Keys := .leaf [
0x1f2f288f866661f11000f,0x1f4442222111902f0000f,0x1f444222a111102f0000f,0x1f4449999333302f0000f]
def r4p23 : Keys := .leaf [
0x1f444f22a1f1100f0000f,0x1f44cf22a1f1100f0000f,0x1f6668888111102f2000f,0x1f6668888131300f0000f]
def r4p24 : Keys := .leaf [
0x1f6668ff822f21111000f,0x1f666aaaa111102f0000f,0x1f666aaaa11110af0000f,0x1f666aafa11110ff0000f]
def r4p25 : Keys := .leaf [
0x1f666f22a1f1100f0000f,0x1f66ef22a1f1100f0000f,0x1f8882262111102f0000f,0x1f88822f211110660000f]
def r4p26 : Keys := .leaf [
0x1f88822f211110f60000f,0x1f88822f211710f00000f,0x1f8884f4422f21131000f,0x1f8884f6422f21111000f]
def r4p27 : Keys := .leaf [
0x1f8885555333302f0000f,0x1f8886666111102f2000f,0x1f8886666131300f0000f,0x1faaa1111066000f0000f]
def r4p28 : Keys := .leaf [
0x1faaa5f55333300f0000f,0x1faaa6666111102f0000f,0x1faaa666611110af0000f,0x1faaa6666131100f0000f]
def r4p29 : Keys := .leaf [
0x1faaa6666171100f0000f,0x1faaa77771f1100f0000f,0x1faaaf666111102f0000f,0x1faaaf66611110af0000f]
def r4p30 : Keys := .leaf [
0x1faaaf666131100f0000f,0x1faaaf666171100f0000f,0x1faaaf6661f1100f0000f,0x1fafa666611110ff0000f]
def r4p31 : Keys := .leaf [
0x1fafaf66611110ff0000f,0x1fafaf6661f1100f0000f,0x1fbbbf6661f1100f0000f,0x1ff338888444412f0000f]
def r4 : Keys := .branch 0x1f22a4444131100f0000f (.branch 0x1f2221f1100f00048000f (.branch 0x199f9444432320f00000f (.branch 0x188f8444432221311000f (.branch 0x1888844443f3312f0000f (r4p0) (r4p1)) (.branch 0x198884444333302f0000f (r4p2) (r4p3))) (.branch 0x1f0f0aaaa11110660000f (.branch 0x1b22b55550f0000f0000f (r4p4) (r4p5)) (.branch 0x1f22211510f0000f8000f (r4p6) (r4p7)))) (.branch 0x1f2225f551f1100f8000f (.branch 0x1f22244441f1100f0000b (.branch 0x1f222444411110afa000f (r4p8) (r4p9)) (.branch 0x1f222444c1f1100f8000f (r4p10) (r4p11))) (.branch 0x1f22288f815510ff0000f (.branch 0x1f2228888177100f0000f (r4p12) (r4p13)) (.branch 0x1f22288f866661711000f (r4p14) (r4p15))))) (.branch 0x1f6668ff822f21111000f (.branch 0x1f2621f1100f0000f0008 (.branch 0x1f22a5f551f1100f0000f (.branch 0x1f22a444c1f1100f0000f (r4p16) (r4p17)) (.branch 0x1f26211110f0000f8000f (r4p18) (r4p19))) (.branch 0x1f2f288f866661f11000f (.branch 0x1f26a11110f0000f0000f (r4p20) (r4p21)) (.branch 0x1f444f22a1f1100f0000f (r4p22) (r4p23)))) (.branch 0x1faaa5f55333300f0000f (.branch 0x1f88822f211110f60000f (.branch 0x1f666f22a1f1100f0000f (r4p24) (r4p25)) (.branch 0x1f8885555333302f0000f (r4p26) (r4p27))) (.branch 0x1faaaf666131100f0000f (.branch 0x1faaa6666171100f0000f (r4p28) (r4p29)) (.branch 0x1fafaf66611110ff0000f (r4p30) (r4p31)))))

def a4p0 : Keys := .leaf [
0xa22211110f888807807c3,0xa22211110f88887c0007a,0xa22211110f8c880780787,0xa22211110f8c88780007a,0xa22211150f88880780787,0xa22211150f8888780007a,0xa22219110f88807c0007a,0xa22219110f8c80780007a,0xa22219150f8880780007a,0xa22791110888887c07804,0xa2279111088c887807806,0xa22791150888887807804,0xa227991108888780007c4,0xa2279911088c878000785,0xa22799150888878000784,0xa7a2111108888807807c1,0xa7a211110888887c00079,0xa7a21111088c880780786,0xa7a21111088c88780007a,0xa7a211150888880780784,0xa7a21115088888780007a,0xa7a219110888807c00078,0xa7a21911088c807800078,0xa7a219150888807800078,0xaa27911108888780007c4,0xaa279111088c878000786,0xaa2791150888878000784,0xc44411110f88882780787,0xc44411110f8888780027e,0xc44411110fa8880780787,0xc44411110fa888780007a,0xc44411310f88880780787]
def a4p1 : Keys := .leaf [
0xc44411310f8888780007a,0xc44419110f8880780027f,0xc44419110fa880780007f,0xc44419310f8880780007f,0xc44422221999880781781,0xc4442222199988780107b,0xc44422221999890780785,0xc44422221999897800078,0xc44422221f99890780785,0xc44422221f99897800078,0xc4442227911109780888c,0xc44422279111098888786,0xc444222791110f888878e,0xc44422279911088881784,0xc44422279911098880785,0xc444222799118f8880787,0xc4442227991908f887806,0xc44422279999880001784,0xc44422279999887801006,0xc44422279999890000785,0xc44423221999880780787,0xc4442322199988780007a,0xc44423279111088888784,0xc44423279911088880784,0xc44423279999880000784,0xc44427a21111088f8878e,0xc44427a21911888f80785,0xc444282811110ff88007a,0xc444282f9111088887f84,0xc444282f911108f887806,0xc444282f91110f8880787,0xc4442a221999810780785]
def a4p2 : Keys := .leaf [
0xc4442a221999817800078,0xc4442a279111088881786,0xc4442a279111098880786,0xc4442a279999810000786,0xc4442a2f911108f887806,0xc4442aaf9111087887806,0xc4442aaf9911878000785,0xc4442b22199980780007d,0xc4442b279111088880784,0xc4442faa911108788007a,0xc4442faa991180780007a,0xc4443939088887f800079,0xc444393908f8878000078,0xc44439390f8880780007a,0xc47c11110888882787801,0xc47c111108a8880787803,0xc47c11310888880787801,0xc47c19110888878000279,0xc47c191108a8878000078,0xc47c19310888878000079,0xc47c22221111090788889,0xc47c2222111109888807b,0xc47c222211110f88880fb,0xc47c22221911088881079,0xc47c22221911098880078,0xc47c22221911888f87803,0xc47c222219190f888007a,0xc47c22221999880001079,0xc47c22221999880781003,0xc47c22221999890000078,0xc47c22279111080887801,0xc47c22279111090008889]
def a4p3 : Keys := .leaf [
0xc47c22279111098888001,0xc47c22279911088881003,0xc47c22279911088887801,0xc47c22279911088887879,0xc47c22279911088887f84,0xc47c222799110f8008889,0xc47c222799110f8888889,0xc47c22279911888887801,0xc47c22279919088887804,0xc47c22279999880001001,0xc47c2322111108888807b,0xc47c23221911088880079,0xc47c23221999880000079,0xc47c23279111088888004,0xc47c27a22227991108889,0xc47c27a7a227991108889,0xc47c282811110f888007a,0xc47c282f9111088887803,0xc47c2a221111088881079,0xc47c2a22111109888007b,0xc47c2a22199981000007b,0xc47c2a279111088881006,0xc47c2a279111088887804,0xc47c2a27911108888787c,0xc47c2a279111088887f84,0xc47c2a2791110f800888c,0xc47c2a2791110f878888c,0xc47c2a2791110f888888c,0xc47c2a279911088887804,0xc47c2a279999911107806,0xc47c2a27a7a211110888c,0xc47c2a27a7a791110888c]
def a4p4 : Keys := .leaf [
0xc47c2a2f9111088887804,0xc47c2aaa91110f888807b,0xc47c2aaa99110f888007a,0xc47c2aaa9911878000078,0xc47c2aaaa80791110f88b,0xc47c2aaf9111080087801,0xc47c2b221111088880079,0xc47c2fa22a2791110888c,0xc47c2fa7aa2791110888c,0xc47c33331999880787803,0xc47c39112aaa8f888007a,0xc47c39390888878000079,0xc54422221999880780787,0xc5442222199988780007a,0xc54422279111088888786,0xc54422279911088880784,0xc54422279999880000784,0xc5442a22199980780007a,0xc5442a279111088880786,0xc57c22221111088888079,0xc57c22221911088880079,0xc57c22221999880000079,0xc57c22279111088888001,0xc57c2a221111088880079,0xc7c411110888882780784,0xc7c41111088888780027c,0xc7c4111108a8880780787,0xc7c4111108a888780007a,0xc7c411310888880780781,0xc7c411310888887800079,0xc7c41911088880780027c,0xc7c4191108a880780007d]
def a4p5 : Keys := .leaf [
0xc7c41931088880780007d,0xc7c42222111108f8880fb,0xc7c42222191908f880078,0xc7c42828111108f88007a,0xc7c4282f9111088880784,0xc7c42a2a111108f88007b,0xc7c42aaa911108788007a,0xc7c42aaa991180780007a,0xc7c433331999880780787,0xc7c43333199988780007a,0xc7c43939088880780007d,0xc7c4447c222799110888c,0xc7c4447c2a2791110888c,0xc7fc2828111108888007b,0xc7fc447c222799110888c,0xc7fc447c2a2791110888c,0xc804a22211110f8f80787,0xc804a22791110f8880786,0xc804a7a21111088f80786,0xc804a7a79111088880786,0xc804aaaa9111078780786,0xc804aaaf9111078000786,0xc804afaa911100780007f,0xc87ca2221111088887879,0xc87ca2221111088f87803,0xc87ca22211110f888007a,0xc87ca2279111088887806,0xc87ca7a21111088880079,0xc87caaaa911107800007a,0xcc4422221999810780785,0xcc4422221999817800078,0xcc4422279111088881784]
def a4p6 : Keys := .leaf [
0xcc4422279111098880786,0xcc4422279999810000786,0xcc4423221999807800078,0xcc4423279111088880784,0xcc44a7a21111088f80786,0xcc44aaaf9111078000785,0xcc7c11110888878000279,0xcc7c111108a887800007b,0xcc7c11310888878000079,0xcc7c2222111108888107b,0xcc7c2222111109888007b,0xcc7c2222199981000007b,0xcc7c22279111088881003,0xcc7c22279111088887801,0xcc7c22279111088887879,0xcc7c22279111088887f81,0xcc7c222791110f8008889,0xcc7c222791110f8888889,0xcc7c222791110ff808889,0xcc7c22279911088887801,0xcc7c22279999911107803,0xcc7c2322111108888007b,0xcc7c27a22227911108889,0xcc7c27a7a227911108889,0xcc7c2a279111088887801,0xcc7c2aaa91110f888007b,0xcc7c33331999878000078,0xcc7c47c42227911108889,0xcc7c47fc2227911108889,0xcc7ca2221111088f87803,0xcc7ca2279111088887801,0xcc7caaaa9111078000078]
def a4p7 : Keys := .leaf [
0xcccca22791110f8888786,0xcccca22799110f8880787,0xcccca2279919078000785,0xcccca7a21111080f80787,0xcccca7a2191900780007f,0xcccca828111107f80007a,0xcccca82f9111078000787,0xccccaa2791110f8880786,0xccccaa2f9111078000785,0xccccafaa9111080780787,0xccccafaa911108780007a,0xccccafaa991100780007f,0xccccafaaa807911100787,0xccccb939078000780007d,0xccccc878222791110f88e,0xccccc8782faa91110007a,0xccfca2221111080f87803,0xccfca2221919078000078,0xccfca2279111080807804,0xccfca828111107800007b,0xccfcaa2a1111078000078,0xcd4422221999807800078,0xcd4422279111088880784,0xcd7c22221111088880079,0xcfc44c7c2227911108889,0xcfcca2221111080f80787,0xcfcca222191900780007f,0xcfcca828111100780007a,0xcfccaaaa9111080780787,0xcfccaaaa911108780007a,0xcfccaaaa991100780007a,0xcfccaaaaa807911100787]
def a4p8 : Keys := .leaf [
0xcfccafaa9111080780787,0xcfccafaa911108780007a,0xcfccafaa991100780007a,0xcfccafaaa807911100787,0xcfccb9112aaa80780007a,0xcfccb9112faa80780007a,0xcfccc8782aaa91110007a,0xcfccc8782faa91110007a,0xcffc4c7c2227911108889,0xd55522279999887807806,0xd55527a21999880780787,0xd55527a2199988780007a,0xd5552a279999878000785,0xd55533330f88880780787,0xd55533330f8888780007a,0xd9114ccca2278f8880787,0xd9114cccafaa80780007f,0xd9114fccafaa80780007f,0xd915a2220888878780784,0xd915a222088f878000785,0xd915a2220f8880780007f,0xd915a2278888878000784,0xd915a7a20888807800078,0xd915aaaa8780007800078,0xdd553b330f88807800078,0xf8001111088887a4007fb,0xf8001111088c87a0007fe,0xf800111108a88784007fb,0xf800111108ac8780007fb,0xf80011110f88807c0027b,0xf80011110f88807f80243,0xf80011110f8c80780027f]
def a4p9 : Keys := .leaf [
0xf80011110f8c807f80207,0xf80011110fa8807c0007a,0xf80011110fa8807f80042,0xf80011110fac80780007a,0xf8001115088887a0007fc,0xf800111508a88780007fa,0xf80011150f8880780027f,0xf80011150f88807f80207,0xf80011150fa880780007a,0xf800113108888784007f9,0xf8001131088c8780007f8,0xf80011310f88807c0007a,0xf80011310f88807f80042,0xf80011310f8c80780007f,0xf800113508888780007f9,0xf80011350f8880780007a,0xf800222211110f8f807cb,0xf800222211158f8f80787,0xf800222211178888857d1,0xf800222211178d8d80787,0xf800222211178f88807d7,0xf800222211178f8d80787,0xf800222791110888817c6,0xf800222791110888857d4,0xf80022279111088c81786,0xf800222791110988807c6,0xf80022279111098c80786,0xf800222791110d8d80786,0xf800222791110f88807ce,0xf80022279115088881784,0xf80022279115098880787,0xf800222791158f8880787]
def a4p10 : Keys := .leaf [
0xf800227f911108ac87803,0xf800227f9135088887801,0xf800232791110888807c6,0xf80023279111088c80786,0xf80023279115088880784,0xf80027a21111088f807cb,0xf80027a21115888f80787,0xf80027a791110888807cc,0xf80027a79115888880784,0xf80033330888857d00078,0xf80033330d8d80780007a,0xf80033378888850500784,0xf800444411110ff8802fe,0xf800444411390ff88007a,0xf8004444117908888337c,0xf800444411790bb88007a,0xf800444411790f888037a,0xf800444411790fb88007a,0xf8004444222791790998c,0xf8004444233791790888c,0xf80044443337888881794,0xf80044443337898980787,0xf800447c111108888127b,0xf800447c1111088883379,0xf800447c111108a88107b,0xf800447c111109888027b,0xf800447c111109a88007b,0xf800447c11110bb88007b,0xf800447c11110f88802fb,0xf800447c1131088881079,0xf800447c113109888007a,0xf800447c11390f888007a]
def a4p11 : Keys := .leaf [
0xf800447c2222111789899,0xf800447c2227888881113,0xf800447c222791110988b,0xf800447c222791110989b,0xf800447c222791110998e,0xf800447c232791110888e,0xf800447c232791110988e,0xf800447c232799998888c,0xf800447c233791110888e,0xf800447c2aaa999981079,0xf800447c333309898007a,0xf800447c3337888881013,0xf800447f911108ac87806,0xf800447f9135088887804,0xf80045453337888880787,0xf800457c111108888027b,0xf800457c111108a88007b,0xf800457c1131088880079,0xf800457c222791110888b,0xf800457c222791110988b,0xf800457c2227999988889,0xf800457c232791110888b,0xf800457c2aaa99998007a,0xf800457d2222111788889,0xf800457d222791110888b,0xf800457d333308888007a,0xf80047c4111108f8802fe,0xf80047c4113908f88007a,0xf80047fc11110888802f9,0xf80047fc1139088880079,0xf8004ccca227999981784,0xf8004ccca327999980787]
def a4p12 : Keys := .leaf [
0xf80055550888833780785,0xf80055550bb880780007f,0xf80055552227899880787,0xf80055552337888880787,0xf800557d0888833000079,0xf800557d2222088881179,0xf800557d222209988007a,0xf800557d2227888881106,0xf800557d233208888007a,0xf800667f911108ac87803,0xf800667f9135088887801,0xf8041111088887a0007f9,0xf804111108a88780007fb,0xf80411110f8880780027f,0xf80411110f88807f80207,0xf80411110fa880780007a,0xf804113108888780007f9,0xf80411310f8880780007a,0xf804a22211110f8f80783,0xf804a7a21111088f80787,0xf807a22211110888857d3,0xf807a22211110d8d80786,0xf807a22211110f88807d3,0xf807a22211110f8d80783,0xf807a22791110f88807c6,0xf807a22791110f8c80787,0xf807a22791150f8880787,0xf807a7a211110888807d6,0xf807a7a21111088d80786,0xf807a7a791110888807c6,0xf807a7a79111088c80786,0xf807a7a791110c8c80786]
def a4p13 : Keys := .leaf [
0xf807a7a79115088880784,0xf807b3330888850500784,0xf807c07c222791110f88e,0xf807c07c27a791110888e,0xf807c44411110fa8807fe,0xf807c44411310f88807fa,0xf807c47c111108a88787b,0xf807c47c1131088887879,0xf807c47c222791110988b,0xf807c47c232791110888e,0xf807c47c2aaf91110f88e,0xf807c57c222791110888b,0xf807c7c4111108a8807fb,0xf807c7c411310888807f9,0xf807ccccafaf911100786,0xf807cfccaaaf911100787,0xf807cfccafaf911100787,0xf807d11522278f8880787,0xf807d11527a7888880784,0xf820111108888784007fb,0xf8201111088c8780007fe,0xf82011110f88807c0007a,0xf82011110f88807f80042,0xf82011110f8c80780007f,0xf820111508888780007fc,0xf82011150f8880780007f,0xf824111108888780007f9,0xf82411110f8880780007a,0xf827c47c1111088887a7c,0xf828444411110ff88007e,0xf82847c4111108f88007a,0xf878222211110f8c807fb]
def a4p14 : Keys := .leaf [
0xf878222211150f88807ff,0xf87822279111088c87f86,0xf87822279115088887f84,0xf87827a21111088c807fe,0xf87827a211150888807fc,0xf8784444111108888337e,0xf878444411110bb88007b,0xf878444411110f888037e,0xf878444411110fb88007e,0xf878447c11110f888027b,0xf878447c11110fa88007a,0xf878447c11310f888007a,0xf878447c202791110f88b,0xf878447c222791110988e,0xf878447c232791110888e,0xf878447c31310f888007a,0xf878457c222791110888b,0xf87847c4111108888037b,0xf87847c4111108b88007b,0xf87847fc111108888027b,0xf87847fc111108a88007b,0xf87847fc11110aa88007b,0xf87847fc1131088880079,0xf87847fc202791110888b,0xf87847fc3131088880079,0xf8784cfca22791110f88b,0xf8784cfcafaa91110007a,0xf8784ffcaaaa91110007a,0xf8784ffcafaa91110007a,0xf87855550888833000078,0xf87c22279111088887fc1,0xf87fc47c222791110f88b]
def a4p15 : Keys := .leaf [
0xf87fc47c27a791110888e,0xf87fc7fc222791110888b,0xf900447c222791110988b,0xf900447c232791110888e,0xf900457c222791110888b,0xf907c47c232791110888e,0xf91108888780007c00279,0xf91108888780007f80241,0xf9110888878400780027d,0xf91108888784007f80205,0xf911088887a0007c00078,0xf911088887a0007f80040,0xf911088887a4007800078,0xf911088c878000780027d,0xf911088c8780007f80205,0xf911088c87a000780007d,0xf91108a88780007c00078,0xf91108a88780007f80040,0xf91108a88784007800078,0xf91108ac8780007800078,0xf9110f888078002400078,0xf9110f888078002780040,0xf9110f88807c00200007d,0xf9110f88807f802000040,0xf9110f8c807800200007f,0xf9110fa88078000780042,0xf911222208888107807c1,0xf91122220888817c00078,0xf91122220888857d00078,0xf911222208888787807c9,0xf9112222088c810780785,0xf9112222088c817800078]
def a4p16 : Keys := .leaf [
0xf9112222088c87f8007fd,0xf9112222088f8780007cd,0xf91122220988807c00078,0xf9112222098c807800078,0xf91122220d8d80780007d,0xf91122220f88807800058,0xf91122220f88807c00078,0xf91122220f88807c80078,0xf91122220f88807d0007a,0xf91122220f8c80780007a,0xf91122220f8c807c0007a,0xf91122220f8c807f80787,0xf91122220f8d80780007a,0xf91122220f8f807800048,0xf91122260f88807c00078,0xf91122260f8c80780007a,0xf91122278888850500784,0xf911222788888780007d4,0xf911222788888787807c4,0xf911222788888787847c4,0xf9112227888c878780785,0xf9112227888d878000785,0xf91122278c8c878780785,0xf91122278f88807c00078,0xf91122278f8c80780007a,0xf91127a20f88807c00078,0xf91127a20f8c80780007a,0xf91127a60f8c80780007a,0xf9112aaa8f88807c00078,0xf9112aaa8f8c80780007a,0xf9112aae8f8c80780007a,0xf9112faa8f88807c00078]
def a4p17 : Keys := .leaf [
0xf9112faa8f8c80780007a,0xf9112fae8f8c80780007a,0xf91133330f88807c0007a,0xf91133330f8c80780007a,0xf91144440888812780785,0xf9114444088881780027c,0xf91144440888833780785,0xf9114444088887f8002fc,0xf911444408a8810780785,0xf911444408a8817800078,0xf911444408a88787807f8,0xf911444408f88780002f8,0xf9114444098880780027d,0xf911444409a880780007d,0xf91144440bb8807800078,0xf91144440f8880380007d,0xf91144440f8880780027d,0xf91144440f888078002fd,0xf91144440f8880780037f,0xf91144440fa880780007f,0xf91144440fa880780027f,0xf91144440fa8807f8007a,0xf91144440fb880780007f,0xf91144440ff880280007d,0xf91144442227888881794,0xf91144442227898980785,0xf91144640f8880780027d,0xf91144640fa880780007f,0xf911447c0888833000078,0xf911447c0888878000379,0xf911447c088887f800279,0xf911447c088887f802279]
def a4p18 : Keys := .leaf [
0xf911447c08a887f800078,0xf911447c08b8878000078,0xf911447c0aa887f800078,0xf911447c0f8880780027d,0xf911447c0fa880780007f,0xf911447c2222088881179,0xf911447c2222099880078,0xf911447c2227888887ff9,0xf911447c22278f88807f8,0xf911447c222791110988b,0xf911447c222799998f889,0xf911447c232791110888e,0xf911447c2aaa8ff88007a,0xf911447c3333088881079,0xf911447c3333088883079,0xf911447c3333098880078,0xf911447c33330b8880078,0xf911447c333788888787c,0xf911447c3bbb8f8880078,0xf911457c222791110888b,0xf911457c3333088880079,0xf91147c40f8880780027d,0xf91147c40fa880780007f,0xf91147e40fa880780007f,0xf9114ccc8f8880780027d,0xf9114ccc8fa880780007f,0xf9114ccca2278f8f80787,0xf9114cccaaaa810780785,0xf9114cccaaaa817800078,0xf9114cec8fa880780007f,0xf9114dccabaa80780007a,0xf9114fcc8f8880780027d]
def a4p19 : Keys := .leaf [
0xf9114fcc8fa880780007f,0xf9114fccafaa80780007a,0xf9114fccafaf80780007f,0xf9114fccbbbb80780007a,0xf9114fccbfbb80780007f,0xf9114fec8fa880780007f,0xf9114ffcafaa80780007a,0xf91155550f8880780027f,0xf91155550fa880780007f,0xf91155552227888881784,0xf91155552227888885784,0xf91155552227898880785,0xf911555522278d8880785,0xf91155552327888880784,0xf911557d2227888887f81,0xf9115ddda2278f8880785,0xf9115dddafaa80780007f,0xf9115fddafaa80780007a,0xf9150888878000780027d,0xf91508888780007f80205,0xf915088887a000780007d,0xf91508a8878000780007d,0xf9150f88807800200007d,0xf91522220888810780785,0xf91522220888817800078,0xf9152222088887f8007f9,0xf91522220988807800078,0xf91522220f88807800078,0xf91522220f88807c00078,0xf91522220f88807f80785,0xf91522220f8c807800078,0xf91522260f88807800078]
def a4p20 : Keys := .leaf [
0xf91522278888878780785,0xf91522278f88807800078,0xf91527a20f88807800078,0xf9152aaa8f88807800078,0xf9152faa8f88807800078,0xf91533330f88807800078,0xf91533370f88807800078,0xf915a2220888878780781,0xf915a222088f878000785,0xf915a2220f88807800078,0xf917a2220888850500785,0xf917a22208888780007d1,0xf917a2220888878500781,0xf917a222088d878000785,0xf917a2220f88807800052,0xf917d55522278f8880785,0xf917d55527a7888880784,0xf93108888780007c00078,0xf93108888780007f80040,0xf93108888784007800078,0xf931088c8780007800078,0xf9310f888078000780040,0xf93144440888810780785,0xf93144440888817800078,0xf931444408888787807fc,0xf9314444098880780007d,0xf93144440f8880780007d,0xf93144440f8880780027d,0xf93144440f88807f80078,0xf93144440fa880780007d,0xf93144640f8880780007d,0xf931447c088887f800078]
def a4p21 : Keys := .leaf [
0xf931447c0f8880780007d,0xf93147c40f8880780007d,0xf9314ccc8f8880780007d,0xf9314fcc8f8880780007d,0xf93155550f8880780007d,0xf93155750f8880780007d,0xf93508888780007800078,0xf9394444088887f80007c,0xf939444408f8878000078,0xf93944440f8880780007d,0xf978457c222791110888b,0xf97944440888833000078,0xf9794444088887800037c,0xf9794444088887b00007c,0xf979444408b8878000078,0xf97944440f8880300007f,0xf979447c33330f8880078,0xf97947fc3333088880079,0xf999c4442222090780787,0xf999c444222209780007a,0xfa22111108888107807c3,0xfa2211110888817c0007b,0xfa2211110888857d0007b,0xfa22111108888787807cc,0xfa221111088c810780786,0xfa221111088c817800078,0xfa221111088c87f8007fe,0xfa2211110988807c0007a,0xfa221111098c80780007a,0xfa2211110d8d80780007a,0xfa2211150888810780784,0xfa2211150888817800078]
def a4p22 : Keys := .leaf [
0xfa221115088887f8007fc,0xfa221115098880780007a,0xfa2211158888878780784,0xfa2211178888850500784,0xfa22111788888780007d1,0xfa2211178888878500785,0xfa221117888d878000785,0xfa2244441117888881794,0xfa2244441117898980787,0xfa22447c222791110988b,0xfa22447c232791110888e,0xfa2245451117888880784,0xfa22457c222791110888b,0xfa2247c4111108f8800fb,0xfa2247c41117888880794,0xfa2247c41117888980785,0xfa2247c4111908f88007a,0xfa2247c51117888880784,0xfa224ccc9999810780785,0xfa224ccc9999817800078,0xfa2255550888811780785,0xfa225555099880780007d,0xfa2279110f88807c0007a,0xfa2279110f8c80780007a,0xfa2279150f88807800078,0xfa2679150f88807800078,0xfa2791110888850500784,0xfa27911108888780007d6,0xfa27911108888787807c4,0xfa27911108888787847c4,0xfa279111088c878780786,0xfa279111088d878000786]
def a4p23 : Keys := .leaf [
0xfa2791110c8c878780786,0xfa2791150888878780784,0xfa27a7a791110888807c4,0xfa27a7a791110888847c4,0xfa27a7a79111088c80786,0xfa27a7a791110c8c80786,0xfa27a7a79115088880784,0xfa27c07c27a791110888e,0xfa27c47c1111088887ffc,0xfa27c47c222791110988b,0xfa27c47c232791110888e,0xfa27c47c27a791110888c,0xfa27c47c27ff91110888e,0xfa27c47c2faf91110888e,0xfa27c57c222791110888b,0xfa27c7fc11110888807fb,0xfa27cccc91110f8f80786,0xfa27ccccafaf911100786,0xfa27cfcc9111088f80786,0xfa27d1150888878780784,0xfa27d11527a7888880784,0xfa2a47c4111108f88007a,0xfa7fc47c27a791110888c,0xfb22447c232791110888e,0xfb27c47c232791110888e,0xfb330888850500780007d,0xfb3344440888817900078,0xfb3344440989807800078,0xfb3347fc1179088880078,0xfb334fcc999980780007a,0xfb3355550888810780785,0xfb3355550888817800078]
def a4p24 : Keys := .leaf [
0xfb3355550888830780785,0xfb3355550888857800078,0xfb335555098880780007d,0xfb3355550d8880780007d,0xfb33557d088887f800078,0xfb335ddd8f8880780007d,0xfb3379110f88807c0007a,0xfb3379110f8c80780007a,0xfb3379150f88807800078,0xfb3779150f88807800078,0xfb37c47c27a791110888c,0xfb37d5550888878780784,0xfb37d55527a7888880784,0xfc4411110888812780786,0xfc441111088881780027e,0xfc4411110888833780786,0xfc441111088887f8002f9,0xfc44111108a8810780783,0xfc44111108a881780007b,0xfc44111108a88787807fb,0xfc441111098880780027e,0xfc44111109a880780007f,0xfc4411110bb880780007f,0xfc4411310888810780785,0xfc4411310888817800078,0xfc44113108888787807f9,0xfc441131098880780007f,0xfc441139088887f800079,0xfc4411790888833000078,0xfc441179088887800037c,0xfc441179088887b000078,0xfc44117908b8878000078]
def a4p25 : Keys := .leaf [
0xfc4422221179088881179,0xfc442222117909988007a,0xfc4423321179088880079,0xfc4427a21111088f8078e,0xfc4427a21111888f80787,0xfc4427a21179088880179,0xfc4427a21179089880078,0xfc4427b21179088880078,0xfc442aaa9999810780785,0xfc442aaa9999817800078,0xfc4433330888817900078,0xfc4433330989807800078,0xfc44447c222791110988e,0xfc44447c232791110888e,0xfc44457c222791110888b,0xfc4479110f8880780027f,0xfc4479110fa880780007f,0xfc4479310f8880780007d,0xfc44a7a21111088f80786,0xfc6479310f8880780007d,0xfc7c11110888833000079,0xfc7c1111088887800037b,0xfc7c1111088887f800279,0xfc7c1111088887f802279,0xfc7c111108a887f80007b,0xfc7c111108b887800007b,0xfc7c11110aa887f80007b,0xfc7c1131088887f800079,0xfc7c22279111088887ff9,0xfc7c27a791110888807f9,0xfc7c2aaa91110ff88007b,0xfc7c2faa911108f88007a]
def a4p26 : Keys := .leaf [
0xfc7c3131088887f800079,0xfc7c447c222791110988e,0xfc7c447c232791110888e,0xfc7c457c222791110888b,0xfc7c47fc1111088880279,0xfc7c47fc1111088882279,0xfc7c47fc111108a88007b,0xfc7c47fc11110aa88007b,0xfc7c47fc1131088880079,0xfc7c47fc202791110888b,0xfc7c47fc2227911108889,0xfc7c47fc3131088880079,0xfc7c47ffa22791110888b,0xfc7c4ffca22791110888b,0xfc7c4ffcaaaa91110007b,0xfc7fc7fc2227911108889,0xfd44457c222791110888b,0xfd5508888330007800078,0xfd5522220888811780785,0xfd552222099880780007d,0xfd5527a79117888880784,0xfd552faa9999807800078,0xfd5533330888810780785,0xfd5533330888817800078,0xfd5533330888830780785,0xfd5533330888857800078,0xfd5533330988807800078,0xfd5533330b88807800078,0xfd5533378888878780785,0xfd553bbb8f88807800078,0xfd5579110f8880780027f,0xfd5579110fa880780007f]
def a4p27 : Keys := .leaf [
0xfd5579310f8880780007d,0xfd557b330888810780785,0xfd557b330888817800078,0xfd557b330888830780785,0xfd557b330888857800078,0xfd557b330988807800078,0xfd557b330b88807800078,0xfd557b330d8880780007d,0xfd557b330f88807800078,0xfd557b378888878780785,0xfd557b378f8880780007d,0xfd557bbb8f8880780007d,0xfd7579310f8880780007d,0xfd7c457c222791110888b,0xfd7d3333088887f800078,0xfd7d47fc2227911108889,0xfd7d47fc3333088880079,0xfd7d7b33088887f800078,0xfd7d7b330f88807800078,0xfdddfb330f88807800078,0xff99c4442222090780785,0xff99c4442222097800078]
def a4 : Keys := .branch 0x1f0f04444222a1f1100ff (.branch 0x19999444f22221f1110f0 (.branch 0x188f8444f222213111000 (.branch 0x1888822621f1110f0000f (a4p0) (.branch 0x188885444333302f0000f (a4p1) (a4p2))) (.branch 0x18f883262111100f0000f (.branch 0x188f8545f222211110f00 (a4p3) (a4p4)) (.branch 0x19888444f2222131100f0 (a4p5) (a4p6)))) (.branch 0x1f00044ff222211590f00 (.branch 0x19f995f552222100f00f0 (a4p7) (.branch 0x1f00022221f1900ff0040 (a4p8) (a4p9))) (.branch 0x1f000aaaa1111066f00f0 (.branch 0x1f00088f84444222f1313 (a4p10) (a4p11)) (.branch 0x1f00f4f4f222a111100f0 (a4p12) (a4p13))))) (.branch 0x1f26288f81f1100f0000f (.branch 0x1f2225f551f1900f0000f (.branch 0x1f0ff88f84f4f22221111 (a4p14) (.branch 0x1f222444411190ff000ff (a4p15) (a4p16))) (.branch 0x1f2229f991f5100f0000f (.branch 0x1f22288f811510ff0000f (a4p17) (a4p18)) (.branch 0x1f22a444f11110f0f00f0 (a4p19) (a4p20)))) (.branch 0x1f666aaaa1111060f00f0 (.branch 0x1f444222a11110ff000ff (a4p21) (.branch 0x1f44f222219190f0f00f0 (a4p22) (a4p23))) (.branch 0x1f8f8626211110ff0000f (.branch 0x1f888444422f21111022f (a4p24) (a4p25)) (.branch 0x1faaaf2621f1100f0000f (a4p26) (a4p27)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p0 : r4p0.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p1 : r4p1.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p2 : r4p2.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p3 : r4p3.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p4 : r4p4.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p5 : r4p5.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p6 : r4p6.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p7 : r4p7.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p8 : r4p8.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p9 : r4p9.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p10 : r4p10.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p11 : r4p11.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p12 : r4p12.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p13 : r4p13.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p14 : r4p14.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p15 : r4p15.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p16 : r4p16.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p17 : r4p17.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p18 : r4p18.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p19 : r4p19.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p20 : r4p20.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p21 : r4p21.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p22 : r4p22.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p23 : r4p23.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p24 : r4p24.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p25 : r4p25.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p26 : r4p26.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p27 : r4p27.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p28 : r4p28.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p29 : r4p29.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p30 : r4p30.all (checkFast 3 a3) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr4p31 : r4p31.all (checkFast 3 a3) = true := by
  decide +kernel

lemma badR4 : Rejects 4 r4 :=
  verifyFast 3 a3 r4 badA3 (by
    unfold r4
    simp only [allBranch, Bool.and_true, goodr4p0, goodr4p1, goodr4p2, goodr4p3, goodr4p4, goodr4p5, goodr4p6, goodr4p7, goodr4p8, goodr4p9, goodr4p10, goodr4p11, goodr4p12, goodr4p13, goodr4p14, goodr4p15, goodr4p16, goodr4p17, goodr4p18, goodr4p19, goodr4p20, goodr4p21, goodr4p22, goodr4p23, goodr4p24, goodr4p25, goodr4p26, goodr4p27, goodr4p28, goodr4p29, goodr4p30, goodr4p31])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p0 : a4p0.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p1 : a4p1.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p2 : a4p2.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p3 : a4p3.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p4 : a4p4.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p5 : a4p5.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p6 : a4p6.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p7 : a4p7.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p8 : a4p8.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p9 : a4p9.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p10 : a4p10.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p11 : a4p11.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p12 : a4p12.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p13 : a4p13.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p14 : a4p14.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p15 : a4p15.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p16 : a4p16.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p17 : a4p17.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p18 : a4p18.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p19 : a4p19.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p20 : a4p20.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p21 : a4p21.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p22 : a4p22.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p23 : a4p23.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p24 : a4p24.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p25 : a4p25.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p26 : a4p26.all (checkAlias r4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda4p27 : a4p27.all (checkAlias r4) = true := by
  decide +kernel

lemma badA4 : RejectsAlias 4 a4 :=
  verifyAliases 4 r4 a4 badR4 (by
    unfold a4
    simp only [allBranch, Bool.and_true, gooda4p0, gooda4p1, gooda4p2, gooda4p3, gooda4p4, gooda4p5, gooda4p6, gooda4p7, gooda4p8, gooda4p9, gooda4p10, gooda4p11, gooda4p12, gooda4p13, gooda4p14, gooda4p15, gooda4p16, gooda4p17, gooda4p18, gooda4p19, gooda4p20, gooda4p21, gooda4p22, gooda4p23, gooda4p24, gooda4p25, gooda4p26, gooda4p27])
def r5p0 : Keys := .leaf [
0x1f22244441f1100f8000f,0x1f22a44441f1100f0000f,0x1faaaf6661f1100f0000f,0x14444322211110f0000f8000f]
def r5p1 : Keys := .leaf [
0x14444322211110f0800f0000f,0x14444322211190f0000f0000f,0x14444322a11110f0000f0000f,0x1444f322211110f0000f00008]
def r5p2 : Keys := .leaf [
0x14f443222111100f0000f0008,0x15444222211110f0800f0000f,0x15444222211190f0000f0000f,0x15444222a11110f0000f0000f]
def r5p3 : Keys := .leaf [
0x1544f222211110f0000f00008,0x1888844443222131100f0000f,0x188884444323211f10f00000f,0x1888844443333120000f0000f]
def r5p4 : Keys := .leaf [
0x1888844443f33120000f0000f,0x188884f443223111100f0000f,0x188885454222211f10f00000f,0x18888555532230f0000f0000f]
def r5p5 : Keys := .leaf [
0x18a8844443222111100f0000f,0x18f8844443222111100f0000f,0x18f8844443223111100f0000f,0x18f88444f3222111100f0000f]
def r5p6 : Keys := .leaf [
0x18f884f443222111100f0000f,0x18f8872224444111100f0000f,0x18ff844443222111100f0000f,0x198884f443222111100f0000f]
def r5p7 : Keys := .leaf [
0x199994f443222111100f0000f,0x19999545422220f0000f0000f,0x19999555532220f0000f0000f,0x19999722255550f0000f0000f]
def r5p8 : Keys := .leaf [
0x19f8844443222111100f0000f,0x19f9944443222111100f0000f,0x1aaaa4f443222111100f0000f,0x1aaaa544433330f0000f0000f]
def r5p9 : Keys := .leaf [
0x1b22299994f44111100f0000f,0x1b22b444411110f0000f0000f,0x1baaa4f443222111100f0000f,0x1baaa666611110f0000f0000f]
def r5p10 : Keys := .leaf [
0x1baaa766611110f0000f0000f,0x1f000226211110f0000f8000f,0x1f000226211110f0000ff0008,0x1f000226211190f0000f0000f]
def r5p11 : Keys := .leaf [
0x1f000226a11110f0000f0000f,0x1f00044442222111902f0000f,0x1f000444422221f1100f9000f,0x1f000444422221f1f00f00009]
def r5p12 : Keys := .leaf [
0x1f0004444222a111102f0000f,0x1f000444f2222111102f00008,0x1f000444f22221f1100f00009,0x1f0004f442222111f00f00009]
def r5p13 : Keys := .leaf [
0x1f0004f4f2222111100f00009,0x1f00088882262111102f0000f,0x1f000888822f211110660000f,0x1f000888822f211710f00000f]
def r5p14 : Keys := .leaf [
0x1f00088885555333302f0000f,0x1f00088886666111102f2000f,0x1f00088f8226211510f00000f,0x1f00088f8226a11110f00000f]
def r5p15 : Keys := .leaf [
0x1f00099994444333302f0000f,0x1f00099995555222202f0000f,0x1f000aaaa1111066000f0000f,0x1f000aaaa6666111102f0000f]
def r5p16 : Keys := .leaf [
0x1f000aaaa666611110af0000f,0x1f040222211110f0000ff0008,0x1f040222211110f0800f0000f,0x1f040222211190f0000f0000f]
def r5p17 : Keys := .leaf [
0x1f040222a11110f0000f0000f,0x1f048222211110f0000f0000f,0x1f0f0444f222211110ff00008,0x1f0f099f9555522220f00000f]
def r5p18 : Keys := .leaf [
0x1f0f0aaaa666611110ff0000f,0x1f22211110f0000f00048000f,0x1f22211110f0000f0004f0008,0x1f22211110f0000ff00400008]
def r5p19 : Keys := .leaf [
0x1f22211110f4000f0000f0008,0x1f22211510f0000f0000f0008,0x1f2221f1100f00040000f0008,0x1f22244441111020800f0000f]
def r5p20 : Keys := .leaf [
0x1f22244441111020f00f00008,0x1f2224444111102f0000f0008,0x1f222444411110f0000f0000b,0x1f222444411110f0000f8000f]
def r5p21 : Keys := .leaf [
0x1f222444411110f0000f9000f,0x1f222444411110f0008f8000f,0x1f222444411110f0800f0000f,0x1f222444411110f0800f8000f]
def r5p22 : Keys := .leaf [
0x1f222444411110f0900f0000f,0x1f222444411110f0a00f0000f,0x1f222444411110f0f00f00009,0x1f222444411110f0f00f8000f]
def r5p23 : Keys := .leaf [
0x1f222444411110f0f08f8000f,0x1f222444411110ff000f8000f,0x1f222444411110ff000ff0008,0x1f222444411110ff800f8000f]
def r5p24 : Keys := .leaf [
0x1f222444411190f0000f0000f,0x1f222444411190f0000f8000f,0x1f222444411190f0800f0000f,0x1f222444411190f0f00f0000f]
def r5p25 : Keys := .leaf [
0x1f2224444111b0f0000f0000f,0x1f2224444111f0f0000f00009,0x1f2224444131100f0000f0008,0x1f222444419190f0f00f0000f]
def r5p26 : Keys := .leaf [
0x1f22244441f1100f0000f0008,0x1f22244441f1100f0000f0009,0x1f22244441f1100f8000f0008,0x1f22244441f1100ff00f00008]
def r5p27 : Keys := .leaf [
0x1f22244441f110f0000f8000f,0x1f22244441f110f0800f0000f,0x1f22244441f11111100f8000f,0x1f22244441f11111900f0000f]
def r5p28 : Keys := .leaf [
0x1f22244441f190f0000f0000f,0x1f22244441f190f0800f0000f,0x1f22244441f19111100f0000f,0x1f22244441f19111900f0000f]
def r5p29 : Keys := .leaf [
0x1f22244441f191f1100f0000f,0x1f222444c11110f0000f8000f,0x1f222444c11110f0800f0000f,0x1f222444c11190f0000f0000f]
def r5p30 : Keys := .leaf [
0x1f222444c1f1100f0000f0008,0x1f222444f11110f0000f8000f,0x1f222444f11110f0800f0000f,0x1f222444f11110f0f00f00008]
def r5p31 : Keys := .leaf [
0x1f222444f11190f0000f0000f,0x1f222444f1f1100f0000f0008,0x1f2224f4411110f0000f8000f,0x1f2224f4411110f0800f0000f]
def r5p32 : Keys := .leaf [
0x1f2224f4411190f0000f0000f,0x1f2224f441f1100f0000f0008,0x1f2224f44222a111100f0000f,0x1f2224f4c11110f0800f0000f]
def r5p33 : Keys := .leaf [
0x1f222555511110f0000f8000f,0x1f222555511110f0800f0000f,0x1f222555511190f0000f0000f,0x1f22255551f1100f0000f0008]
def r5p34 : Keys := .leaf [
0x1f222555d11190f0000f0000f,0x1f2225f551f1100f0000f0008,0x1f222666611110f0000f8000f,0x1f222666611110f0800f0000f]
def r5p35 : Keys := .leaf [
0x1f222666611190f0000f0000f,0x1f22288881111066000f0000f,0x1f222888811110f4000ff000f,0x1f222888811110f4400f0000f]
def r5p36 : Keys := .leaf [
0x1f222888811110f4f00f0000f,0x1f222888811510f0000ff000f,0x1f222888811510f0f00f0000f,0x1f222888815510f0000f0000f]
def r5p37 : Keys := .leaf [
0x1f22288881f1100f00044000f,0x1f22288881f1100f0004f000f,0x1f22288881f11044000f0000f,0x1f22288884444111102f0000f]
def r5p38 : Keys := .leaf [
0x1f22288884444111102f2000f,0x1f2228888444411110af0000f,0x1f2228888444411f10f00001f,0x1f22288884444131100f0000f]
def r5p39 : Keys := .leaf [
0x1f22288884444131102f0000f,0x1f22288884444131300f0000f,0x1f22288884444171100f0000f,0x1f222888844441f1100f0000f]
def r5p40 : Keys := .leaf [
0x1f222888844441f1100f1000f,0x1f222888844441f1100f8000f,0x1f222888844441f1102f0000f,0x1f222888844441f1112f0000f]
def r5p41 : Keys := .leaf [
0x1f2228888444f111102f0000f,0x1f2228888445411f10f00000f,0x1f22288884644111102f0000f,0x1f22288884f44111102f0000f]
def r5p42 : Keys := .leaf [
0x1f22288885555111102f0000f,0x1f22288886666111102f0000f,0x1f22288886666171100f0000f,0x1f222888944441f1100f0000f]
def r5p43 : Keys := .leaf [
0x1f222889844441f1100f0000f,0x1f22288c844441f1100f0000f,0x1f22288f811110ff00440000f,0x1f22288f84444111102f0000f]
def r5p44 : Keys := .leaf [
0x1f22288f8444411310f00000f,0x1f22288f84444131100f0000f,0x1f22288f844441f1100ff000f,0x1f22288f844441f1111f1000f]
def r5p45 : Keys := .leaf [
0x1f22288f8444433331f11000f,0x1f22288f8444f11110ff0000f,0x1f22288f8444f1f1100f0000f,0x1f22288f8446411110f00000f]
def r5p46 : Keys := .leaf [
0x1f22288f844f444441f11000f,0x1f22288f84f4422f21111000f,0x1f22288f8555511f10f00000f,0x1f22288f8555533330f00000f]
def r5p47 : Keys := .leaf [
0x1f22288f8666611110f0f000f,0x1f22288f8666611110ff0000f,0x1f22288f8666f11110f00000f,0x1f22288f8777711110f00000f]
def r5p48 : Keys := .leaf [
0x1f222898844441f1100f0000f,0x1f2228a884444111102f0000f,0x1f2228a884444131100f0000f,0x1f2228a8844441f1100f0000f]
def r5p49 : Keys := .leaf [
0x1f2228a884644111100f0000f,0x1f2228af84444111102f0000f,0x1f2228c8844441f1100f0000f,0x1f2228f884444111102f0000f]
def r5p50 : Keys := .leaf [
0x1f2228f884444131100f0000f,0x1f2228f88444f1f1100f0000f,0x1f2228f884644111100f0000f,0x1f2228f884f441f1100f0000f]
def r5p51 : Keys := .leaf [
0x1f2228ff844441f1100f0000f,0x1f2228ff84f44111100f0000f,0x1f22299994444111102f0000f,0x1f22299994444131100f0000f]
def r5p52 : Keys := .leaf [
0x1f2229999444f1f1100f0000f,0x1f22299994f441f1100f0000f,0x1f222999955550f0f00f0000f,0x1f222999955551f1100f0000f]
def r5p53 : Keys := .leaf [
0x1f22299f944441f1100f0000f,0x1f22299f955550f0000f0000f,0x1f2229a8844441f1100f0000f,0x1f2229b994444131100f0000f]
def r5p54 : Keys := .leaf [
0x1f2229f9944441f1100f0000f,0x1f2229f99444f1f1100f0000f,0x1f2229f994f44111100f0000f,0x1f2229f994f441f1100f0000f]
def r5p55 : Keys := .leaf [
0x1f2229f9955550f0000f0000f,0x1f2229f9955551f1100f0000f,0x1f2229f995f550f0000f0000f,0x1f2229f995f55111100f0000f]
def r5p56 : Keys := .leaf [
0x1f2229f995f551f1100f0000f,0x1f2229ff944441f1100f0000f,0x1f222aaaa4444111102f0000f,0x1f222aaaa444411110af0000f]
def r5p57 : Keys := .leaf [
0x1f222aaaa4444131100f0000f,0x1f222aaaa4644111100f0000f,0x1f222aaaa4e44111100f0000f,0x1f222aaaa4f441f1100f0000f]
def r5p58 : Keys := .leaf [
0x1f222aaaa4f4f111100f0000f,0x1f222aaaa55551f1100f0000f,0x1f222aaaa5f55111100f0000f,0x1f222aafa4f44111100f0000f]
def r5p59 : Keys := .leaf [
0x1f222afaa44441f1100f0000f,0x1f222afaa4f44111100f0000f,0x1f222bbbb44441f1100f0000f,0x1f222bbbb4f44111100f0000f]
def r5p60 : Keys := .leaf [
0x1f222bbbb55550f0000f0000f,0x1f222bfbb44441f1100f0000f,0x1f223888844441f1100f0000f,0x1f22a444411110f0000f0000f]
def r5p61 : Keys := .leaf [
0x1f22a444411110f0000f8000f,0x1f22a444411110f0800f0000f,0x1f22a444411110f0f00f0000f,0x1f22a444411190f0000f0000f]
def r5p62 : Keys := .leaf [
0x1f22a44441f1100f0000f0008,0x1f22a44441f110f0000f0000f,0x1f22a44441f11111100f0000f,0x1f22a444c11110f0000f0000f]
def r5p63 : Keys := .leaf [
0x1f22a444f11110f0000f0000f,0x1f22a4f4411110f0000f0000f,0x1f22a4f44222a111100f0000f,0x1f22a555511110f0000f0000f]
def r5p64 : Keys := .leaf [
0x1f22a666611110f0000f0000f,0x1f22a666e11110f0000f0000f,0x1f22a888844441f1100f0000f,0x1f22b444411110f0000f0000f]
def r5p65 : Keys := .leaf [
0x1f22faaaa44441f1100f0000f,0x1f22faaaa4f44111100f0000f,0x1f2328888444411f10f00000f,0x1f26211110f0000f0000f0008]
def r5p66 : Keys := .leaf [
0x1f262888811110f0000ff000f,0x1f262888811110f0f00f0000f,0x1f2f288f8666611110f00000f,0x1f44422221111020800f0000f]
def r5p67 : Keys := .leaf [
0x1f44422221111020f00f00008,0x1f4442222111102f0000f0008,0x1f444222211110f0000f0000b,0x1f444222211110f0800f0000f]
def r5p68 : Keys := .leaf [
0x1f444222211110f0900f0000f,0x1f444222211110f0a00f0000f,0x1f444222211110f0f00f00009,0x1f444222211110ff000ff0008]
def r5p69 : Keys := .leaf [
0x1f444222211190f0000f0000f,0x1f444222211190f0000f8000f,0x1f444222211190f0800f0000f,0x1f444222211190f0f00f0000f]
def r5p70 : Keys := .leaf [
0x1f4442222111b0f0000f0000f,0x1f444222219190f0f00f0000f,0x1f44422221f19111100f0000f,0x1f444222a11110f0000f0000f]
def r5p71 : Keys := .leaf [
0x1f444222a11110f0000f8000f,0x1f444222a11110f0800f0000f,0x1f444222a11110f0f00f0000f,0x1f444222a11190f0000f0000f]
def r5p72 : Keys := .leaf [
0x1f444222a1f11111100f0000f,0x1f444222b11110f0000f0000f,0x1f4444f44222a111100f0000f,0x1f4448888223211f10f00000f]
def r5p73 : Keys := .leaf [
0x1f44488882f22111102f0000f,0x1f4448f882223111100f0000f,0x1f4448f88222a111100f0000f,0x1f444f22211110f0000f8000f]
def r5p74 : Keys := .leaf [
0x1f444f22211110f0800f0000f,0x1f444f22211190f0000f0000f,0x1f444f2228888111102f0000f,0x1f444f22288f811110ff0000f]
def r5p75 : Keys := .leaf [
0x1f444f22a11110f0000f0000f,0x1f44c222211110f0800f0000f,0x1f44c222211190f0000f0000f,0x1f44c222a11110f0000f0000f]
def r5p76 : Keys := .leaf [
0x1f44cf22a11110f0000f0000f,0x1f44f222211110f0800f0000f,0x1f44f222211110f0f00f00008,0x1f44f222211190f0000f0000f]
def r5p77 : Keys := .leaf [
0x1f44f222a11110f0000f0000f,0x1f44f4f4f2222111100f00008,0x1f4548888222211f10f00000f,0x1f666222211110f0800f0000f]
def r5p78 : Keys := .leaf [
0x1f666222211190f0000f0000f,0x1f666222a11110f0000f0000f,0x1f66688f822f211110f00000f,0x1f666aaaa1111060000f0000f]
def r5p79 : Keys := .leaf [
0x1f666aaaa11110f0f00f0000f,0x1f666aaaa4f44111100f0000f,0x1f666f22211110f0000f8000f,0x1f666f22211110f0800f0000f]
def r5p80 : Keys := .leaf [
0x1f666f22211190f0000f0000f,0x1f666f2228888111102f0000f,0x1f666f2228888171100f0000f,0x1f666f22288f811110ff0000f]
def r5p81 : Keys := .leaf [
0x1f666f22a11110f0000f0000f,0x1f66e222a11110f0000f0000f,0x1f66ef22a11110f0000f0000f,0x1f88822221111066000f0000f]
def r5p82 : Keys := .leaf [
0x1f888222211110f4400f0000f,0x1f888222211110f4f00f0000f,0x1f888222211510f0000ff000f,0x1f888222211510f0f00f0000f]
def r5p83 : Keys := .leaf [
0x1f888222215510f0000f0000f,0x1f888226211110f0000ff000f,0x1f888226211110f0f00f0000f,0x1f888444422f211310f00000f]
def r5p84 : Keys := .leaf [
0x1f88844442f22111102f0000f,0x1f888446422f211110f00000f,0x1f88846443333111100f0000f,0x1f8884e442222111100f0000f]
def r5p85 : Keys := .leaf [
0x1f8884f442222111100f0000f,0x1f8884f442222111f00f00001,0x1f8884f442223111100f0000f,0x1f8884f44222a111100f0000f]
def r5p86 : Keys := .leaf [
0x1f8884f443222111100f0000f,0x1f888626211110f0000f0000f,0x1f888666622f211110ff0000f,0x1f888666633331f1100f0000f]
def r5p87 : Keys := .leaf [
0x1f888a2224f44111100f0000f,0x1f888f2224444111102f0000f,0x1f888f2224444131100f0000f,0x1f888f2224f441f1100f0000f]
def r5p88 : Keys := .leaf [
0x1f8894f442222111100f0000f,0x1f88a4f442222111100f0000f,0x1f8a84f442222111100f0000f,0x1f8c84f442222111100f0000f]
def r5p89 : Keys := .leaf [
0x1f8f84f442222111100f0000f,0x1f8f84f4f2222111100f0000f,0x1f8f85555222211f10f00000f,0x1f8f8626211110f0000f0000f]
def r5p90 : Keys := .leaf [
0x1f8f899f9555522220f00000f,0x1faaa444433331f1100f0000f,0x1faaa4e442222111100f0000f,0x1faaa4f44222f111100f0000f]
def r5p91 : Keys := .leaf [
0x1faaa4f443333111100f0000f,0x1faaa4f4f2222111100f0000f,0x1faaa555533330f0000f0000f,0x1faaa66661111060000f0000f]
def r5p92 : Keys := .leaf [
0x1faaa666611110f0000f0000f,0x1faaa666611110f0f00f0000f,0x1faaa66661f11111100f0000f,0x1faaa666f11110f0000f0000f]
def r5p93 : Keys := .leaf [
0x1faaa777711110f0000f0000f,0x1faaa88f8666611110f00000f,0x1faaaf2224444111102f0000f,0x1faaaf222444411110af0000f]
def r5p94 : Keys := .leaf [
0x1faaaf2224444131100f0000f,0x1faaaf2224f441f1100f0000f,0x1faaaf22255551f1100f0000f,0x1faaaf2225f551f1100f0000f]
def r5p95 : Keys := .leaf [
0x1faaaf22f44441f1100f0000f,0x1faaaf33344441f1100f0000f,0x1faaaf6661111060000f0000f,0x1faaaf66611110f0000f0000f]
def r5p96 : Keys := .leaf [
0x1faaaf66611110f0f00f0000f,0x1faaaf6661f110f0000f0000f,0x1faaaf6661f11111100f0000f,0x1faaaf66644441f1100f0000f]
def r5p97 : Keys := .leaf [
0x1fafa4f442222111100f0000f,0x1fafa666611110f0000f0000f,0x1fafa88f8666611110f00000f,0x1fafaf66611110f0000f0000f]
def r5p98 : Keys := .leaf [
0x1fbbbf66611110f0000f0000f,0x1fc884f442222111100f0000f,0x1ff3388884444120000f0000f,0x1ff88f22244441f1100f0000f]
def r5p99 : Keys := .leaf [
0x1ff99f22244441f1100f0000f,0x1ffbbf22244441f1100f0000f]
def r5 : Keys := .branch 0x1f2228f884444131100f0000f (.branch 0x1f2224444111b0f0000f0000f (.branch 0x1f0004444222a111102f0000f (.branch 0x18f884f443222111100f0000f (.branch 0x1544f222211110f0000f00008 (.branch 0x14444322211110f0800f0000f (r5p0) (.branch 0x14f443222111100f0000f0008 (r5p1) (r5p2))) (.branch 0x1888844443f33120000f0000f (r5p3) (.branch 0x18a8844443222111100f0000f (r5p4) (r5p5)))) (.branch 0x1b22299994f44111100f0000f (.branch 0x199994f443222111100f0000f (r5p6) (.branch 0x19f8844443222111100f0000f (r5p7) (r5p8))) (.branch 0x1baaa766611110f0000f0000f (r5p9) (.branch 0x1f000226a11110f0000f0000f (r5p10) (r5p11))))) (.branch 0x1f0f0aaaa666611110ff0000f (.branch 0x1f00099994444333302f0000f (.branch 0x1f0004f4f2222111100f00009 (r5p12) (.branch 0x1f00088885555333302f0000f (r5p13) (r5p14))) (.branch 0x1f000aaaa666611110af0000f (r5p15) (.branch 0x1f040222a11110f0000f0000f (r5p16) (r5p17)))) (.branch 0x1f222444411110f0000f9000f (.branch 0x1f22211110f4000f0000f0008 (r5p18) (.branch 0x1f22244441111020f00f00008 (r5p19) (r5p20))) (.branch 0x1f222444411110f0f08f8000f (.branch 0x1f222444411110f0900f0000f (r5p21) (r5p22)) (.branch 0x1f222444411190f0000f0000f (r5p23) (r5p24)))))) (.branch 0x1f22288881f1100f00044000f (.branch 0x1f222444f11190f0000f0000f (.branch 0x1f22244441f190f0000f0000f (.branch 0x1f22244441f1100f0000f0008 (r5p25) (.branch 0x1f22244441f110f0000f8000f (r5p26) (r5p27))) (.branch 0x1f22244441f191f1100f0000f (r5p28) (.branch 0x1f222444c1f1100f0000f0008 (r5p29) (r5p30)))) (.branch 0x1f222555d11190f0000f0000f (.branch 0x1f2224f4411190f0000f0000f (r5p31) (.branch 0x1f222555511110f0000f8000f (r5p32) (r5p33))) (.branch 0x1f222666611190f0000f0000f (r5p34) (.branch 0x1f222888811110f4f00f0000f (r5p35) (r5p36))))) (.branch 0x1f222889844441f1100f0000f (.branch 0x1f222888844441f1100f1000f (.branch 0x1f22288884444111102f2000f (r5p37) (.branch 0x1f22288884444131102f0000f (r5p38) (r5p39))) (.branch 0x1f2228888444f111102f0000f (r5p40) (.branch 0x1f22288885555111102f0000f (r5p41) (r5p42)))) (.branch 0x1f22288f844f444441f11000f (.branch 0x1f22288f8444411310f00000f (r5p43) (.branch 0x1f22288f8444433331f11000f (r5p44) (r5p45))) (.branch 0x1f222898844441f1100f0000f (.branch 0x1f22288f8666611110f0f000f (r5p46) (r5p47)) (.branch 0x1f2228a884644111100f0000f (r5p48) (r5p49))))))) (.branch 0x1f444f22a11110f0000f0000f (.branch 0x1f22a44441f1100f0000f0008 (.branch 0x1f2229f995f551f1100f0000f (.branch 0x1f22299f944441f1100f0000f (.branch 0x1f2228ff844441f1100f0000f (r5p50) (.branch 0x1f2229999444f1f1100f0000f (r5p51) (r5p52))) (.branch 0x1f2229f9944441f1100f0000f (r5p53) (.branch 0x1f2229f9955550f0000f0000f (r5p54) (r5p55)))) (.branch 0x1f222afaa44441f1100f0000f (.branch 0x1f222aaaa4444131100f0000f (r5p56) (.branch 0x1f222aaaa4f4f111100f0000f (r5p57) (r5p58))) (.branch 0x1f222bbbb55550f0000f0000f (r5p59) (.branch 0x1f22a444411110f0000f8000f (r5p60) (r5p61))))) (.branch 0x1f444222211110f0900f0000f (.branch 0x1f22faaaa44441f1100f0000f (.branch 0x1f22a444f11110f0000f0000f (r5p62) (.branch 0x1f22a666611110f0000f0000f (r5p63) (r5p64))) (.branch 0x1f262888811110f0000ff000f (r5p65) (.branch 0x1f44422221111020f00f00008 (r5p66) (r5p67)))) (.branch 0x1f444222a11110f0000f8000f (.branch 0x1f444222211190f0000f0000f (r5p68) (.branch 0x1f4442222111b0f0000f0000f (r5p69) (r5p70))) (.branch 0x1f44488882f22111102f0000f (.branch 0x1f444222a1f11111100f0000f (r5p71) (r5p72)) (.branch 0x1f444f22211110f0800f0000f (r5p73) (r5p74)))))) (.branch 0x1f888a2224f44111100f0000f (.branch 0x1f666f22a11110f0000f0000f (.branch 0x1f666222211190f0000f0000f (.branch 0x1f44cf22a11110f0000f0000f (r5p75) (.branch 0x1f44f222a11110f0000f0000f (r5p76) (r5p77))) (.branch 0x1f666aaaa11110f0f00f0000f (r5p78) (.branch 0x1f666f22211190f0000f0000f (r5p79) (r5p80)))) (.branch 0x1f88844442f22111102f0000f (.branch 0x1f888222211110f4400f0000f (r5p81) (.branch 0x1f888222215510f0000f0000f (r5p82) (r5p83))) (.branch 0x1f8884f442222111100f0000f (r5p84) (.branch 0x1f8884f443222111100f0000f (r5p85) (r5p86))))) (.branch 0x1faaa777711110f0000f0000f (.branch 0x1f8f899f9555522220f00000f (.branch 0x1f8894f442222111100f0000f (r5p87) (.branch 0x1f8f84f442222111100f0000f (r5p88) (r5p89))) (.branch 0x1faaa4f443333111100f0000f (r5p90) (.branch 0x1faaa666611110f0000f0000f (r5p91) (r5p92)))) (.branch 0x1faaaf66611110f0f00f0000f (.branch 0x1faaaf2224444131100f0000f (r5p93) (.branch 0x1faaaf22f44441f1100f0000f (r5p94) (r5p95))) (.branch 0x1fbbbf66611110f0000f0000f (.branch 0x1fafa4f442222111100f0000f (r5p96) (r5p97)) (.branch 0x1ff99f22244441f1100f0000f (r5p98) (r5p99)))))))

def a5p0 : Keys := .leaf [
0xc47c22279911088887801,0xc47c2a279111088887804,0xcc7c22279111088887801,0xf800447c222791110988b,0xf800447c232791110888e,0xf800457c222791110888b,0xf91122220f88807c00078,0xf91122220f8c80780007a,0xf91144440f8880780027d,0xf91144440fa880780007f,0xf9114fccafaa80780007a,0xf91522220f88807800078,0xf93144440f8880780007d,0xfa27c47c27a791110888c,0xfc7c47fc2227911108889,0xfd557b330f88807800078,0xa2221111088888078780007c1,0xa222111108888807878400781,0xa222111108888878078400079,0xa22211110888887c078000079,0xa2221111088c8807878000786,0xa2221111088c887807800007a,0xa22211110f888800007c00079,0xa22211110f88880400780007a,0xa22211110f888807807800042,0xa22211110f888878000780042,0xa22211110f8c8800007800079,0xa222111508888807878000784,0xa22211150888887807800007a,0xa22211150f88880000780007c,0xa222191108888780007c00078,0xa222191108888784007800078]
def a5p1 : Keys := .leaf [
0xa2221911088c8780007800078,0xa22219110f888078000780042,0xa222191508888780007800078,0xa2279111088888000780007c4,0xa227911108888804078000784,0xa227911108888878078000042,0xa2279111088c8800078000784,0xa227911508888800078000784,0xa227991108888780007800040,0xa7a2111108888800007c00079,0xa7a211110888880400780007a,0xa7a2111108888807807800042,0xa7a2111108888878000780042,0xa7a21111088c880000780007c,0xa7a211150888880000780007c,0xa7a2191108888078000780040,0xaa22111108888780007c00079,0xaa22111108888784007800078,0xaa221111088c8780007800078,0xaa22111508888780007800078,0xaa27911108888780007800040,0xc44411110888880787a000784,0xc444111108888827878000784,0xc44411110888887807800027c,0xc44411110888887807a00007c,0xc444111108a88807878000787,0xc444111108a8887807800007a,0xc44411110f88880000780027c,0xc44411110f888807807800207,0xc44411110f88882000780007f,0xc44411110f88887800200007f,0xc44411110fa8880000780007c]
def a5p2 : Keys := .leaf [
0xc444113108888807878000781,0xc444113108888878078000079,0xc44411310f888800007800079,0xc44419110888878000780027c,0xc4441911088887a000780007d,0xc444191108a8878000780007d,0xc44419110f88807800200007f,0xc44419310888878000780007d,0xc444222211110888880781781,0xc44422221111088888780107b,0xc44422221111088f887887806,0xc4442222111108f8880f87803,0xc444222211110907888880784,0xc444222211110978088880079,0xc444222211110988880780786,0xc44422221111098888780007b,0xc444222211110f88880780787,0xc444222211110f88880f80787,0xc444222211110f8888780007a,0xc444222211110f8888780807b,0xc444222211110f8888788007a,0xc444222211110f88890780786,0xc444222211110f8889780007b,0xc444222219110888810780784,0xc444222219110888817800079,0xc444222219110988807800078,0xc444222219110f8880780007a,0xc444222219110f88880780787,0xc444222219110f8888780007a,0xc44422221911888f878000785,0xc444222219118f8880780007a,0xc4442222191908f8878000078]
def a5p3 : Keys := .leaf [
0xc444222219190f8880780007f,0xc444222219998800010780784,0xc444222219998800017800079,0xc444222219998807810000786,0xc44422221999887801000007b,0xc444222219998900007800078,0xc44422221f998900007800078,0xc444222791110808878000784,0xc444222791110888880001784,0xc444222791110888887801006,0xc444222791110888887807804,0xc44422279111088888780787c,0xc444222791110888887807f84,0xc444222791110888887887804,0xc4442227911108f8880807804,0xc444222791110900088880784,0xc444222791110988880000784,0xc444222791110f80088888784,0xc444222791110f88880080781,0xc444222791110f88880780787,0xc444222791110f8888780007a,0xc444222791110f88888888784,0xc444222791110ff8088888784,0xc444222799110888810000786,0xc444222799110888878000784,0xc444222799110888878780784,0xc44422279911088887f800784,0xc444222799110888887807804,0xc444222799110f80088880784,0xc444222799110f8880780007f,0xc444222799110f88888880784,0xc444222799118888878000781]
def a5p4 : Keys := .leaf [
0xc444222799190888878000784,0xc444222799998800010000784,0xc444222799999111087807806,0xc444232211110888880780784,0xc44423221111088888780007c,0xc44423221911088880780007d,0xc44423221999880000780007c,0xc444232791110888880000784,0xc44427a21111080880780007c,0xc44427a211110888880780784,0xc44427a211110888880f80784,0xc44427a21111088888780007c,0xc44427a21111088888780807c,0xc44427a21111088888788007c,0xc44427a21111088f880080781,0xc44427a211110f88880780787,0xc44427a211110f8888780007a,0xc44427a21911088880780007d,0xc44427a219110888880780784,0xc44427a21911088888780007c,0xc44427a219110f8880780007f,0xc44427a219118888807800078,0xc44427a21919088880780007d,0xc44427a219999111080780786,0xc44427a21999911108780007e,0xc44427a222279111088888784,0xc44427a222279911088880784,0xc44427a791110888880780784,0xc44427a79111088888780007c,0xc44427a79911088880780007d,0xc44427a7a2279111088888784,0xc44427a7a2279911088880784]
def a5p5 : Keys := .leaf [
0xc4442807a22211110f8880787,0xc4442807a7a21111088880786,0xc44428281111088887f80007b,0xc4442828111108f887800007a,0xc444282811110f8880780007a,0xc444282f91110888878000784,0xc4442a2211110888810780786,0xc4442a221111088881780007e,0xc4442a221111098880780007f,0xc4442a2211110f88880780787,0xc4442a2211110f8888780007a,0xc4442a2219110f8880780007f,0xc4442a221999810000780007e,0xc4442a2791110888810000786,0xc4442a2791110888878000784,0xc4442a2791110888878780784,0xc4442a279111088887f800784,0xc4442a2791110888887807804,0xc4442a2791110f80088880784,0xc4442a2791110f87888880784,0xc4442a2791110f88880780787,0xc4442a2791110f88888880784,0xc4442a2799110888878000784,0xc4442a2799999111078000786,0xc4442a27a7a21111088880784,0xc4442a27a7a79111088880784,0xc4442a2a111108f8878000078,0xc4442a2f91110888878000784,0xc4442aaa9111087887800007a,0xc4442aaa91110f88880780787,0xc4442aaa91110f8888780007a,0xc4442aaa99110f8880780007f]
def a5p6 : Keys := .leaf [
0xc4442aaa99118780007800078,0xc4442aaaa80791110f8880787,0xc4442aaf91110800878000781,0xc4442b221111088880780007c,0xc4442fa211110888880780784,0xc4442fa21111088888780007c,0xc4442fa21911088880780007d,0xc4442fa22a279111088880784,0xc4442fa791110888880780784,0xc4442fa7aa279111088880784,0xc4442faa91110800807800079,0xc4442faa91110888880780784,0xc4442faa9111088888780007c,0xc4442faa91110f88880780787,0xc4442faa91110f8888780007a,0xc4442faa9911088880780007d,0xc4442faa99110f8880780007f,0xc4442faaa8079111088880786,0xc4442faaa80791110f8880787,0xc444333311110f88880780787,0xc444333311110f8888780007a,0xc444333319110f8880780007f,0xc444333319998807878000787,0xc44433331999887807800007a,0xc444391122220f8880780007a,0xc44439112aaa8f8880780007a,0xc44439112faa8f8880780007a,0xc44439390888878000780007d,0xc4443b3319110f8880780007f,0xc47c111108888800078000279,0xc47c111108888807878000207,0xc47c111108888820078000079]
def a5p7 : Keys := .leaf [
0xc47c111108a88800078000079,0xc47c113108888800078000079,0xc47c19110888878000200007d,0xc47c222211110808878000079,0xc47c222211110888880001079,0xc47c222211110888880781003,0xc47c222211110888880787801,0xc47c222211110888880787879,0xc47c222211110888880787f81,0xc47c222211110888880f87801,0xc47c22221111088f880087801,0xc47c222211110900088880079,0xc47c222211110988880000079,0xc47c222211110f80088888079,0xc47c222211110f87888888079,0xc47c222211110f88880780787,0xc47c222211110f8888080007c,0xc47c222211110f8888780007a,0xc47c222211110f88888888079,0xc47c22221911088881000007b,0xc47c222219110888878000079,0xc47c222219110888878780079,0xc47c22221911088887f800079,0xc47c222219110888880787801,0xc47c222219110f80088880079,0xc47c222219110f8880780007a,0xc47c222219110f88888880079,0xc47c222219118888878000079,0xc47c22221919088887800007c,0xc47c222219998800010000079,0xc47c222219999111080787803,0xc47c222791110888880001001]
def a5p8 : Keys := .leaf [
0xc47c222791110888880007801,0xc47c222791110888880007879,0xc47c222791110888880007f84,0xc47c222791110888880087801,0xc47c222791110888880787801,0xc47c222791110888880807804,0xc47c222791110888887807804,0xc47c222791110f80088888001,0xc47c222791110f88888888001,0xc47c222798001111088887803,0xc47c222799110888878000079,0xc47c222799110888878000784,0xc47c222799110888880007801,0xc47c222799111111088887803,0xc47c222799999111080007801,0xc47c2227a2221911088887801,0xc47c232211110888880000079,0xc47c27a211110888880780784,0xc47c27a211110888887800079,0xc47c27a21911088880780007d,0xc47c27a222221111088888079,0xc47c27a222221911088880079,0xc47c27a222279111088888001,0xc47c27a7a2279111088888001,0xc47c280022279111088887803,0xc47c2807a2221111088887803,0xc47c28281111088887800007b,0xc47c2a221111088881000007b,0xc47c2a2211110888878000079,0xc47c2a2211110888878780079,0xc47c2a221111088887f800079,0xc47c2a2211110888880787801]
def a5p9 : Keys := .leaf [
0xc47c2a2211110f80088880079,0xc47c2a2211110f88888880079,0xc47c2a2219110888878000079,0xc47c2a221999911107800007b,0xc47c2a2222279111088887801,0xc47c2a2227a21111088880079,0xc47c2a2291110888878000079,0xc47c2a2791110888878000079,0xc47c2a2791110888878000784,0xc47c2a2791110888880007804,0xc47c2a2791110888880787801,0xc47c2a27a2221111088887801,0xc47c2a27a2279111088887801,0xc47c2a27aa221111088887801,0xc47c2a2a11110888878000079,0xc47c2aaa91110800878000079,0xc47c2aaa91110888880787801,0xc47c2aaa91110f88880000079,0xc47c2aaa99110888878000079,0xc47c2aaaa80011110f888007b,0xc47c2aaaa8079111088887801,0xc47c2fa22a221111088880079,0xc47c333311110888880787803,0xc47c333319110888878000079,0xc47c333319998800078000079,0xc47c391122220888878000079,0xc47c39112aaa8888878000079,0xc47c3a221111088887800007b,0xc47c3b331111088887800007b,0xc47c3b3319110888878000079,0xc47c444422279911088887804,0xc47c44442a279111088887804]
def a5p10 : Keys := .leaf [
0xc544222211110888880780781,0xc544222211110888887800079,0xc544222219110888807800078,0xc544222219998800007800079,0xc544222791110888880000784,0xc5442a2211110888807800079,0xc57c222211110888880000079,0xc7c411110888880000780027c,0xc7c4111108888807807800207,0xc7c4111108888820007800079,0xc7c411110888887800200007f,0xc7c4111108a88800007800079,0xc7c4113108888800007800079,0xc7c419110888807800200007d,0xc7c4222211110808807800079,0xc7c4222211110888880780781,0xc7c4222211110888880f80781,0xc7c4222211110888887800079,0xc7c4222211110888887808079,0xc7c4222211110888887880079,0xc7c42222111108f888080007c,0xc7c4222211110f88880780787,0xc7c4222211110f8888780007a,0xc7c4222219110888807800078,0xc7c4222219110888880780781,0xc7c4222219110888887800079,0xc7c4222219110f8880780007a,0xc7c4222219118888807800078,0xc7c422221919088880780007d,0xc7c4222219999111080780783,0xc7c422221999911108780007b,0xc7c4222791110888880780784]
def a5p11 : Keys := .leaf [
0xc7c4222791110888887800079,0xc7c4222799110888807800078,0xc7c427a211110888880780784,0xc7c427a211110888887800079,0xc7c427a219110888807800078,0xc7c42807a2221111088880783,0xc7c428281111088880780007a,0xc7c42a2211110888807800079,0xc7c42a2211110888880780781,0xc7c42a2211110888887800079,0xc7c42a221911088880780007d,0xc7c42a221999911100780007a,0xc7c42a2291110888807800079,0xc7c42a2791110888807800079,0xc7c42a2791110888880780784,0xc7c42a2a11110888807800079,0xc7c42aaa91110800807800079,0xc7c42aaa91110888880780781,0xc7c42aaa91110888887800079,0xc7c42aaa9911088880780007d,0xc7c42aaaa8079111088880781,0xc7c4333311110888880780783,0xc7c433331111088888780007b,0xc7c433331911088880780007d,0xc7c4333319998800007800079,0xc7c4391122220888807800078,0xc7c439112aaa888880780007d,0xc7c43a221111088880780007b,0xc7c43b331111088880780007b,0xc7c43b331911088880780007d,0xc7c4444422279111088888784,0xc7c4444422279911088880784]
def a5p12 : Keys := .leaf [
0xc7c444442a279111088880784,0xc7c4447c22221111088888079,0xc7c4447c22221911088880079,0xc7c4447c22279111088888004,0xc7c4447c2a221111088880079,0xc7fc222211110888880780781,0xc7fc222211110888887800079,0xc7fc222219110888807800078,0xc7fc2a2211110888807800079,0xc7fc447c22221111088888079,0xc7fc447c22221911088880079,0xc7fc447c22279111088888004,0xc7fc447c2a221111088880079,0xc800447c22279111088887806,0xc804a22211110888878780786,0xc804a2221111088f878000786,0xc804a22211110f8880780007f,0xc804a22791110888878000786,0xc804a7a21111088880780007e,0xc804aaaa9111078000780007f,0xc8784444222211110f888007a,0xc878444422279111088887806,0xc878444427a2111108888007e,0xc87847c42222111108888007b,0xc87ca22211110888878000079,0xcc4411110888878000780027c,0xcc441111088887a000780007c,0xcc44111108a8878000780007d,0xcc4411310888878000780007d,0xcc44222211110888810780783,0xcc4422221111088881780007b,0xcc4422221111098880780007a]
def a5p13 : Keys := .leaf [
0xcc44222211110f88880780787,0xcc44222211110f8888780007a,0xcc44222219110f8880780007a,0xcc4422221999810000780007b,0xcc44222791110888810000786,0xcc44222791110888878000784,0xcc44222791110888878780784,0xcc4422279111088887f800784,0xcc44222791110888887807804,0xcc44222791110f80088880784,0xcc44222791110f88888880784,0xcc44222799110888878000784,0xcc44222799999111078000786,0xcc4423221111088880780007b,0xcc4427a21111088880780007c,0xcc4427a211110888880780784,0xcc4427a21111088888780007c,0xcc4427a219110888807800078,0xcc4427a21999911100780007f,0xcc4427a222279111088880784,0xcc4427a79111088880780007c,0xcc4427a7a2279111088880784,0xcc442a2211110f8880780007a,0xcc442a2791110888878000784,0xcc442aaa91110f8880780007f,0xcc442fa21111088880780007c,0xcc442faa9111088880780007c,0xcc4433331999878000780007d,0xcc44447c22279111088887804,0xcc4447c422279111088880784,0xcc44a2221111088f878000785,0xcc44a22791110888878000784]
def a5p14 : Keys := .leaf [
0xcc44a7a21111088880780007c,0xcc44aaaa9111078000780007d,0xcc4c222791110888878000784,0xcc4c27a21111088880780007c,0xcc7c11110888878000200007d,0xcc7c22221111088881000007b,0xcc7c222211110888878000079,0xcc7c222211110888878780079,0xcc7c22221111088887f800079,0xcc7c222211110888880787801,0xcc7c222211110f80088880079,0xcc7c222211110f8888780007a,0xcc7c222211110f88888880079,0xcc7c222211110ff8088880079,0xcc7c222219110888878000079,0xcc7c22221999911107800007b,0xcc7c222791110888878000079,0xcc7c222791110888878000784,0xcc7c222791110888880007801,0xcc7c222791110888887807804,0xcc7c2227a2221111088887801,0xcc7c27a21111088880780007c,0xcc7c27a211110888887800079,0xcc7c27a222221111088880079,0xcc7c2a2211110888878000079,0xcc7c2aaa91110888878000079,0xcc7c33331111088887800007b,0xcc7c444422279111088887804,0xcc7c447c22279111088887804,0xcc7c47c422221111088880079,0xcc7c47fc22221111088880079,0xcc7c4c4422279111088887804]
def a5p15 : Keys := .leaf [
0xcc7ca22211110888878000079,0xcccca2221111080f878000787,0xcccca22211110f88880780787,0xcccca22211110f8888780007a,0xcccca22219110f8880780007a,0xcccca2221919078000780007d,0xcccca22791110808078000784,0xcccca22791110888887807804,0xcccca22791110f88880000784,0xcccca22799110888878000784,0xcccca7a21111080800780007c,0xcccca7a211110888880780784,0xcccca7a21111088888780007c,0xcccca7a219110888807800078,0xcccca8281111078000780007a,0xccccaa2211110f8880780007a,0xccccaa2791110888878000784,0xccccaa2a11110780007800078,0xccccaaaa91110807878000787,0xccccaaaa9111087807800007a,0xccccaaaa99110780007800078,0xccccaaaaa8079111078000787,0xccccafaa9111080000780007c,0xccccafaaa800111100780007a,0xccccb9112aaa8780007800078,0xccccc800222791110f8880786,0xccccc8002faa911100780007f,0xccccc878222211110f888007a,0xccccc87822279111088887804,0xccccc87827a2111108888007c,0xccccc8782aaa911107800007a,0xccfca2221111080807800007c]
def a5p16 : Keys := .leaf [
0xcd44222211110888807800079,0xcfc4222211110888880780781,0xcfc4222211110888887800079,0xcfc4222219110888807800078,0xcfc42a2211110888807800079,0xcfc44c4422279111088880784,0xcfc44c7c22221111088880079,0xcfcca2221111080800780007c,0xcfcca22211110888880780781,0xcfcca22211110888887800079,0xcfcca22211110f88880780787,0xcfcca22211110f8888780007a,0xcfcca22219110888807800078,0xcfcca22219110f8880780007a,0xcfccaa2211110888807800079,0xcfccaaaa91110800007800079,0xcfccaaaaa800111100780007a,0xcfccafaa91110800007800079,0xcfccafaaa800111100780007a,0xcfccc8002aaa911100780007f,0xcfccc8002faa911100780007f,0xcfccc8782222111108888007b,0xcfccc878222211110f888007a,0xcffc222211110888887800079,0xcffc4c7c22221111088880079,0xd555222211110f88880780787,0xd555222211110f8888780007a,0xd555222219110f8880780007a,0xd555222219998807878000787,0xd55522221999887807800007a,0xd555222791110888887807806,0xd555222799110888878000784]
def a5p17 : Keys := .leaf [
0xd555222799998800078000784,0xd55527a211110888880780786,0xd55527a21111088888780007e,0xd55527a219110888807800078,0xd55527a21999880000780007c,0xd5552a2219998780007800078,0xd5552a2791110888878000786,0xd555333308888807878000787,0xd55533330888887807800007a,0xd55533330f888800007800079,0xd5553b330888878000780007d,0xd911444422220f8880780007f,0xd911444422278888878000784,0xd911444427a2088880780007d,0xd9114ccca2220f8880780007f,0xd9114ccca2278888878000784,0xd9114ccca7a20888807800078,0xd9114cccaaaa878000780007d,0xd9114fcca2220f8880780007f,0xd915a22208888780007800078,0xdc44222791110888878000786,0xdc4427a21111088880780007e,0xdd55222219110f8880780007a,0xdd55222791110888878000786,0xdd55222799110888878000784,0xdd5527a21111088880780007e,0xdd5527a219110888807800078,0xdd55333308888780007800078,0xdd553b3308888780007800078,0xea2247c41111088880780007a,0xea224ccc91110f8880780007a,0xea224fcc9111088880780007a]
def a5p18 : Keys := .leaf [
0xec4427a21111088880780007f,0xec442aaa91110f8880780007f,0xec442faa9111088880780007f,0xf800111108888780007c00279,0xf800111108888780007f80241,0xf80011110888878400780027e,0xf800111108888784007f80207,0xf8001111088887a0007c0007b,0xf8001111088887a0007f80042,0xf8001111088887a400780007a,0xf8001111088c878000780027f,0xf8001111088c8780007f80207,0xf8001111088c87a000780007a,0xf800111108a88780007c0007a,0xf800111108a88780007f80042,0xf800111108a8878400780007f,0xf800111108ac878000780007a,0xf80011110f88807800240007a,0xf80011110f888078002780042,0xf80011110f88807c00200007f,0xf80011110f88807f802000042,0xf80011110f8c807800200007f,0xf80011110fa88078000780042,0xf80011150888878000780027d,0xf800111508888780007f80205,0xf8001115088887a000780007a,0xf800111508a8878000780007a,0xf80011150f88807800200007f,0xf800113108888780007c00078,0xf800113108888780007f80040,0xf80011310888878400780007f,0xf8001131088c8780007800078]
def a5p19 : Keys := .leaf [
0xf80011310f888078000780042,0xf800113508888780007800078,0xf8002222111108888107807c3,0xf800222211110888817c0007b,0xf800222211110888857d0007b,0xf8002222111108888787807c9,0xf80022221111088c810780786,0xf80022221111088c817800078,0xf80022221111088c87f8007fe,0xf80022221111088f8780007cb,0xf800222211110988807c0007a,0xf80022221111098c80780007a,0xf800222211110d8d80780007a,0xf800222211110f8880780005a,0xf800222211110f88807c0007a,0xf800222211110f88807c80078,0xf800222211110f88807d0007a,0xf800222211110f8c80780007a,0xf800222211110f8c807c0007a,0xf800222211110f8c807f80787,0xf800222211110f8d80780007a,0xf800222211110f8f807800048,0xf800222211150888810780784,0xf800222211150888817800078,0xf80022221115088887f8007fc,0xf80022221115098880780007a,0xf800222211150f8880780007a,0xf800222211150f88807c0007a,0xf800222211150f88807f80787,0xf800222211150f8c80780007a,0xf800222211158888878780784,0xf80022221115888f878000787]
def a5p20 : Keys := .leaf [
0xf800222211158f8880780007a,0xf800222211178888850500784,0xf8002222111788888780007d1,0xf800222211178888878500781,0xf80022221117888d878000785,0xf800222211178f88807800052,0xf800222611110f88807c0007a,0xf800222611110f8c80780007a,0xf800222611150f8880780007a,0xf8002227911108888100007c6,0xf800222791110888810400786,0xf800222791110888817800040,0xf800222791110888850500784,0xf8002227911108888780007c4,0xf8002227911108888780007cc,0xf8002227911108888780007d6,0xf8002227911108888780047c4,0xf8002227911108888784007c6,0xf8002227911108888787807c6,0xf8002227911108888787847c4,0xf80022279111088887f8007c6,0xf80022279111088887fc007c6,0xf80022279111088c810000786,0xf80022279111088c878000786,0xf80022279111088c8780007c6,0xf80022279111088c878400786,0xf80022279111088c878780786,0xf80022279111088c87f800786,0xf80022279111088d878000786,0xf8002227911108ac878000787,0xf800222791110988807800042,0xf800222791110c8c878000786]
def a5p21 : Keys := .leaf [
0xf800222791110c8c878780786,0xf800222791110f88807800048,0xf800222791110f88807c0007a,0xf800222791110f888888807c6,0xf800222791110f88888c80786,0xf800222791110f8c80780007a,0xf800222791110f8c888c80786,0xf800222791150888810000786,0xf800222791150888878000784,0xf8002227911508888780007c4,0xf800222791150888878400784,0xf800222791150888878780784,0xf80022279115088887f800784,0xf80022279115088c878000785,0xf800222791150f8880780007a,0xf800222791150f88888880784,0xf800222791158888878000784,0xf800222791350888878000785,0xf800227f91110888878000241,0xf800232211110888807c0007b,0xf80023221111088c80780007a,0xf80023221115088880780007a,0xf800232791110888807800042,0xf80027a21111088880780005a,0xf80027a211110888807c0007b,0xf80027a211110888807c80079,0xf80027a211110888807d0007b,0xf80027a21111088c80780007a,0xf80027a21111088c807c0007a,0xf80027a21111088c807f80787,0xf80027a21111088d80780007a,0xf80027a21111088f807800048]
def a5p22 : Keys := .leaf [
0xf80027a211110c8c80780007f,0xf80027a211110f88807c0007a,0xf80027a211110f8c80780007a,0xf80027a21115088880780007a,0xf80027a211150888807c0007a,0xf80027a211150888807f80787,0xf80027a21115088c80780007a,0xf80027a211150f8880780007a,0xf80027a21115888880780007a,0xf80027a2222791110888807c6,0xf80027a222279111088c80786,0xf80027a222279115088880784,0xf80027a611110888807c0007b,0xf80027a61111088c80780007a,0xf80027a611110f8c80780007a,0xf80027a61115088880780007a,0xf80027a791110888807800048,0xf80027a791110888807c0007b,0xf80027a79111088c80780007a,0xf80027a791110c8c80780007f,0xf80027a79115088880780007a,0xf80027a7a22791110888807c6,0xf80027a7a22791110888847c4,0xf80027a7a2279111088c80786,0xf80027a7a22791110c8c80786,0xf80027a7a2279115088880784,0xf8002aaa91110f88807c0007a,0xf8002aaa91110f8c80780007a,0xf8002aaa91150f8880780007a,0xf8002aae91110f8c80780007a,0xf8002faa91110888807c0007b,0xf8002faa9111088c80780007a]
def a5p23 : Keys := .leaf [
0xf8002faa91110f88807c0007a,0xf8002faa91110f8c80780007a,0xf8002faa9115088880780007a,0xf8002faa91150f8880780007a,0xf8002fae9111088c80780007a,0xf8002fae91110f8c80780007a,0xf80033330888850500780007d,0xf800333311110f88807c0007a,0xf800333311110f8c80780007a,0xf800333311150f8880780007a,0xf800333711150f8880780007a,0xf800407c222211110f888007a,0xf800407c22279111088887806,0xf800407c27a2111108888007b,0xf800444411110888812780786,0xf80044441111088881780027e,0xf800444411110888833780786,0xf80044441111088887f8002fc,0xf8004444111108a8810780783,0xf8004444111108a881780007b,0xf8004444111108a88787807fb,0xf8004444111108f88780002fe,0xf80044441111098880780027e,0xf8004444111109a880780007f,0xf800444411110bb880780007f,0xf800444411110f8880380007f,0xf800444411110f8880780027f,0xf800444411110f888078002fd,0xf800444411110f8880780037f,0xf800444411110fa880780007f,0xf800444411110fa880780027f,0xf800444411110fa8807f8007a]
def a5p24 : Keys := .leaf [
0xf800444411110fb880780007f,0xf800444411110ff880280007d,0xf800444411310888810780785,0xf800444411310888817800078,0xf8004444113108888787807f9,0xf80044441131098880780007f,0xf800444411310f8880780007f,0xf800444411310f8880780027f,0xf800444411310f88807f8007a,0xf800444411310fa880780007f,0xf80044441139088887f800079,0xf8004444113908f887800007a,0xf800444411390f8880780007f,0xf800444411790888833000078,0xf80044441179088887800037c,0xf80044441179088887b00007c,0xf8004444117908b8878000078,0xf800444411790f8880300007f,0xf8004444202791110f8880787,0xf800444422221117888881794,0xf800444422221117898980787,0xf8004444222211178f8880797,0xf8004444222211178f8980787,0xf800444422221179088881179,0xf80044442222117909988007a,0xf8004444222211790f888017a,0xf8004444222211790f988007a,0xf800444422278888811100786,0xf800444422279111088881786,0xf800444422279111088881796,0xf800444422279111088885784,0xf800444422279111098880786]
def a5p25 : Keys := .leaf [
0xf800444422279111098881786,0xf800444422279111098980783,0xf800444422279111099880786,0xf8004444222791110d8880786,0xf8004444222791110f888078e,0xf8004444222791118f8880787,0xf80044442227911908f887806,0xf800444422279179088881106,0xf800444422279179088887904,0xf800444422279179089887804,0xf800444422279999888881784,0xf8004444222f911108f887806,0xf8004444223211790f888007a,0xf800444422379179088887804,0xf800444423279111088880786,0xf800444423279111088881786,0xf800444423279111098880786,0xf800444423279999888880784,0xf80044442332117908888007a,0xf800444423379111088880786,0xf800444427a21111088f8078e,0xf800444427a21111888f80787,0xf800444427a2117908888017c,0xf800444427a2117908988007a,0xf800444427b2117908888007a,0xf80044442aaa9999810780785,0xf80044442aaa9999817800078,0xf800444431310f8880780007a,0xf800444433330888817900078,0xf80044443333098980780007a,0xf800444433378888810100783,0xf8004444a22791110f8880787]
def a5p26 : Keys := .leaf [
0xf8004444a7a21111088f80787,0xf8004445222211178f8880787,0xf8004447a7a21111088c80786,0xf8004447a7a21115088880784,0xf800446411110f8880780027f,0xf800446411110fa880780007f,0xf800446411310f8880780007f,0xf800447c1111088881000027b,0xf800447c11110888810780205,0xf800447c1111088881200007b,0xf800447c11110888833000079,0xf800447c11110888878000279,0xf800447c111108888780002f9,0xf800447c1111088887800037b,0xf800447c11110888878002279,0xf800447c1111088887878027b,0xf800447c1111088887a00027b,0xf800447c1111088887a78027b,0xf800447c1111088887f80027b,0xf800447c1111088887f802279,0xf800447c111108a881000007b,0xf800447c111108a887800007b,0xf800447c111108a887800027b,0xf800447c111108a887878007b,0xf800447c111108a887a00007b,0xf800447c111108a887f80007b,0xf800447c111108ac87800007a,0xf800447c111108b887800007b,0xf800447c1111098880200007f,0xf800447c11110aa887800007b,0xf800447c11110aa887f80007b,0xf800447c11110f8880280007d]
def a5p27 : Keys := .leaf [
0xf800447c11110f8880780027f,0xf800447c11110f8888888027b,0xf800447c11110f8888a88007b,0xf800447c11110fa880780007f,0xf800447c11110fa888a88007b,0xf800447c1131088881000007b,0xf800447c11310888878000079,0xf800447c11310888878000279,0xf800447c11310888878780079,0xf800447c1131088887a000079,0xf800447c1131088887f800079,0xf800447c113108a8878000078,0xf800447c11310f8880780007f,0xf800447c11310f88888880079,0xf800447c11350888878000078,0xf800447c11390888878000079,0xf800447c20279111088887803,0xf800447c2222088881110007b,0xf800447c2222111108888107b,0xf800447c2222111108888117b,0xf800447c22221111088883079,0xf800447c2222111109888007b,0xf800447c2222111109888107b,0xf800447c2222111109898007b,0xf800447c2222111109988007e,0xf800447c222211110b888007b,0xf800447c222211110f88800fb,0xf800447c22221111888f87803,0xf800447c22221117888881013,0xf800447c22221117888887811,0xf800447c22221117888987801,0xf800447c222211190f888007a]
def a5p28 : Keys := .leaf [
0xf800447c22221999888881079,0xf800447c22279111088881003,0xf800447c22279111088881013,0xf800447c2227911108888107b,0xf800447c22279111088881106,0xf800447c22279111088881786,0xf800447c22279111088881801,0xf800447c22279111088883001,0xf800447c22279111088885004,0xf800447c22279111088887801,0xf800447c2227911108888780b,0xf800447c22279111088887813,0xf800447c22279111088887823,0xf800447c22279111088887846,0xf800447c22279111088887886,0xf800447c22279111088887906,0xf800447c22279111088887a03,0xf800447c22279111088887a43,0xf800447c22279111088887c06,0xf800447c22279111088887ffb,0xf800447c22279111088987803,0xf800447c22279111088c87806,0xf800447c22279111089887806,0xf800447c2227911108a887803,0xf800447c2227911108ac87803,0xf800447c2227911109888007b,0xf800447c22279111098880786,0xf800447c22279111098881003,0xf800447c22279111098887803,0xf800447c22279111098888889,0xf800447c222791110f800888b,0xf800447c222791110f88807fb]
def a5p29 : Keys := .leaf [
0xf800447c222791110f88888fb,0xf800447c222791110f8888f8e,0xf800447c222791110f8f8888b,0xf800447c222791110ff88888e,0xf800447c22279111888887801,0xf800447c22279115088887804,0xf800447c22279119088887804,0xf800447c22279131088887801,0xf800447c22279135088887801,0xf800447c22279911088887801,0xf800447c22279999888881003,0xf800447c2227999991110f88b,0xf800447c2227a22211110988b,0xf800447c222a11110f888007a,0xf800447c222f9111088887804,0xf800447c22379111088887806,0xf800447c2322111108888007b,0xf800447c2322111108888107b,0xf800447c2322111109888007b,0xf800447c23221999888880079,0xf800447c2322222791110888b,0xf800447c2323111108888007b,0xf800447c2327911108888007b,0xf800447c23279111088880786,0xf800447c23279111088881006,0xf800447c2327911108888107b,0xf800447c23279111088887806,0xf800447c2327a22211110888b,0xf800447c2327a22791110888b,0xf800447c2327a32211110888b,0xf800447c2332111108888007b,0xf800447c23a21111088880079]
def a5p30 : Keys := .leaf [
0xf800447c2780222791110888b,0xf800447c27a2111108888027b,0xf800447c27a2111108a88007b,0xf800447c27a21131088880079,0xf800447c27a791110888807fe,0xf800447c27a7a22791110888b,0xf800447c27a7a27f91110888e,0xf800447c27fa222791110888b,0xf800447c27ffa22791110888b,0xf800447c2a279111088887804,0xf800447c2aaa9111088881079,0xf800447c2aaa911109888007b,0xf800447c2aaa91110ff88007a,0xf800447c2aaa999981000007b,0xf800447c2aaf91110f888007a,0xf800447c2baa9111088880079,0xf800447c2baa911109888007b,0xf800447c2faa911108f88007a,0xf800447c2faaa22791110888b,0xf800447c2fafa22791110888b,0xf800447c31310888878000079,0xf800447c3333088881010007b,0xf800447c3333111108888107b,0xf800447c3333111108888307b,0xf800447c3333111109888007b,0xf800447c333311110b888007b,0xf800447c333311790f888007a,0xf800447c333319998f888007a,0xf800447c3337911108888787e,0xf800447c3337a7a791110888e,0xf800447c3bbb91110f888007a,0xf800447c4444222791110988e]
def a5p31 : Keys := .leaf [
0xf800447c4444232791110888e,0xf800447ca2221111088f87803,0xf800447ca2279111088887801,0xf800447d22221117888887801,0xf800447d22279111088887803,0xf800447f91110888878000244,0xf80045441111088880780027e,0xf8004544111108a880780007f,0xf80045441131088880780007f,0xf800454422279111088880786,0xf800454422279111088881786,0xf800454422279111098880786,0xf800454422279999888880784,0xf800454423279111088880786,0xf80045442aaa999980780007f,0xf8004544447c222791110888e,0xf800454522221117888880787,0xf800454522279111088880786,0xf80045453333088880780007f,0xf800455422279111088880786,0xf800457c1111088880200007f,0xf800457c2222111108888007b,0xf800457c2222111108888107b,0xf800457c2222111109888007b,0xf800457c22221999888880079,0xf800457c2227911108888007b,0xf800457c22279111088880786,0xf800457c22279111088881003,0xf800457c22279111088881786,0xf800457c22279111088887803,0xf800457c2227a22211110888b,0xf800457c2322111108888007b]
def a5p32 : Keys := .leaf [
0xf800457c2aaa9111088880079,0xf800457c3333111108888007b,0xf800457c4444222791110888e,0xf800457c447c222791110888e,0xf800457c4544222791110888e,0xf800457d2222111108888007b,0xf80045c422279111088880784,0xf8004780447c222791110888e,0xf80047c41111088880380007f,0xf80047c41111088880780027e,0xf80047c4111108888078002fc,0xf80047c41111088880780037e,0xf80047c4111108a880780007f,0xf80047c4111108a880780027f,0xf80047c4111108a8807f8007a,0xf80047c4111108b880780007f,0xf80047c4111108f880280007d,0xf80047c411110aa880780007a,0xf80047c411110f8880780027f,0xf80047c411110fa880780007f,0xf80047c41131088880780007f,0xf80047c41131088880780027f,0xf80047c411310888807f8007a,0xf80047c4113108a880780007f,0xf80047c411310f8880780007f,0xf80047c41139088880780007f,0xf80047c420279111088880786,0xf80047c42222111108f8800fb,0xf80047c422221117888880791,0xf80047c422221117888980787,0xf80047c42222111908f88007a,0xf80047c4222791110888807c6]
def a5p33 : Keys := .leaf [
0xf80047c422279111088c80786,0xf80047c422279115088880784,0xf80047c4222a111108f88007a,0xf80047c4227a111108a88007b,0xf80047c4227a1131088880079,0xf80047c43131088880780007a,0xf80047c4447c111108888027b,0xf80047c4447c111108a88007b,0xf80047c4447c1131088880079,0xf80047c522221117888880781,0xf80047c7c47c222791110888e,0xf80047e41111088880780027e,0xf80047e4111108a880780007f,0xf80047e411110fa880780007f,0xf80047e41131088880780007f,0xf80047fc1111088880280007d,0xf80047fc1111088880780027e,0xf80047fc111108a880780007f,0xf80047fc11110aa880780007a,0xf80047fc1131088880780007f,0xf80047fc222791110888807fb,0xf80047fc3333117908888007a,0xf80047fc447c111108888027b,0xf80047fc447c1111088882279,0xf80047fc447c111108a88007b,0xf80047fc447c11110aa88007b,0xf80047fc447c1131088880079,0xf80047fc447c222791110888e,0xf80047fc447fa22791110888b,0xf80047ffc47c222791110888e,0xf8004c7c22279111088887801,0xf8004ccc91110f8880780027f]
def a5p34 : Keys := .leaf [
0xf8004ccc91110fa880780007f,0xf8004ccc91310f8880780007f,0xf8004ccca2221999810780785,0xf8004ccca2221999817800078,0xf8004ccca2279111088881784,0xf8004ccca2279111098880786,0xf8004ccca22791110f8f80787,0xf8004ccca2279999810000786,0xf8004ccca322199980780007a,0xf8004ccca3279111088880784,0xf8004cccaaaa9111010780785,0xf8004cccaaaa9111017800078,0xf8004cccabaa911100780007f,0xf8004cccafaa911100780007f,0xf8004cccafaaa227911100787,0xf8004cccafaf911100780007f,0xf8004cccafafa227911100787,0xf8004cec91110fa880780007f,0xf8004cfca22791110f8880787,0xf8004cfcafaa911100780007f,0xf8004dcca2279111088880784,0xf8004dcca2279111098880786,0xf8004dccaaaa911100780007a,0xf8004dccabaa911100780007a,0xf8004fcc9111088880780027e,0xf8004fcc911108a880780007f,0xf8004fcc91110f8880780027f,0xf8004fcc91110fa880780007f,0xf8004fcc9131088880780007f,0xf8004fcc91310f8880780007f,0xf8004fcca2279111088f80787,0xf8004fccaaaa911100780007a]
def a5p35 : Keys := .leaf [
0xf8004fccaaaf911100780007a,0xf8004fccafaa911100780007a,0xf8004fccafaf911100780007f,0xf8004fccb333199980780007a,0xf8004fccbbbb911100780007a,0xf8004fccbfbb911100780007f,0xf8004fccc47c222791110888e,0xf8004fccc47c2aaa91110007a,0xf8004fec911108a880780007f,0xf8004fec91110fa880780007f,0xf8004ffcaaaa911100780007a,0xf8004ffcafaa911100780007a,0xf8004ffcc47c222791110888e,0xf8004ffcc47c2aaa91110007a,0xf800511522220f8880780007f,0xf800511522278888878000784,0xf800511527a2088880780007f,0xf800555508888330007800078,0xf800555511110f8880780027f,0xf800555511110fa880780007f,0xf800555511310f8880780007f,0xf800555522220888811780785,0xf80055552222099880780007f,0xf800555522278888811000786,0xf800555522279111088881786,0xf800555522279111088885786,0xf800555522279111098880786,0xf8005555222791110d8880786,0xf8005555222791178f8880787,0xf8005555222799998f8880787,0xf800555523279111088880786,0xf80055552332088880780007a]
def a5p36 : Keys := .leaf [
0xf800555527a79117888880787,0xf80055552faa999980780007f,0xf800555533330888810780785,0xf800555533330888817800078,0xf800555533330888830780785,0xf800555533330888857800078,0xf80055553333098880780007a,0xf800555533330b8880780007a,0xf800555533330d8880780007f,0xf800555533378888878780787,0xf800555533378f8880780007f,0xf80055553337a7a7888880787,0xf80055553bbb8f8880780007f,0xf800557511310f8880780007f,0xf800557d2222088881100007e,0xf800557d22279111088887f83,0xf800557d3333088887f80007a,0xf800557d33330f8880780007a,0xf800557d47fc222791110888b,0xf800557d47fc333308888007a,0xf8005ddda22791110f8880787,0xf8005dddafaa911100780007f,0xf8005dddb3330f8880780007a,0xf8005fddafaa911100780007a,0xf800667f91110888878000241,0xf80067e6447c222791110888b,0xf80067e7c47c222791110888b,0xf80067fe447c222791110888e,0xf80067ffc47c222791110888b,0xf800c444222791110f8880786,0xf800c44427a21111088f80786,0xf800c47c22221111088f87803]
def a5p37 : Keys := .leaf [
0xf800c47c22279111088887801,0xf801447c22279111088887801,0xf802447c22279111088887801,0xf80411110888878000780027c,0xf804111108888780007f80205,0xf8041111088887a000780007a,0xf804111108a8878000780007d,0xf80411110f88807800200007f,0xf80411310888878000780007d,0xf804222211110888810780783,0xf80422221111088881780007b,0xf80422221111088887f8007fb,0xf80422221111098880780007a,0xf804222211110f8880780007a,0xf804222211110f88807c0007a,0xf804222211110f88807f80787,0xf804222211110f8c80780007a,0xf804222211150f8880780007a,0xf804222611110f8880780007a,0xf8042227911108888780007c4,0xf804222791110888878400784,0xf804222791110888878780786,0xf80422279111088c878000786,0xf804222791110f8880780007a,0xf804222791150888878000784,0xf80423221111088880780007a,0xf80427a21111088880780007a,0xf80427a211110888807c00079,0xf80427a211110888807f80786,0xf80427a21111088c80780007a,0xf80427a211110f8880780007a,0xf80427a21115088880780007a]
def a5p38 : Keys := .leaf [
0xf80427a61111088880780007a,0xf80427a79111088880780007a,0xf8042aaa91110f8880780007a,0xf8042faa9111088880780007a,0xf8042faa91110f8880780007a,0xf804333311110f8880780007a,0xf804447c22279111088887804,0xf80447c422279111088880786,0xf804a22211110888878780783,0xf804a2221111088f878000783,0xf804a22211110f8880780007a,0xf804a7a21111088880780007a,0xf805222211110f8880780007a,0xf80527a21111088880780007a,0xf807a22211110888850500784,0xf807a222111108888780007d3,0xf807a22211110888878500781,0xf807a222111108888787807c1,0xf807a222111108888787847c1,0xf807a2221111088c878780786,0xf807a2221111088d878000786,0xf807a22211110c8c878780786,0xf807a22211110f88807800052,0xf807a22211110f88807c0007a,0xf807a22211110f8c80780007a,0xf807a22211150888878780784,0xf807a22211150f8880780007a,0xf807a227911108888780007c4,0xf807a22791110888878400784,0xf807a2279111088c878000786,0xf807a22791110f88807800042,0xf807a22791150888878000784]
def a5p39 : Keys := .leaf [
0xf807a7a211110888807800052,0xf807a7a211110888807c00079,0xf807a7a21111088c80780007a,0xf807a7a21115088880780007a,0xf807a7a791110888807800042,0xf807a7a791110888840400784,0xf807c004222791110f8880787,0xf807c00427a79111088880786,0xf807c07c2222111108888787b,0xf807c07c222211110f888007a,0xf807c07c22279111088887806,0xf807c07c27a21111088880079,0xf807c4441111088887a0007fc,0xf807c4441111088887a780786,0xf807c444111108a88780007fb,0xf807c444111108a8878780783,0xf807c44411110f8880780027f,0xf807c44411110f88807f80207,0xf807c44411110fa880780007a,0xf807c444113108888780007f9,0xf807c44411310888878780781,0xf807c44411310f8880780007a,0xf807c44422279111088881786,0xf807c44422279111098880786,0xf807c44423279111088880786,0xf807c44427a79111088880786,0xf807c44427a791110f8880786,0xf807c4442aaf91110f8880786,0xf807c4442faf9111088880786,0xf807c4442faf91110f8880786,0xf807c47c11110888878000279,0xf807c47c11110888878780205]
def a5p40 : Keys := .leaf [
0xf807c47c111108a887800007b,0xf807c47c11310888878000079,0xf807c47c2222111108888107b,0xf807c47c22221111088887ffb,0xf807c47c2222111109888007b,0xf807c47c222211110f88807fb,0xf807c47c222211110f88888fb,0xf807c47c222211110f8f8888b,0xf807c47c22279111088881003,0xf807c47c22279111088887879,0xf807c47c22279111088887f83,0xf807c47c222791110f8880787,0xf807c47c222791110f8888889,0xf807c47c2322111108888007b,0xf807c47c27a211110888807fe,0xf807c47c27a22227911108889,0xf807c47c27a79111088880786,0xf807c47c27a7a22211110888b,0xf807c47c27a7a22791110888b,0xf807c47c2aaa9111088887879,0xf807c47c2aaa91110f888007a,0xf807c47c2aaf9111088887804,0xf807c47c3333111108888787b,0xf807c54422279111088880786,0xf807c57c2222111108888007b,0xf807c78422279111088880784,0xf807c7c41111088880780027c,0xf807c7c411110888807f80207,0xf807c7c4111108a880780007a,0xf807c7c41131088880780007a,0xf807c7c4222791110f8880787,0xf807c7c427a79111088880784]
def a5p41 : Keys := .leaf [
0xf807c7c42aaf9111088880784,0xf807c7c4447c222791110888c,0xf807c7fc222211110888807fb,0xf807c7fc22279111088880784,0xf807c7fc447c222791110888b,0xf807cccca22211110f8f80783,0xf807cccca22791110f8880786,0xf807cccca7a21111088f80786,0xf807cccca7a79111088880784,0xf807ccccaaaa9111078780786,0xf807ccccaaaf9111078000785,0xf807ccccafaa911100780007a,0xf807cfcca2221111088f80783,0xf807cfcca22211110f8f80783,0xf807cfcca2279111088880784,0xf807cfcca22791110f8880787,0xf807cfccaaaa911100780007a,0xf807cfccafaa911100780007a,0xf807d11522220888878780784,0xf807d11522220f8880780007a,0xf807d11522278888878000784,0xf807d11527a2088880780007a,0xf807d555222791110f8880786,0xf807d55527a79111088880786,0xf807d55533330888878780784,0xf807d55533330f8880780007a,0xf80844442227911108f887806,0xf808447c222211110f888007b,0xf808447c22279111088887804,0xf80847c42222111108f88007b,0xf810447c22279111088887804,0xf820111108888780007c00079]
def a5p42 : Keys := .leaf [
0xf820111108888780007f80040,0xf820111108888784007800078,0xf8201111088c8780007800078,0xf82011110f888078000780042,0xf820111508888780007800078,0xf820444411110888810780786,0xf82044441111088881780007e,0xf8204444111108888787807fe,0xf82044441111098880780007f,0xf820444411110f8880780007f,0xf820444411110f8880780027f,0xf820444411110f88807f8007a,0xf820444411110fa880780007f,0xf820444411310f8880780007f,0xf820446411110f8880780007f,0xf820447c11110888878000279,0xf820447c1111088887a000079,0xf820447c1111088887f80007b,0xf820447c111108a887800007b,0xf820447c11110f8880780007f,0xf820447c11310888878000079,0xf820447c22279111088887801,0xf820447c27a2111108888007b,0xf82045441111088880780007e,0xf82047c41111088880780007f,0xf82047c41111088880780027c,0xf82047c411110888807f8007b,0xf82047c4111108a880780007f,0xf82047c411110f8880780007f,0xf82047c41131088880780007f,0xf82047e41111088880780007f,0xf82047fc1111088880780007f]
def a5p43 : Keys := .leaf [
0xf8204ccc91110f8880780007f,0xf8204fcc9111088880780007f,0xf8204fcc91110f8880780007f,0xf820555511110f8880780007f,0xf822444411110f8880780007a,0xf82247c41111088880780007a,0xf824111108888780007800078,0xf824447c22279111088887801,0xf827c44411110888878780784,0xf827c4441111088887a780784,0xf827c44411110f8880780007a,0xf827c44411110f8880780027f,0xf827c47c11110888878000279,0xf827c7c41111088880780007a,0xf827c7c41111088880780027c,0xf82844441111088887f80007e,0xf8284444111108f887800007e,0xf828444411110f8880780007f,0xf82847c41111088880780007f,0xf830444411110f8880780007f,0xf83047c41111088880780007f,0xf840447c22279111088887804,0xf844222211110f8880780007f,0xf84427a21111088880780007f,0xf8782222111108888784007f9,0xf87822221111088887fc0007b,0xf87822221111088c8780007fe,0xf87822221111088c87f80007e,0xf878222211110f88807c0007a,0xf878222211110f88807f80042,0xf878222211110f8c80780007f,0xf8782222111508888780007fc]
def a5p44 : Keys := .leaf [
0xf87822221115088887f80007c,0xf878222211150f8880780007f,0xf8782227911108888780007c4,0xf87822279111088887f800040,0xf87822279111088c878000786,0xf878222791150888878000784,0xf87827a211110888807c00079,0xf87827a211110888807f80042,0xf87827a21111088c80780007f,0xf87827a21115088880780007f,0xf878444411110888833000079,0xf87844441111088887800037e,0xf87844441111088887b00007c,0xf87844441111088887f80027c,0xf87844441111088887f80227c,0xf8784444111108a887f80007b,0xf8784444111108b887800007b,0xf878444411110aa887f80007b,0xf878444411110f8880300007f,0xf878444411110f8880780027f,0xf878444411110fa880780007f,0xf87844441131088887f800079,0xf878444411310f8880780007f,0xf878444420279111088887f86,0xf8784444202791110f8880787,0xf878444422279111088881786,0xf878444422279111088887ffe,0xf878444422279111098880786,0xf8784444222791110f88807fe,0xf8784444222791110f8888f8e,0xf8784444222791110ff88888e,0xf878444423279111088880786]
def a5p45 : Keys := .leaf [
0xf878444427a791110888807fe,0xf87844442aaa91110ff88007e,0xf87844442faa911108f88007e,0xf87844442faa91110ff88007e,0xf87844443131088887f800079,0xf878444431310f8880780007f,0xf878447c11110888878000279,0xf878447c1111088887a000079,0xf878447c111108a887800007b,0xf878447c11110f8880200007f,0xf878447c11310888878000079,0xf878447c202011110f888007a,0xf878447c20279111088887803,0xf878447c2222111108888107b,0xf878447c2222111109888007b,0xf878447c22279111088881006,0xf878447c22279111088887879,0xf878447c22279111088887f84,0xf878447c222791110f888007a,0xf878447c222791110f888888c,0xf878447c2322111108888007b,0xf878447c27a01111088880079,0xf878447c27a211110f888007a,0xf878447c27a22227911108889,0xf878447c27a79111088880079,0xf878447c27a7a22791110888e,0xf878447c2aaa91110f888007a,0xf878447c2faa9111088880079,0xf878447c2faa91110f888007a,0xf878447c31310888878000079,0xf878447c333311110f888007b,0xf878454422279111088880786]
def a5p46 : Keys := .leaf [
0xf878457c2222111108888007b,0xf87847c41111088880300007f,0xf87847c41111088880780027c,0xf87847c4111108a880780007f,0xf87847c41131088880780007f,0xf87847c420279111088880784,0xf87847c4222791110888807fb,0xf87847c42aaa911108f88007a,0xf87847c43131088880780007f,0xf87847c4447c222791110888c,0xf87847fc1111088880200007f,0xf87847fc11110888822000079,0xf87847fc2020111108888007b,0xf87847fc2222111108888007b,0xf87847fc222211110f888007b,0xf87847fc2227911108888007b,0xf87847fc27a21111088880079,0xf87847fc2aaa9111088880079,0xf87847fc3333111108888007b,0xf87847fc4444222791110888e,0xf87847fc447c222791110888e,0xf8784ccca2279111088887f84,0xf8784ccca22791110f8880787,0xf8784cccaaaa911107f80007a,0xf8784cccafaa911100780007f,0xf8784cfca22211110f888007b,0xf8784cfca2279111088887801,0xf8784cfca7a21111088880079,0xf8784cfcaaaa9111078000078,0xf8784fccaaaa911100780007f,0xf8784fccafaa911100780007f,0xf8784ffca222111108888007b]
def a5p47 : Keys := .leaf [
0xf8784ffca22211110f888007b,0xf878555522279111088887f86,0xf87855553333088887f800078,0xf878555533330f8880780007f,0xf87c22221111088887f800079,0xf87c22221111088887fc00079,0xf87c222211110f8880780007f,0xf87c222211110f88807c0007a,0xf87c2227911108888780007c4,0xf87c27a21111088880780007f,0xf87c27a211110888807c00079,0xf87fc44422279111088887f84,0xf87fc444222791110f8880786,0xf87fc44427a79111088880786,0xf87fc47c22221111088887879,0xf87fc47c222211110f888007b,0xf87fc47c22279111088887801,0xf87fc47c27a21111088880079,0xf87fc7c422279111088880784,0xf87fc7fc2222111108888007b,0xf888c44427a21111080780787,0xf888c44427a2111108780007a,0xf888c7c422221111080780787,0xf888c7c42222111108780007a,0xf888f800447c222791110f88b,0xf900444422279111088881786,0xf900444422279111098880786,0xf900444423279111088880786,0xf900447c2222111108888107b,0xf900447c2222111109888007b,0xf900447c22279111088881003,0xf900447c22279111088887801]
def a5p48 : Keys := .leaf [
0xf900447c2322111108888007b,0xf900454422279111088880786,0xf900457c2222111108888007b,0xf907c44423279111088880786,0xf907c47c2222111108888107b,0xf911088887800078002400078,0xf911088887800078002780040,0xf91108888780007c00200007d,0xf91108888780007f802000040,0xf91108888784007800200007d,0xf911088887a00078000780040,0xf911088c8780007800200007d,0xf91108a887800078000780040,0xf9110f8880780020000780040,0xf911222208888100007c0007b,0xf911222208888104007800078,0xf911222208888107807800040,0xf911222208888178000780040,0xf91122220888850500780007d,0xf911222208888780007800058,0xf911222208888780007c00078,0xf911222208888780007c80078,0xf911222208888780007d0007a,0xf911222208888780047c00078,0xf911222208888784007800078,0xf911222208888784007c00078,0xf911222208888784007f80785,0xf911222208888784807800078,0xf911222208888785007800078,0xf911222208888787807800048,0xf911222208888787807c00078,0xf911222208888787847c00078]
def a5p49 : Keys := .leaf [
0xf9112222088887c400780007d,0xf9112222088887f8007c00078,0xf9112222088887f8007f80040,0xf9112222088887fc00780007d,0xf9112222088887fc007c00078,0xf9112222088c810000780007e,0xf9112222088c8780007800078,0xf9112222088c8780007c00078,0xf9112222088c8780007f80785,0xf9112222088c8784007800078,0xf9112222088c8787807800078,0xf9112222088c87f800780007d,0xf9112222088d8780007800078,0xf9112222088f8780007800048,0xf911222209888078000780040,0xf91122220c8c878000780007d,0xf91122220c8c8787807800078,0xf91122220f888078000780040,0xf91122220f888078000780048,0xf91122220f888078000780052,0xf91122220f88807800440007d,0xf91122220f88807c000780040,0xf91122220f88807c00780007d,0xf91122220f88807f807800040,0xf91122220f88840400780007d,0xf91122220f888780007c00078,0xf91122220f888784007800078,0xf91122220f888888807c00078,0xf91122220f88888c807800078,0xf91122220f8c8078000780042,0xf91122220f8c8780007800078,0xf91122220f8c8784007800078]
def a5p50 : Keys := .leaf [
0xf91122220f8c8888807800078,0xf91122220f8c888c807800078,0xf91122220f8c8f88807800078,0xf911222211110f88807c0007a,0xf911222211110f8c80780007a,0xf911222211150f8880780007a,0xf911222608888780007c00078,0xf911222608888784007800078,0xf9112226088c8780007800078,0xf91122260f888078000780040,0xf911222788888780007800052,0xf911222788888780007c00078,0xf911222788888784007800078,0xf911222788888787807800040,0xf911222788888787840400785,0xf9112227888c8780007800078,0xf91122278f888078000780040,0xf9112227911108888780007c4,0xf91122279111088c878000786,0xf911222791150888878000784,0xf91127a208888780007c00078,0xf91127a208888784007800078,0xf91127a2088c8780007800078,0xf91127a20f888078000780040,0xf91127a211110888807c0007b,0xf91127a21111088c80780007a,0xf91127a211150888807800078,0xf91127a608888784007800078,0xf9112aaa88888780007c00078,0xf9112aaa88888784007800078,0xf9112aaa888c8780007800078,0xf9112aaa8f888078000780040]
def a5p51 : Keys := .leaf [
0xf9112aae888c8780007800078,0xf9112faa8f888078000780040,0xf911333308888780007c00078,0xf911333308888784007800078,0xf9113333088c8780007800078,0xf91133330f888078000780042,0xf911400422220f8880780007f,0xf91144440888810000780027e,0xf911444408888107807800205,0xf91144440888812000780007d,0xf91144440888817800200007d,0xf911444408888330007800078,0xf91144440888878000380007d,0xf91144440888878000780027d,0xf9114444088887800078002fd,0xf91144440888878000780037f,0xf911444408888780022780785,0xf91144440888878780780027d,0xf911444408888787807f80205,0xf9114444088887a000780007d,0xf9114444088887a000780027d,0xf9114444088887a0007f80078,0xf9114444088887a2007800078,0xf9114444088887a7807800078,0xf9114444088887a780780027d,0xf9114444088887a800780007d,0xf9114444088887b000780007d,0xf9114444088887f800280007d,0xf9114444088887f800780027d,0xf9114444088887f8022780785,0xf911444408a8810000780007b,0xf911444408a8878000780007d]
def a5p52 : Keys := .leaf [
0xf911444408a8878000780027d,0xf911444408a88780007f80078,0xf911444408a88787807800078,0xf911444408a887a000780007d,0xf911444408a887f800780007d,0xf911444408b8878000780007d,0xf911444408f8878000280007d,0xf91144440988807800200007d,0xf91144440aa88780007800078,0xf91144440aa887f800780007d,0xf91144440f88807800200007d,0xf91144440f888078002200078,0xf91144440f888078002780078,0xf91144440f888078002780205,0xf91144440f88807800280007d,0xf91144440f88807800300007f,0xf91144440f88807f80200007d,0xf91144440f888220007800078,0xf91144440f88878000780027d,0xf91144440f8887a000780007d,0xf91144440f88888880780027d,0xf91144440f8888a880780007d,0xf91144440fa8807800200007f,0xf91144440fa8878000780007d,0xf91144440fa887a000780007d,0xf91144440fa8888880780007d,0xf91144440fa888a880780007d,0xf91144440fa88f8880780007d,0xf911444411110f8880780027f,0xf911444411110fa880780007f,0xf911444411310f8880780007f,0xf911444420200f8880780007a]
def a5p53 : Keys := .leaf [
0xf911444422220888810780785,0xf911444422220888811780785,0xf911444422220888817800078,0xf911444422220888817801079,0xf911444422220888817900078,0xf911444422220888830780785,0xf911444422220888857800078,0xf91144442222088f87800078d,0xf9114444222208f88780000f8,0xf911444422220907888880784,0xf911444422220978088880079,0xf911444422220988807800078,0xf911444422220988810780785,0xf911444422220988817800078,0xf911444422220989807800078,0xf91144442222099880780007d,0xf911444422220b88807800078,0xf911444422220d8880780007d,0xf911444422220f88807800078,0xf911444422220f888078000fd,0xf911444422220f8880780017f,0xf911444422220f8880780027d,0xf911444422220f88807880078,0xf911444422220f8880790007a,0xf911444422220f88807c00078,0xf911444422220f88810780785,0xf911444422220f88817800078,0xf911444422220f88880780787,0xf911444422220f8888780007a,0xf911444422220f88890780785,0xf911444422220f88897800078,0xf911444422220f8980780007a]
def a5p54 : Keys := .leaf [
0xf911444422220f8c80780007a,0xf911444422220f9880780007f,0xf911444422220fa880780007f,0xf911444422228f8880780007d,0xf911444422230f8880780007f,0xf911444422260f8880780007d,0xf911444422278888810100783,0xf911444422278888810780785,0xf911444422278888817800078,0xf911444422278888878000794,0xf911444422278888878100784,0xf91144442227888887f8007fc,0xf91144442227888887ff80784,0xf911444422278889878000785,0xf91144442227898880780007d,0xf911444422278f88807f80785,0xf911444422278f88888f80785,0xf911444422278f8f888880784,0xf911444422279111088881786,0xf911444422279111098880786,0xf9114444222791178f8880787,0xf911444422279179088887f84,0xf9114444222799998f8880785,0xf9114444222a08f8878000078,0xf9114444222a0f8880780007d,0xf911444422320f8880780007f,0xf911444422a20f8880780007d,0xf911444423220888810780785,0xf911444423220888817800078,0xf91144442322098880780007d,0xf911444423220f8880780007d,0xf911444423278888810780785]
def a5p55 : Keys := .leaf [
0xf911444423279111088880786,0xf911444426220f8880780007d,0xf911444427a20888810780785,0xf911444427a20888817800078,0xf911444427a2098880780007d,0xf911444427a78f8880780007d,0xf911444427a79117888880784,0xf91144442a220f8880780007f,0xf91144442aaa8888810780785,0xf91144442aaa8888817800078,0xf91144442aaa898880780007d,0xf91144442aaa8ff880780007f,0xf91144442aaf8f8880780007d,0xf91144442b220f8880780007d,0xf91144442baa898880780007d,0xf91144442faa8f8880780007d,0xf91144442faa8ff880780007f,0xf91144442faa999980780007f,0xf91144442faa9f9980780007f,0xf91144442faf8f8880780007d,0xf911444432220f8880780007f,0xf911444433330888810780785,0xf911444433330888817800078,0xf911444433330888830780785,0xf91144443333098880780007d,0xf911444433330b88807800078,0xf911444433378888878780784,0xf911444433378f8880780007f,0xf911444437b30f8880780007d,0xf91144443bbb8f8880780007d,0xf91144443fbb8f8880780007d,0xf9114444a222088f878000785]
def a5p56 : Keys := .leaf [
0xf9114444a2220f88807800078,0xf911444522220f8880780007a,0xf911444522278888878000785,0xf9114447c44422278f8880785,0xf911444c22220f88807800078,0xf911445422220f8880780007a,0xf91144640888878000780027d,0xf9114464088887a000780007d,0xf911446408a8878000780007d,0xf91144640f88807800200007d,0xf911446422220f88807800078,0xf911447c0888878000300007f,0xf911447c0888878000780027d,0xf911447c088887a000780007d,0xf911447c088887f800200007d,0xf911447c088887f8022000078,0xf911447c08a8878000780007d,0xf911447c0f88807800200007d,0xf911447c11110888878000279,0xf911447c111108a887800007b,0xf911447c11310888878000079,0xf911447c22220888810780785,0xf911447c2222088881100007e,0xf911447c22220888817800078,0xf911447c22220888878000179,0xf911447c222208888787807f9,0xf911447c22220888879000079,0xf911447c2222088887ff80079,0xf911447c22220898878000078,0xf911447c22220988807800078,0xf911447c22220f88807f80078,0xf911447c22220f8888f880078]
def a5p57 : Keys := .leaf [
0xf911447c22220ff8888880079,0xf911447c2222111108888107b,0xf911447c2222111109888007b,0xf911447c22221117888887879,0xf911447c222211790f888007a,0xf911447c222219998f8880078,0xf911447c222788888780007f9,0xf911447c22278888878780785,0xf911447c2227888887f800078,0xf911447c22278f88807800078,0xf911447c22279111088881003,0xf911447c2227911108888787b,0xf911447c22279111088887f86,0xf911447c222791110f8888889,0xf911447c22279117888887801,0xf911447c22279179088887804,0xf911447c22279791088887801,0xf911447c22279999888887801,0xf911447c22320888878000078,0xf911447c227a22220f8880078,0xf911447c2322111108888007b,0xf911447c27a20f8880780007d,0xf911447c27a21179088880078,0xf911447c27a2222791110888b,0xf911447c27a7a22791110888b,0xf911447c2aaa888887f800079,0xf911447c2aaa88f8878000078,0xf911447c2aaa8f8880780007d,0xf911447c2aaa91110f888007b,0xf911447c2aaa9999878000078,0xf911447c2faa8f8880780007d,0xf911447c3333088881000007b]
def a5p58 : Keys := .leaf [
0xf911447c33330888830000079,0xf911447c33330888878780078,0xf911447c3333088887f800078,0xf911447c33330f8880780007f,0xf911447c33330f88888880079,0xf911447c33378888878000078,0xf911447c3bbb8888878000078,0xf91144c422220f88807800078,0xf911454422220888810780785,0xf911454422220888817800078,0xf911454422220988807800078,0xf911454422220f88807800078,0xf911454422279111088880786,0xf911454423220888807800078,0xf911454427a2088880780007d,0xf91145443333088880780007d,0xf911457c22220888817800078,0xf911457c2222111108888007b,0xf911464422220f88807800078,0xf91147443333088880780007d,0xf91147c40888878000780027d,0xf91147c4088887a000780007d,0xf91147c408a8878000780007d,0xf91147c40f88807800200007d,0xf91147c41111088880780027e,0xf91147c4111108a880780007f,0xf91147c41131088880780007d,0xf91147c422220888810780785,0xf91147c422220888817800078,0xf91147c422220988807800078,0xf91147c422278f88807800078,0xf91147c422279117888880784]
def a5p59 : Keys := .leaf [
0xf91147c423220888807800078,0xf91147c427a20f88807800078,0xf91147c427a7888880780007d,0xf91147c42aaa8f8880780007d,0xf91147c42aaa999980780007a,0xf91147c42faa888880780007d,0xf91147c42faa8f8880780007d,0xf91147c433330f8880780007d,0xf91147c43337888880780007d,0xf91147c437b3088880780007d,0xf91147c43bbb888880780007d,0xf91147c4447c222791110888e,0xf91147c4447c3333088880079,0xf91147e4088887a000780007d,0xf91147fc22220f88807800078,0xf91147fc22221179088880079,0xf91147fc27a20888807800078,0xf91147fc3333088880780007d,0xf91147fc447c222791110888e,0xf91147fc447c3333088880079,0xf9114c4422220f8880780007a,0xf9114ccc8888878000780027d,0xf9114ccc888887a000780007d,0xf9114ccc88a8878000780007d,0xf9114ccc8f88807800200007d,0xf9114ccca2220888810780785,0xf9114ccca2220888817800078,0xf9114ccca2220988807800078,0xf9114ccca2220f8f80780007a,0xf9114ccca2278888878780784,0xf9114ccca227888f878000785,0xf9114ccca2278f88807800078]
def a5p60 : Keys := .leaf [
0xf9114ccca22791110f8880786,0xf9114ccca2279999878000785,0xf9114ccca7a20f88807800078,0xf9114ccca7a2199980780007f,0xf9114cccaaaa810000780007b,0xf9114cccaaaa8787807800078,0xf9114cccaaaa87f800780007d,0xf9114cccaaaa8f88807800078,0xf9114cccaaaf878000780007d,0xf9114cccafaa878000780007d,0xf9114cccafaa8f8880780007d,0xf9114cccafaa911100780007f,0xf9114cccb3330f8880780007a,0xf9114cccbbbb878000780007d,0xf9114cec88a8878000780007d,0xf9114cfca2220f88807800078,0xf9114cfcaaaa8780007800078,0xf9114d4422220f88807800078,0xf9114dcca2220988807800078,0xf9114fcc8f88807800200007d,0xf9114fcca2220f88807800078,0xf9114fcca2220f8f80780007a,0xf9114fcca222199980780007a,0xf9114fcca2221f9980780007a,0xf9114fcca2278f88807800078,0xf9114fcca7a20888807800078,0xf9114fcca7a20f88807800078,0xf9114fccaaaa8780007800078,0xf9114fccaaaa8f88807800078,0xf9114fccaaaa911100780007a,0xf9114fccafaa8780007800078,0xf9114fccafaa8888807800078]
def a5p61 : Keys := .leaf [
0xf9114fccafaa8f88807800078,0xf9114fccafaa911100780007a,0xf9114fccafaaa22200780007a,0xf9114fccb333088880780007d,0xf9114fccb3330f8880780007a,0xf9114fccc4442faa80780007f,0xf9114ffca2220f88807800078,0xf911544422220f8880780007a,0xf91155550888878000780027d,0xf9115555088887a000780007d,0xf911555508a8878000780007d,0xf91155550f88807800200007f,0xf911555522220888810780785,0xf911555522220888817800078,0xf911555522220888857800078,0xf911555522220988807800078,0xf911555522220d8880780007d,0xf911555522278888810000786,0xf911555522278888850000784,0xf911555522278888878780784,0xf91155552227888887f800785,0xf911555522278f8880780007a,0xf911555522278f88888880784,0xf911555523220888807800078,0xf911555527220888807800078,0xf911555527a20f88807800078,0xf911555527a22227888880784,0xf911555527a78888807800078,0xf911555527a7a227888880784,0xf91155552aaa8f88807800078,0xf91155552faa8888807800078,0xf91155552faa8f8880780007f]
def a5p62 : Keys := .leaf [
0xf911555533330f8880780007a,0xf911557d2222088887f800079,0xf911557d22220f8880780007a,0xf911557d22278888878000785,0xf911557d27a20888807800078,0xf91157d522220f88807800078,0xf91157d527a20888807800078,0xf9115ddda2220f88807800078,0xf9115ddda2278888878000785,0xf9115ddda7a20888807800078,0xf9115dddaaaa8780007800078,0xf9115fdda2220f88807800078,0xf911622244440f8880780007f,0xf911644422220f8880780007a,0xf911780022220f88807c0007a,0xf911780022220f8c80780007a,0xf911780044440f8880780027f,0xf911780044440fa880780007f,0xf91178004fccafaa80780007a,0xf911780422220f8880780007a,0xf911782044440f8880780007f,0xf911c4442222088f878000785,0xf911c44422220f88807800078,0xf91508888780007800200007d,0xf91522220888810000780007b,0xf915222208888780007800078,0xf915222208888780007c00078,0xf915222208888780007f80785,0xf915222208888784007800078,0xf915222208888787807800078,0xf9152222088887f800780007d,0xf9152222088c8780007800078]
def a5p63 : Keys := .leaf [
0xf91522220f888078000780040,0xf91522220f888780007800078,0xf91522220f888888807800078,0xf915222211110f8880780007a,0xf915222211150f8880780007a,0xf915222608888780007800078,0xf915222788888780007800078,0xf915222791150888878000784,0xf91527a208888780007800078,0xf91527a21111088880780007a,0xf91527a211150888807800078,0xf9152aaa88888780007800078,0xf915333308888780007800078,0xf915333708888780007800078,0xf915444422220f88807800078,0xf915780022220f8880780007a,0xf915780422220f8880780007a,0xf915791122220f8880780007a,0xf915a22208888780007800078,0xf917a22208888780007800052,0xf917c444222791110f8880786,0xf917c44427a79111088880786,0xf917c47c22221111088887879,0xf917c47c22279111088887801,0xf917c7c422279111088880784,0xf917d55522220888878780781,0xf917d55522220f88807800078,0xf917d55522278888878000785,0xf917d55527a20888807800078,0xf9194444222208f8878000078,0xf919444422220f8880780007d,0xf931088887800078000780040]
def a5p64 : Keys := .leaf [
0xf93144440888810000780007e,0xf93144440888878000780007d,0xf93144440888878000780027d,0xf931444408888780007f80078,0xf931444408888787807800078,0xf9314444088887a000780007d,0xf9314444088887f800780007d,0xf931444408a8878000780007d,0xf93144440f88807800200007d,0xf93144440f88878000780007d,0xf93144440f88888880780007d,0xf931444411110f8880780007f,0xf931444411310f8880780007f,0xf931444422220f8880780007d,0xf93144640888878000780007d,0xf931447c0888878000780007d,0xf931447c11310888878000079,0xf93147c40888878000780007d,0xf93147c41111088880780007f,0xf93147c41131088880780007d,0xf9314ccc8888878000780007d,0xf93155550888878000780007d,0xf93155750888878000780007d,0xf931780044440f8880780007f,0xf931782044440f8880780007f,0xf931791144440f8880780007f,0xf93944440888878000780007d,0xf978444422279111088881786,0xf978457c2222111108888007b,0xf97944440888878000300007f,0xf979444422279111088887f84,0xf97944443333088887f80007c]
def a5p65 : Keys := .leaf [
0xf979444433330f8880780007d,0xf979447c222211110f888007b,0xf979447c22279111088887804,0xf979447c27a21111088880079,0xf979447c33330888878000078,0xf97947c43333088880780007d,0xf97947fc2222111108888007b,0xf999c4442222090000780007a,0xfa00447c22279111088887801,0xfa20447c1111088887f80007b,0xfa2047c41111088880780007b,0xfa2047fc1111088880780007b,0xfa22111108888100007c0007b,0xfa22111108888104007800078,0xfa22111108888107807800040,0xfa22111108888178000780040,0xfa2211110888850500780007c,0xfa22111108888780007800058,0xfa22111108888780007c00079,0xfa22111108888780007c80079,0xfa22111108888780007d0007b,0xfa22111108888780047c00079,0xfa22111108888784007800078,0xfa22111108888784007c0007b,0xfa22111108888784007f80784,0xfa22111108888784807800078,0xfa22111108888785007800078,0xfa22111108888787807800048,0xfa22111108888787807c0007b,0xfa22111108888787847c0007b,0xfa221111088887c400780007d,0xfa221111088887f8007c0007b]
def a5p66 : Keys := .leaf [
0xfa221111088887f8007f80040,0xfa221111088887fc00780007d,0xfa221111088887fc007c0007b,0xfa221111088c810000780007e,0xfa221111088c8780007800078,0xfa221111088c8780007c00078,0xfa221111088c8780007f80785,0xfa221111088c8784007800078,0xfa221111088c8787807800078,0xfa221111088c87f800780007d,0xfa221111088d8780007800078,0xfa22111109888078000780042,0xfa2211110c8c878000780007d,0xfa2211110c8c8787807800078,0xfa2211110f888888807c00079,0xfa2211110f88888c80780007a,0xfa2211110f8c8888807800078,0xfa2211110f8c888c80780007a,0xfa2211150888810000780007e,0xfa22111508888780007800078,0xfa22111508888780007c00078,0xfa22111508888780007f80785,0xfa22111508888784007800078,0xfa22111508888787807800078,0xfa221115088887f800780007d,0xfa221115088c8780007800078,0xfa2211150f888888807800078,0xfa22111588888780007800078,0xfa22111788888780007800052,0xfa222227911108888780007c4,0xfa2222279111088c878000786,0xfa22222791150888878000784]
def a5p67 : Keys := .leaf [
0xfa2227a211110888807c00079,0xfa2227a21111088c80780007a,0xfa2227a211150888807800078,0xfa2244440888811100780007e,0xfa22444411110888810780786,0xfa22444411110888811780786,0xfa2244441111088881780007e,0xfa2244441111088881780107e,0xfa2244441111088881790007e,0xfa22444411110888830780784,0xfa2244441111088885780007c,0xfa224444111108f88780000fe,0xfa2244441111098880780007f,0xfa22444411110988810780786,0xfa2244441111098881780007e,0xfa2244441111098980780007a,0xfa2244441111099880780007f,0xfa22444411110d8880780007f,0xfa22444411110f88880780787,0xfa22444411110f8888780007a,0xfa22444411178888810100783,0xfa22444411178888878000794,0xfa22444411178888878100784,0xfa22444411178889878000785,0xfa224444111908f8878000078,0xfa22444417910888810780785,0xfa22444417910888817800078,0xfa22444419110f8880780007f,0xfa22444419998888810780784,0xfa2244441999888881780007c,0xfa22444422279111088881786,0xfa22444422279111098880786]
def a5p68 : Keys := .leaf [
0xfa22444423279111088880786,0xfa22444511178888878000785,0xfa2244479111088c878000786,0xfa22444791150888878000784,0xfa22447c11110888810780786,0xfa22447c1111088881780007b,0xfa22447c11110888878000279,0xfa22447c111108888787807fc,0xfa22447c1111088887a000079,0xfa22447c1111088887ff8007b,0xfa22447c111108a887800007b,0xfa22447c1111098880780007f,0xfa22447c11110f8888f88007a,0xfa22447c11110ff888888007b,0xfa22447c11310888878000079,0xfa22447c2222111108888107b,0xfa22447c2222111109888007b,0xfa22447c22279111088881003,0xfa22447c2227911108888787b,0xfa22447c22279111088887f83,0xfa22447c222791110f8888889,0xfa22447c2322111108888007b,0xfa22447c27a22227911108889,0xfa22447c27a7911108888007b,0xfa22447c27a7a22791110888b,0xfa22447c27fa111108888007b,0xfa22447c2faa911108888007b,0xfa2245441111088880780007e,0xfa22454411110888810780786,0xfa2245441111088881780007e,0xfa2245441111098880780007a,0xfa2245441999888880780007d]
def a5p69 : Keys := .leaf [
0xfa22454422279111088880786,0xfa2245451111088880780007e,0xfa2245541111088880780007e,0xfa22457c1111088880780007e,0xfa22457c1111088881780007b,0xfa22457c2222111108888007b,0xfa2245c41111088880780007c,0xfa2247441111088880780007d,0xfa2247841111088880780007c,0xfa2247c41111088880780007a,0xfa2247c4111108888078000fc,0xfa2247c41111088880780017e,0xfa2247c41111088880780027c,0xfa2247c411110888807880079,0xfa2247c41111088880790007b,0xfa2247c411110888807c0007b,0xfa2247c411110888810780786,0xfa2247c41111088881780007b,0xfa2247c41111088884780007b,0xfa2247c411110888880780784,0xfa2247c411110888887800079,0xfa2247c41111088980780007a,0xfa2247c41111088c80780007a,0xfa2247c41111089880780007f,0xfa2247c4111108a880780007f,0xfa2247c4111108f880080007c,0xfa2247c41111098880780007a,0xfa2247c411110c8880780007a,0xfa2247c411118888807800078,0xfa2247c411150888807800078,0xfa2247c411178888807800012,0xfa2247c41119088880780007d]
def a5p70 : Keys := .leaf [
0xfa2247c41131088880780007d,0xfa2247c41911088880780007d,0xfa2247c420079111088880784,0xfa2247c43111088880780007d,0xfa2247c4447c222791110888b,0xfa2247c49111088880780007a,0xfa2247c51111088880780007a,0xfa2247cc1111088880780007a,0xfa2247d41111088880780007b,0xfa2247e41111088880780007a,0xfa2247fc1111088880780007a,0xfa2247fc11110888807f8007b,0xfa2247fc1179111108888007b,0xfa2247fc447c222791110888b,0xfa224c4411110f8880780007f,0xfa224ccc91110888810780784,0xfa224ccc9111088881780007c,0xfa224ccc9111098880780007a,0xfa224ccc91110f8f80780007a,0xfa224ccc9999810000780007e,0xfa224ccca22791110f8880786,0xfa224cccafaa911100780007a,0xfa224cfc91110f8880780007a,0xfa224dcc9111088880780007c,0xfa224dcc9111098880780007a,0xfa224fc41111088880780007b,0xfa224fcc9111088880780007b,0xfa224fcc9111088f80780007a,0xfa224fcc9999911100780007a,0xfa224ffc9111088880780007a,0xfa2251150888878000780007d,0xfa2255550888811000780007e]
def a5p71 : Keys := .leaf [
0xfa22555511110888810780786,0xfa2255551111088881780007e,0xfa2255551111088885780007e,0xfa2255551111098880780007a,0xfa22555511110d8880780007a,0xfa22555511178888878780784,0xfa22555519998f8880780007d,0xfa22557d1111088887f80007b,0xfa225ddd91110f8880780007a,0xfa2267c41111088880780007a,0xfa22780011110f88807c0007a,0xfa22780011110f8c80780007a,0xfa22780011150f8880780007a,0xfa22780411110f8880780007a,0xfa22791108888780007c00078,0xfa22791108888784007800078,0xfa227911088c8780007800078,0xfa2279110f888078000780042,0xfa22791144440888810780785,0xfa22791144440888817800078,0xfa2279114444098880780007d,0xfa227911447c088887f800078,0xfa227911447c0f8880780007f,0xfa22791147c40f8880780007a,0xfa2279114ccc8f8880780007a,0xfa2279114fcc8f8880780007a,0xfa22791155550f8880780007a,0xfa22791508888780007800078,0xfa22c7c41111088880780007c,0xfa2347c41111088880780007c,0xfa26111108888780007c00079,0xfa26111108888784007800078]
def a5p72 : Keys := .leaf [
0xfa261111088c8780007800078,0xfa26111508888780007800078,0xfa2647c41111088880780007d,0xfa26780411110f8880780007a,0xfa26791508888780007800078,0xfa27911108888780007800052,0xfa27911108888780007c00079,0xfa27911108888784007800078,0xfa27911108888787807800040,0xfa27911108888787840400784,0xfa279111088c8780007800078,0xfa27911508888780007800078,0xfa27a227911108888780007c4,0xfa27a2279111088c878000786,0xfa27a22791150888878000784,0xfa27a7a791110888807800040,0xfa27a7a791110888840400784,0xfa27c00411110888878780786,0xfa27c00427a79111088880786,0xfa27c07c22279111088887806,0xfa27c44411110888810780786,0xfa27c4441111088881780007e,0xfa27c44411110888878780784,0xfa27c4441111088887f8007fc,0xfa27c4441111088887ff80784,0xfa27c4441111098880780007f,0xfa27c44411110f88888f80786,0xfa27c44411110f8f888880784,0xfa27c44422279111088881786,0xfa27c44422279111098880786,0xfa27c44423279111088880786,0xfa27c44427a79111088880784]
def a5p73 : Keys := .leaf [
0xfa27c44427ff9111088880786,0xfa27c4442faf9111088880786,0xfa27c47c111108888780007fc,0xfa27c47c11110888878780784,0xfa27c47c1111088887f80007b,0xfa27c47c22221111088887879,0xfa27c47c22279111088881003,0xfa27c47c22279111088887801,0xfa27c47c22279111088887879,0xfa27c47c22279111088887f84,0xfa27c47c222791110f8888889,0xfa27c47c227f9111088887804,0xfa27c47c27a21111088880079,0xfa27c47c27a22227911108889,0xfa27c47c27a79111088880079,0xfa27c47c27a79111088880784,0xfa27c47c27a79111088887804,0xfa27c47c27a7a222111108889,0xfa27c47c27a7a227911108889,0xfa27c47c2aaf9111088887804,0xfa27c47c444427a791110888c,0xfa27c5441111088880780007e,0xfa27c54422279111088880786,0xfa27c7841111088880780007c,0xfa27c7c41111088880780007d,0xfa27c7c411110888807f80784,0xfa27c7c41111088f888880784,0xfa27c7c4447c222791110888c,0xfa27c7fc1111088880780007a,0xfa27c7fc447c222791110888b,0xfa27cccc91110888878780784,0xfa27cccc9111088f878000785]
def a5p74 : Keys := .leaf [
0xfa27cccc91110f8880780007a,0xfa27cccca22791110f8880786,0xfa27cccca7a79111088880784,0xfa27ccccaaaf9111078000785,0xfa27cfcc9111088880780007a,0xfa27d1150888878000780007d,0xfa27d11522278888878000784,0xfa27d55511110888878780786,0xfa27d55527a79111088880786,0xfa27f800447c27a791110888e,0xfa27f91144440888878780784,0xfa27f91144440f8880780007f,0xfa2a4444111108f8878000078,0xfa2a47c41111088880780007c,0xfa3247c41111088880780007d,0xfa7a447c22279111088887801,0xfa7a447c27a21111088880079,0xfa7fc44427a79111088880784,0xfa7fc47c22279111088887801,0xfaaaf91144440f8880780007f,0xfb22444411110888810780786,0xfb2244441111088881780007e,0xfb2244441111098880780007f,0xfb22444423279111088880786,0xfb22447c2322111108888007b,0xfb2245441111088880780007e,0xfb2247c41111088880780007c,0xfb27c44411110888810780786,0xfb27c44423279111088880786,0xfb33111108888780007c00079,0xfb33111108888784007800078,0xfb331111088c8780007800078]
def a5p75 : Keys := .leaf [
0xfb33111508888780007800078,0xfb3344440888810100780007b,0xfb33444411110888810780786,0xfb3344441111088881780007e,0xfb33444411110888830780784,0xfb3344441111098880780007f,0xfb3344441179088887f80007c,0xfb33444419998f8880780007d,0xfb33447c1111088887f80007b,0xfb33447c11790888878000078,0xfb33447c22279111088887801,0xfb33447c27a21111088880079,0xfb3345441111088880780007e,0xfb3347441111088880780007d,0xfb3347c41111088880780007c,0xfb3347c41179088880780007d,0xfb3347c41999888880780007d,0xfb3347fc1111088880780007b,0xfb334ccc91110f8880780007a,0xfb334ccc9999878000780007d,0xfb334fcc9111088880780007b,0xfb3355550888810000780007e,0xfb33555508888300007800078,0xfb3355550888850000780007d,0xfb3355550888878000780007d,0xfb33555508888787807800078,0xfb335555088887f800780007d,0xfb3355550f88888880780007d,0xfb33555522278888878000785,0xfb33555527a20888807800078,0xfb33557d0888878000780007d,0xfb335ddd8888878000780007d]
def a5p76 : Keys := .leaf [
0xfb33780055550f8880780007f,0xfb33791108888780007c00078,0xfb33791108888784007800078,0xfb337911088c8780007800078,0xfb3379110f888078000780042,0xfb33791144440888810780785,0xfb33791144440888817800078,0xfb33791144440888830780785,0xfb3379114444098880780007d,0xfb33791144440b88807800078,0xfb33791144440f8880780007f,0xfb337911447c088887f800078,0xfb337911447c0f8880780007f,0xfb33791147c40f8880780007d,0xfb3379114ccc8f8880780007d,0xfb3379114fcc8f8880780007a,0xfb33791155550f8880780007f,0xfb33791508888780007800078,0xfb3379794444088887f80007c,0xfb33797944440f8880780007d,0xfb337999c4440f8880780007d,0xfb37111508888780007800078,0xfb37791508888780007800078,0xfb37c44411110888878780784,0xfb37c44427a79111088880784,0xfb37c47c22279111088887801,0xfb37c7c41111088880780007c,0xfb37d5550888878000780007d,0xfb37d55522278888878000785,0xfb37f91144440888878780784,0xfb37f91144440f8880780007f,0xfbbbf91144440f8880780007f]
def a5p77 : Keys := .leaf [
0xfc00447c22279111088887804,0xfc04222791110888878780786,0xfc0427a21111088880780007e,0xfc0427a79111088880780007e,0xfc4411110888810000780027e,0xfc44111108888107807800205,0xfc4411110888812000780007b,0xfc4411110888817800200007d,0xfc44111108888330007800078,0xfc4411110888878000380007d,0xfc4411110888878000780027c,0xfc441111088887800078002fc,0xfc4411110888878000780037e,0xfc44111108888780022780784,0xfc4411110888878780780027e,0xfc44111108888787807f80205,0xfc441111088887a000780007d,0xfc441111088887a000780027e,0xfc441111088887a0007f80079,0xfc441111088887a2007800078,0xfc441111088887a7807800078,0xfc441111088887a780780027e,0xfc441111088887a800780007d,0xfc441111088887b000780007d,0xfc441111088887f800280007d,0xfc441111088887f800780027e,0xfc441111088887f8022780786,0xfc44111108a8810000780007b,0xfc44111108a8878000780007d,0xfc44111108a8878000780027d,0xfc44111108a88780007f80078,0xfc44111108a88787807800078]
def a5p78 : Keys := .leaf [
0xfc44111108a887a000780007d,0xfc44111108a887f800780007d,0xfc44111108b8878000780007d,0xfc4411110988807800200007f,0xfc4411110aa88780007800078,0xfc4411110aa887f800780007d,0xfc4411110f88888880780027c,0xfc4411110f8888a880780007f,0xfc4411110fa8888880780007d,0xfc4411110fa888a880780007f,0xfc4411310888810000780007b,0xfc4411310888878000780007d,0xfc4411310888878000780027d,0xfc44113108888780007f80078,0xfc44113108888787807800078,0xfc441131088887a000780007d,0xfc441131088887f800780007d,0xfc44113108a8878000780007d,0xfc4411310f88888880780007d,0xfc4411390888878000780007d,0xfc4411790888878000300007f,0xfc4422220888811100780007b,0xfc44222211110888810780783,0xfc44222211110888811780783,0xfc4422221111088881780007b,0xfc4422221111088881780107b,0xfc4422221111088881790007b,0xfc44222211110888830780781,0xfc44222211110888857800079,0xfc4422221111088f87800078b,0xfc4422221111098880780007a,0xfc44222211110988810780783]
def a5p79 : Keys := .leaf [
0xfc4422221111098881780007b,0xfc4422221111098980780007a,0xfc4422221111099880780007f,0xfc44222211110b8880780007a,0xfc44222211110f88880780787,0xfc44222211110f8888780007a,0xfc4422221111888f878000785,0xfc4422221179088881100007e,0xfc44222211790888878000179,0xfc44222211790888879000079,0xfc44222211790898878000078,0xfc44222217910888810780785,0xfc44222217910888817800078,0xfc44222219110f8880780007a,0xfc44222219998888810780781,0xfc44222219998888817800079,0xfc44222791110888810780786,0xfc4422279111088881780007b,0xfc442227911108888780007c4,0xfc44222791110888878400784,0xfc4422279111088887f8007f9,0xfc4422279111088887ff80786,0xfc4422279111088c878000786,0xfc4422279111098880780007a,0xfc44222791110f88888f80786,0xfc44222791110f8f888880786,0xfc44222791150888878000784,0xfc44223211790888878000078,0xfc44227a111108a887800007b,0xfc44227a11310888878000079,0xfc4423221111088880780007b,0xfc44232211110888810780783]
def a5p80 : Keys := .leaf [
0xfc4423221111088881780007b,0xfc4423221111098880780007f,0xfc44232219998888807800078,0xfc4423231111088880780007b,0xfc4423279111088880780007b,0xfc44232791110888810780786,0xfc4423321111088880780007b,0xfc4423a211110888807800079,0xfc44272211110888807800078,0xfc4427a011110888807800079,0xfc4427a211110888807800078,0xfc4427a2111108888078000fc,0xfc4427a21111088880780017e,0xfc4427a21111088880780027e,0xfc4427a211110888807880079,0xfc4427a21111088880790007b,0xfc4427a211110888807c00079,0xfc4427a211110888810780786,0xfc4427a21111088881780007b,0xfc4427a211110888820780786,0xfc4427a211110888880780784,0xfc4427a211110888887800079,0xfc4427a21111088980780007a,0xfc4427a21111088c80780007a,0xfc4427a21111088f807800008,0xfc4427a21111089880780007f,0xfc4427a2111108a880780007f,0xfc4427a21111098880780007f,0xfc4427a211110a8880780007f,0xfc4427a211118888807800078,0xfc4427a211150888807800078,0xfc4427a21119088880780007d]
def a5p81 : Keys := .leaf [
0xfc4427a21131088880780007d,0xfc4427a21179088880100007e,0xfc4427a219110888807800078,0xfc4427a29111088880780007e,0xfc4427a31111088880780007e,0xfc4427a61111088880780007f,0xfc4427a79111088880780007f,0xfc4427a791110888807f80786,0xfc4427a791179111088880786,0xfc4427aa1111088880780007f,0xfc4427b21111088880780007e,0xfc442a2211110f8880780007a,0xfc442aaa91110888810780781,0xfc442aaa91110888817800079,0xfc442aaa9111098880780007f,0xfc442aaa91110ff880780007f,0xfc442aaa9999810000780007b,0xfc442aaf91110f8880780007f,0xfc442baa91110888807800079,0xfc442baa9111098880780007f,0xfc442fa21111088880780007e,0xfc442faa9111088880780007e,0xfc442faa911108f880780007f,0xfc442faa9999911100780007f,0xfc442faf9111088880780007e,0xfc44313108888780007800078,0xfc4433330888810100780007b,0xfc44333311110888810780783,0xfc4433331111088881780007b,0xfc44333311110888830780783,0xfc4433331111098880780007f,0xfc44333311110b8880780007f]
def a5p82 : Keys := .leaf [
0xfc4433331179088887f800078,0xfc44333319998f88807800078,0xfc44333791110888878780786,0xfc443bbb91110f8880780007f,0xfc44407827a21111088880079,0xfc44444422279111088881786,0xfc44444422279111098880786,0xfc44444423279111088880786,0xfc44447c11110888878000279,0xfc44447c111108a887800007b,0xfc44447c11310888878000079,0xfc44447c2222111108888107b,0xfc44447c2222111109888007b,0xfc44447c22279111088881006,0xfc44447c2227911108888787e,0xfc44447c22279111088887f86,0xfc44447c222791110f888888c,0xfc44447c2322111108888007b,0xfc44447c27a22227911108889,0xfc44447c27a7a22791110888e,0xfc44447c2aaa91110f888007b,0xfc44454422279111088880786,0xfc44457c2222111108888007b,0xfc4447c41111088880780027c,0xfc4447c4111108a880780007f,0xfc4447c41131088880780007d,0xfc4447c4447c222791110888c,0xfc4447c7a2279111088880786,0xfc4447fc22279111088880786,0xfc4447fc447c222791110888e,0xfc444fcca2279111088880786,0xfc444fccaaaa911100780007f]
def a5p83 : Keys := .leaf [
0xfc44511127a20888807800078,0xfc4467a21111088880780007e,0xfc44780011110f8880780027f,0xfc44780011110fa880780007f,0xfc44780011310f8880780007f,0xfc44782011110f8880780007f,0xfc4479110888878000780027d,0xfc447911088887a000780007d,0xfc44791108a8878000780007d,0xfc4479110f88807800200007f,0xfc44791122220888810780785,0xfc44791122220888817800078,0xfc44791122220988807800078,0xfc44791122278888878780785,0xfc44791122278f8880780007a,0xfc44791127a20f88807800078,0xfc4479112aaa8f8880780007f,0xfc4479112faa8f8880780007f,0xfc44791133330f8880780007f,0xfc4479310888878000780007d,0xfc447a2211110888810780786,0xfc447a221111088881780007b,0xfc447a221111098880780007a,0xfc447a2279110f8880780007a,0xfc447a2791110888878780786,0xfc447a2791110f8880780007f,0xfc447aaa91110f8880780007f,0xfc447b3311110f8880780007f,0xfc447b3379110f8880780007f,0xfc44a2221111088f878000783,0xfc44a7a211110888807800078,0xfc4527a211110888807800078]
def a5p84 : Keys := .leaf [
0xfc47c47c22279111088887804,0xfc47c7c422279111088880784,0xfc4c27a211110888807800079,0xfc5427a211110888807800078,0xfc6411110888878000780027c,0xfc641111088887a000780007d,0xfc64111108a8878000780007d,0xfc6411310888878000780007d,0xfc6427a211110888807800078,0xfc64782011110f8880780007f,0xfc6479310888878000780007d,0xfc7c11110888878000300007f,0xfc7c11110888878000780027c,0xfc7c1111088887a000780007d,0xfc7c1111088887f800200007d,0xfc7c1111088887f8022000079,0xfc7c111108a8878000780007d,0xfc7c11310888878000780007d,0xfc7c20201111088887f80007b,0xfc7c222211110888810780783,0xfc7c22221111088881780007b,0xfc7c2222111108888787807f9,0xfc7c22221111088887f800079,0xfc7c22221111088887ff80079,0xfc7c22221111098880780007a,0xfc7c222211110f8888f88007b,0xfc7c222211110ff8888880079,0xfc7c2227911108888780007f9,0xfc7c222791110888878780786,0xfc7c22279111088887f800079,0xfc7c23221111088880780007b,0xfc7c27a011110888807800079]
def a5p85 : Keys := .leaf [
0xfc7c27a211110888807800078,0xfc7c27a211110888807f80079,0xfc7c27a2111108f8888880079,0xfc7c27a791110888807800078,0xfc7c2aaa9111088887f800079,0xfc7c2aaa911108f8878000078,0xfc7c2aaa91110f8880780007f,0xfc7c2faa91110888807800079,0xfc7c313108888780007800078,0xfc7c33331111088887f80007b,0xfc7c444422279111088887f84,0xfc7c447c11110888878000279,0xfc7c447c111108a887800007b,0xfc7c447c11310888878000079,0xfc7c447c20279111088887803,0xfc7c447c2222111108888107b,0xfc7c447c2222111109888007b,0xfc7c447c22279111088881006,0xfc7c447c22279111088887804,0xfc7c447c22279111088887879,0xfc7c447c22279111088887f84,0xfc7c447c222791110f888888c,0xfc7c447c2322111108888007b,0xfc7c447c27a22227911108889,0xfc7c447c27a7a227911108889,0xfc7c447c2aaa91110f888007b,0xfc7c447c31310888878000079,0xfc7c447fa2279111088887801,0xfc7c457c2222111108888007b,0xfc7c47c422279111088880784,0xfc7c47c4447c222791110888c,0xfc7c47fc1111088880200007d]
def a5p86 : Keys := .leaf [
0xfc7c47fc11110888822000079,0xfc7c47fc2020111108888007b,0xfc7c47fc22221111088880079,0xfc7c47fc22279111088880079,0xfc7c47fc22279111088880784,0xfc7c47fc22279111088887801,0xfc7c47fc2227a222111108889,0xfc7c47fc2aaa9111088880079,0xfc7c47fc3333111108888007b,0xfc7c47fc4444222791110888c,0xfc7c47fc447c222791110888c,0xfc7c47ffa222111108888007b,0xfc7c4cfca2279111088887801,0xfc7c4cfcaaaa9111078000078,0xfc7c4ffca222111108888007b,0xfc7c780047fc222791110888b,0xfc7c79112222088887f800079,0xfc7c791122220f8880780007a,0xfc7c7a221111088887f80007b,0xfc7c7a2211110f8880780007a,0xfc7fc47c22279111088887804,0xfc7fc7fc22221111088880079,0xfcccf91122220f8880780007a,0xfcccfa2211110f8880780007a,0xfd44222211110888810780783,0xfd4422221111088881780007b,0xfd4422221111098880780007a,0xfd4423221111088880780007b,0xfd4427a211110888807800079,0xfd44454422279111088880786,0xfd44457c2222111108888007b,0xfd5511110888878000780027c]
def a5p87 : Keys := .leaf [
0xfd551111088887a000780007d,0xfd55111108a8878000780007d,0xfd5511310888878000780007d,0xfd5522220888811000780007e,0xfd55222211110888810780783,0xfd5522221111088881780007b,0xfd55222211110888857800079,0xfd5522221111098880780007a,0xfd55222211178888878780781,0xfd55222219998f88807800078,0xfd55222791110888878780786,0xfd55222791178888878000785,0xfd5523221111088880780007b,0xfd55272211110888807800078,0xfd5527a211110888807800079,0xfd5527a211178888807800078,0xfd5527a219998888807800078,0xfd5527a791110888807800078,0xfd552aaa91110f8880780007f,0xfd552aaa99998780007800078,0xfd552faa91110888807800079,0xfd5533330888810000780007b,0xfd55333308888300007800078,0xfd5533330888850000780007d,0xfd55333308888780007800078,0xfd55333308888787807800078,0xfd553333088887f800780007d,0xfd5533330f888888807800078,0xfd55333788888780007800078,0xfd553bbb88888780007800078,0xfd55447c22279111088887804,0xfd55447c33330888878000078]
def a5p88 : Keys := .leaf [
0xfd5547c422279111088880784,0xfd5547c43333088880780007d,0xfd55780033330f8880780007a,0xfd5579110888878000780027d,0xfd557911088887a000780007d,0xfd55791108a8878000780007d,0xfd5579110f88807800200007f,0xfd55791122220888810780785,0xfd55791122220888817800078,0xfd55791122220888857800078,0xfd55791122220988807800078,0xfd55791122220d8880780007d,0xfd55791122220f8880780007a,0xfd55791122278888878780785,0xfd55791122278f8880780007a,0xfd55791127a20f88807800078,0xfd5579112aaa8f88807800078,0xfd5579112faa8f88807800078,0xfd55791133330f8880780007a,0xfd557917a2220888878780781,0xfd557917a2220f88807800078,0xfd5579310888878000780007d,0xfd557999a2220f88807800078,0xfd557a2211110f8880780007a,0xfd557a2279110f8880780007a,0xfd557b330888810000780007b,0xfd557b3308888300007800078,0xfd557b330888850000780007d,0xfd557b3308888780007800078,0xfd557b3308888787807800078,0xfd557b33088887f800780007d,0xfd557b330f888780007800078]
def a5p89 : Keys := .leaf [
0xfd557b330f888888807800078,0xfd557b3311110f8880780007a,0xfd557b3322220f88807800078,0xfd557b3344440f8880780007d,0xfd557b3378000f8880780007a,0xfd557b3379110f8880780007a,0xfd557b378888878000780007d,0xfd557bbb8888878000780007d,0xfd7511310888878000780007d,0xfd7579310888878000780007d,0xfd7c22221111088881780007b,0xfd7c457c2222111108888007b,0xfd7d22221111088887f800079,0xfd7d27a211110888807800078,0xfd7d333308888780007800078,0xfd7d447c22279111088887804,0xfd7d447c33330888878000078,0xfd7d47fc22221111088880079,0xfd7d79112222088887f800079,0xfd7d791122220f8880780007a,0xfd7d7b3308888780007800078,0xfdddf91122220f8880780007a,0xfdddfb3308888780007800078,0xfe2247c41111088880780007c,0xfe4427a211110888807800078,0xfe66447c22279111088887801,0xfe67c47c22279111088887801,0xfe7e447c22279111088887804,0xfe7fc47c22279111088887801,0xff99c44422220900007800078,0xffa2791144440f8880780007d,0xffaaf91144440f8880780007d]
def a5p90 : Keys := .leaf [
0xffb3791144440f8880780007f,0xffbbf91144440f8880780007d,0xffc4791122220f88807800078,0xffccf91122220f88807800078,0xffd5791122220f8880780007a,0xffddf91122220f88807800078]
def a5 : Keys := .branch 0x1f0f088884f4f2222111100ff (.branch 0x1f0004f442222191900f0000f (.branch 0x18f88444f2222111110f0000f (.branch 0x18888500f444422221f1100f0 (.branch 0x1888822621111100f0f0000f0 (.branch 0x14444322211190f0000f0000f (a5p0) (a5p1)) (.branch 0x18888444432321f1100f0000f (a5p2) (.branch 0x18888444f323211110f0000f0 (a5p3) (a5p4)))) (.branch 0x188f8444f2222111110000f00 (.branch 0x18888555532230f0000f0000f (a5p5) (.branch 0x188f82222115110000f00000f (a5p6) (a5p7))) (.branch 0x188f8544422221f001111000f (a5p8) (.branch 0x18a88444422221111100f00f0 (a5p9) (a5p10))))) (.branch 0x19a8844442222111100f0000f (.branch 0x19888444422221f11100f00f0 (.branch 0x18f888888544f2222111100f0 (a5p11) (a5p12)) (.branch 0x198894f442222111100f0000f (a5p13) (.branch 0x198f94444222211110f00000f (a5p14) (a5p15)))) (.branch 0x1f00022621f1100f0000f0008 (.branch 0x1aaaa444f333310000f0000f0 (a5p16) (.branch 0x1d8884f442222111100f0000f (a5p17) (a5p18))) (.branch 0x1f0004444222b1f1100f0000f (a5p19) (.branch 0x1f000444f222219190f0f00f0 (a5p20) (a5p21)))))) (.branch 0x1f0008f88444f2222111900f0 (.branch 0x1f00088f822221f1100f0004f (.branch 0x1f000888822221f7100f0000f (.branch 0x1f0005f5522221f1100f8000f (a5p22) (a5p23)) (.branch 0x1f0008888444f2222131102f0 (a5p24) (.branch 0x1f00088894f442222111f00f0 (a5p25) (a5p26)))) (.branch 0x1f00088f84f00444f22221111 (.branch 0x1f00088f8444433331111020f (a5p27) (.branch 0x1f00088f8444f22221f11111f (a5p28) (a5p29))) (.branch 0x1f00088f88888464f22221111 (a5p30) (.branch 0x1f0008af8555522221111000f (a5p31) (a5p32))))) (.branch 0x1f00f4f442222111100f0000a (.branch 0x1f000aaaa4f4f222f111100f0 (.branch 0x1f000999922221f5100f0000f (a5p33) (.branch 0x1f0009f99555f222200f0000f (a5p34) (a5p35))) (.branch 0x1f00188f8444f222211110f00 (a5p36) (.branch 0x1f0084f4c2222111100f0000f (a5p37) (a5p38)))) (.branch 0x1f040222211110f0000ff0008 (.branch 0x1f00f88f8222211510f00000f (a5p39) (.branch 0x1f00f8f88555f2222111100f0 (a5p40) (a5p41))) (.branch 0x1f040999922221f1100f0000f (a5p42) (.branch 0x1f0f04444222a11110ff0000f (a5p43) (a5p44))))))) (.branch 0x1f4448888464f2222111100f0 (.branch 0x1f222888944441f1100f0000f (.branch 0x1f22244441f19111100f0000f (.branch 0x1f0f09ff9444422221f11000f (.branch 0x1f0f08af8444422221111000f (a5p45) (a5p46)) (.branch 0x1f20088f8464422221111000f (a5p47) (.branch 0x1f222444411110f8800f0000f (a5p48) (a5p49)))) (.branch 0x1f222888844441111020f00f0 (.branch 0x1f222555d11190f0000f0000f (a5p50) (.branch 0x1f222888811510f0000f0004f (a5p51) (a5p52))) (.branch 0x1f222888844441f1900f0000f (a5p53) (.branch 0x1f2228888464f2222111100f0 (a5p54) (a5p55))))) (.branch 0x1f222aaaa66661f1100f0000f (.branch 0x1f2228f884644111100f0000f (.branch 0x1f22288f844441ff11111000f (a5p56) (.branch 0x1f22288f8666611110600000f (a5p57) (a5p58))) (.branch 0x1f2229999444f22221f1100f0 (a5p59) (.branch 0x1f2229f995f551f1100f0000f (a5p60) (a5p61)))) (.branch 0x1f2f2888866661f1100f0000f (.branch 0x1f22a44441f1100f0000f0008 (a5p62) (.branch 0x1f26288881111020000f0000f (a5p63) (a5p64))) (.branch 0x1f444222211110ff000ff0008 (a5p65) (.branch 0x1f4444f442222111100f8000f (a5p66) (a5p67)))))) (.branch 0x1f88844442222131102f0000f (.branch 0x1f44f88884fff2222111100f0 (.branch 0x1f4448f882262111100f0000f (.branch 0x1f4448a88444f2222111100f0 (a5p68) (a5p69)) (.branch 0x1f444aaaa22221111020f00f0 (a5p70) (.branch 0x1f44c222211190f0000f0000f (a5p71) (a5p72)))) (.branch 0x1f666f000aaaa1f1100f0000f (.branch 0x1f44f999922221f1100f0000f (a5p73) (.branch 0x1f666222a11110f0000f0000f (a5p74) (a5p75))) (.branch 0x1f80088f8444f222211110f00 (a5p76) (.branch 0x1f888222211510f4000f0000f (a5p77) (a5p78))))) (.branch 0x1f8f84f442222111100f0000f (.branch 0x1f888666622f211110ff0000f (.branch 0x1f88846442222111102f0000f (a5p79) (.branch 0x1f8884f442262111100f0000f (a5p80) (a5p81))) (.branch 0x1f888a2224f44111100f0000f (a5p82) (.branch 0x1f88f88f8444f222211110f00 (a5p83) (a5p84)))) (.branch 0x1faaa8f88444f2222111100f0 (.branch 0x1f8f88ff8222211110440000f (a5p85) (.branch 0x1faaa222211110f4000f0000f (a5p86) (a5p87))) (.branch 0x1faaaf6661f11111100f0000f (a5p88) (.branch 0x1ff66f22288881f1100f0000f (a5p89) (a5p90)))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p0 : r5p0.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p1 : r5p1.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p2 : r5p2.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p3 : r5p3.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p4 : r5p4.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p5 : r5p5.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p6 : r5p6.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p7 : r5p7.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p8 : r5p8.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p9 : r5p9.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p10 : r5p10.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p11 : r5p11.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p12 : r5p12.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p13 : r5p13.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p14 : r5p14.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p15 : r5p15.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p16 : r5p16.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p17 : r5p17.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p18 : r5p18.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p19 : r5p19.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p20 : r5p20.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p21 : r5p21.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p22 : r5p22.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p23 : r5p23.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p24 : r5p24.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p25 : r5p25.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p26 : r5p26.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p27 : r5p27.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p28 : r5p28.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p29 : r5p29.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p30 : r5p30.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p31 : r5p31.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p32 : r5p32.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p33 : r5p33.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p34 : r5p34.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p35 : r5p35.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p36 : r5p36.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p37 : r5p37.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p38 : r5p38.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p39 : r5p39.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p40 : r5p40.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p41 : r5p41.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p42 : r5p42.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p43 : r5p43.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p44 : r5p44.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p45 : r5p45.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p46 : r5p46.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p47 : r5p47.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p48 : r5p48.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p49 : r5p49.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p50 : r5p50.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p51 : r5p51.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p52 : r5p52.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p53 : r5p53.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p54 : r5p54.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p55 : r5p55.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p56 : r5p56.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p57 : r5p57.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p58 : r5p58.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p59 : r5p59.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p60 : r5p60.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p61 : r5p61.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p62 : r5p62.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p63 : r5p63.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p64 : r5p64.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p65 : r5p65.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p66 : r5p66.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p67 : r5p67.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p68 : r5p68.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p69 : r5p69.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p70 : r5p70.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p71 : r5p71.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p72 : r5p72.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p73 : r5p73.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p74 : r5p74.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p75 : r5p75.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p76 : r5p76.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p77 : r5p77.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p78 : r5p78.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p79 : r5p79.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p80 : r5p80.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p81 : r5p81.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p82 : r5p82.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p83 : r5p83.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p84 : r5p84.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p85 : r5p85.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p86 : r5p86.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p87 : r5p87.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p88 : r5p88.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p89 : r5p89.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p90 : r5p90.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p91 : r5p91.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p92 : r5p92.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p93 : r5p93.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p94 : r5p94.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p95 : r5p95.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p96 : r5p96.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p97 : r5p97.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p98 : r5p98.all (checkFast 4 a4) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr5p99 : r5p99.all (checkFast 4 a4) = true := by
  decide +kernel

lemma badR5 : Rejects 5 r5 :=
  verifyFast 4 a4 r5 badA4 (by
    unfold r5
    simp only [allBranch, Bool.and_true, goodr5p0, goodr5p1, goodr5p2, goodr5p3, goodr5p4, goodr5p5, goodr5p6, goodr5p7, goodr5p8, goodr5p9, goodr5p10, goodr5p11, goodr5p12, goodr5p13, goodr5p14, goodr5p15, goodr5p16, goodr5p17, goodr5p18, goodr5p19, goodr5p20, goodr5p21, goodr5p22, goodr5p23, goodr5p24, goodr5p25, goodr5p26, goodr5p27, goodr5p28, goodr5p29, goodr5p30, goodr5p31, goodr5p32, goodr5p33, goodr5p34, goodr5p35, goodr5p36, goodr5p37, goodr5p38, goodr5p39, goodr5p40, goodr5p41, goodr5p42, goodr5p43, goodr5p44, goodr5p45, goodr5p46, goodr5p47, goodr5p48, goodr5p49, goodr5p50, goodr5p51, goodr5p52, goodr5p53, goodr5p54, goodr5p55, goodr5p56, goodr5p57, goodr5p58, goodr5p59, goodr5p60, goodr5p61, goodr5p62, goodr5p63, goodr5p64, goodr5p65, goodr5p66, goodr5p67, goodr5p68, goodr5p69, goodr5p70, goodr5p71, goodr5p72, goodr5p73, goodr5p74, goodr5p75, goodr5p76, goodr5p77, goodr5p78, goodr5p79, goodr5p80, goodr5p81, goodr5p82, goodr5p83, goodr5p84, goodr5p85, goodr5p86, goodr5p87, goodr5p88, goodr5p89, goodr5p90, goodr5p91, goodr5p92, goodr5p93, goodr5p94, goodr5p95, goodr5p96, goodr5p97, goodr5p98, goodr5p99])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p0 : a5p0.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p1 : a5p1.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p2 : a5p2.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p3 : a5p3.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p4 : a5p4.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p5 : a5p5.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p6 : a5p6.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p7 : a5p7.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p8 : a5p8.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p9 : a5p9.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p10 : a5p10.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p11 : a5p11.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p12 : a5p12.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p13 : a5p13.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p14 : a5p14.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p15 : a5p15.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p16 : a5p16.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p17 : a5p17.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p18 : a5p18.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p19 : a5p19.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p20 : a5p20.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p21 : a5p21.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p22 : a5p22.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p23 : a5p23.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p24 : a5p24.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p25 : a5p25.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p26 : a5p26.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p27 : a5p27.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p28 : a5p28.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p29 : a5p29.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p30 : a5p30.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p31 : a5p31.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p32 : a5p32.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p33 : a5p33.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p34 : a5p34.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p35 : a5p35.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p36 : a5p36.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p37 : a5p37.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p38 : a5p38.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p39 : a5p39.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p40 : a5p40.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p41 : a5p41.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p42 : a5p42.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p43 : a5p43.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p44 : a5p44.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p45 : a5p45.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p46 : a5p46.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p47 : a5p47.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p48 : a5p48.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p49 : a5p49.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p50 : a5p50.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p51 : a5p51.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p52 : a5p52.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p53 : a5p53.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p54 : a5p54.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p55 : a5p55.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p56 : a5p56.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p57 : a5p57.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p58 : a5p58.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p59 : a5p59.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p60 : a5p60.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p61 : a5p61.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p62 : a5p62.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p63 : a5p63.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p64 : a5p64.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p65 : a5p65.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p66 : a5p66.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p67 : a5p67.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p68 : a5p68.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p69 : a5p69.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p70 : a5p70.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p71 : a5p71.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p72 : a5p72.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p73 : a5p73.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p74 : a5p74.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p75 : a5p75.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p76 : a5p76.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p77 : a5p77.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p78 : a5p78.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p79 : a5p79.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p80 : a5p80.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p81 : a5p81.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p82 : a5p82.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p83 : a5p83.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p84 : a5p84.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p85 : a5p85.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p86 : a5p86.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p87 : a5p87.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p88 : a5p88.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p89 : a5p89.all (checkAlias r5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda5p90 : a5p90.all (checkAlias r5) = true := by
  decide +kernel

lemma badA5 : RejectsAlias 5 a5 :=
  verifyAliases 5 r5 a5 badR5 (by
    unfold a5
    simp only [allBranch, Bool.and_true, gooda5p0, gooda5p1, gooda5p2, gooda5p3, gooda5p4, gooda5p5, gooda5p6, gooda5p7, gooda5p8, gooda5p9, gooda5p10, gooda5p11, gooda5p12, gooda5p13, gooda5p14, gooda5p15, gooda5p16, gooda5p17, gooda5p18, gooda5p19, gooda5p20, gooda5p21, gooda5p22, gooda5p23, gooda5p24, gooda5p25, gooda5p26, gooda5p27, gooda5p28, gooda5p29, gooda5p30, gooda5p31, gooda5p32, gooda5p33, gooda5p34, gooda5p35, gooda5p36, gooda5p37, gooda5p38, gooda5p39, gooda5p40, gooda5p41, gooda5p42, gooda5p43, gooda5p44, gooda5p45, gooda5p46, gooda5p47, gooda5p48, gooda5p49, gooda5p50, gooda5p51, gooda5p52, gooda5p53, gooda5p54, gooda5p55, gooda5p56, gooda5p57, gooda5p58, gooda5p59, gooda5p60, gooda5p61, gooda5p62, gooda5p63, gooda5p64, gooda5p65, gooda5p66, gooda5p67, gooda5p68, gooda5p69, gooda5p70, gooda5p71, gooda5p72, gooda5p73, gooda5p74, gooda5p75, gooda5p76, gooda5p77, gooda5p78, gooda5p79, gooda5p80, gooda5p81, gooda5p82, gooda5p83, gooda5p84, gooda5p85, gooda5p86, gooda5p87, gooda5p88, gooda5p89, gooda5p90])
def r6p0 : Keys := .leaf [
0x18f8844443222111100f0000f,0x1f222444411110f0000f8000f,0x1f222444411110f0800f0000f,0x1f222444411190f0000f0000f]
def r6p1 : Keys := .leaf [
0x1f22244441f1100f0000f0008,0x1f22288884444111102f0000f,0x1f22288884444131100f0000f,0x1f22288f844441f1100f0000f]
def r6p2 : Keys := .leaf [
0x1f22288f8666611110f00000f,0x1f2228f8844441f1100f0000f,0x1f2228f884f44111100f0000f,0x1f222999944441f1100f0000f]
def r6p3 : Keys := .leaf [
0x1f222999955550f0000f0000f,0x1f2229f9944441f1100f0000f,0x1f222aaaa4f44111100f0000f,0x1f22a444411110f0000f0000f]
def r6p4 : Keys := .leaf [
0x1f444222211110f0800f0000f,0x1f444222211190f0000f0000f,0x1f444222a11110f0000f0000f,0x1f8f84f442222111100f0000f]
def r6p5 : Keys := .leaf [
0x1faaa666611110f0000f0000f,0x1faaaf66611110f0000f0000f,0x14444322211110f0000f0000f0008,0x15444222211110f0000f0000f0008]
def r6p6 : Keys := .leaf [
0x188884444322211110f0000f0000f,0x188884444322211110f0f00f0000f,0x18888444432221f00111100f0000f,0x18888444432221f110f0000f0000f]
def r6p7 : Keys := .leaf [
0x18888444432221f11111100f0000f,0x188884444322311110f0000f0000f,0x188884f4444443222111100f0000f,0x188887222444411110f0000f0000f]
def r6p8 : Keys := .leaf [
0x188f84444322211110f0000f0000f,0x18f884444322211110f0000f0000f,0x198884444222211110f0000f0000f,0x198884444322211110f0000f0000f]
def r6p9 : Keys := .leaf [
0x198884444333322220f0000f0000f,0x19888444f222211110f0000f0000f,0x198884f44222211110f0000f0000f,0x198885444222211110f0000f0000f]
def r6p10 : Keys := .leaf [
0x198894444222211110f0000f0000f,0x198984444222211110f0000f0000f,0x198f84444222211110f0000f0000f,0x199994444322211110f0000f0000f]
def r6p11 : Keys := .leaf [
0x199995444222211110f0000f0000f,0x1aaaa4444322211110f0000f0000f,0x1aaaa5444222211110f0000f0000f,0x1b2229999444411110f0000f0000f]
def r6p12 : Keys := .leaf [
0x1b8884444222211110f0000f0000f,0x1baaa4444222211110f0000f0000f,0x1baaa4444322211110f0000f0000f,0x1d8884444222211110f0000f0000f]
def r6p13 : Keys := .leaf [
0x1d8885555222211110f0000f0000f,0x1f000222211110f0000f00048000f,0x1f000222211110f0000f0004f0008,0x1f000222211110f0000ff00400008]
def r6p14 : Keys := .leaf [
0x1f000226211110f0000f0000f0008,0x1f000444422221111020800f0000f,0x1f000444422221111020f00f00008,0x1f00044442222111102f0000f0008]
def r6p15 : Keys := .leaf [
0x1f0004444222211110f0000f0000b,0x1f0004444222211110f0f00f00009,0x1f00044442222111f0f0000f00009,0x1f000444422221f1100f0000f0009]
def r6p16 : Keys := .leaf [
0x1f0004444222a11110f0000f0000f,0x1f0004444222a11110f0000f8000f,0x1f0004444222a11190f0000f0000f,0x1f0004444222b11110f0000f0000f]
def r6p17 : Keys := .leaf [
0x1f000444c222a11110f0000f0000f,0x1f000444f222211110f0000f00008,0x1f000444f222211110f0000f00009,0x1f000444f222211110f0000f80008]
def r6p18 : Keys := .leaf [
0x1f000444f222a11110f0000f00008,0x1f000444f222a11110f0000f0000f,0x1f0004f442222111100f0000f0009,0x1f0004f44222a11110f0000f0000f]
def r6p19 : Keys := .leaf [
0x1f0005555222a11110f0000f0000f,0x1f0006666222a11110f0000f0000f,0x1f000666e222a11110f0000f0000f,0x1f000888822221111066000f0000f]
def r6p20 : Keys := .leaf [
0x1f000888822221f11044000f0000f,0x1f0008888226211110f0000ff000f,0x1f0008888444422221f1100f1000f,0x1f0008888444422221f1102f0000f]
def r6p21 : Keys := .leaf [
0x1f0008888444422f211310f00000f,0x1f000888844442f22111102f0000f,0x1f0008888444f22221f1100f00001,0x1f0008888446422f211110f00000f]
def r6p22 : Keys := .leaf [
0x1f00088884f442222111f00f00001,0x1f00088f8222211110f000044000f,0x1f00088f8222211110f000048000f,0x1f00088f8222211110f00004f000f]
def r6p23 : Keys := .leaf [
0x1f00088f8444f222211110f000004,0x1f00088f8444f222211110f000008,0x1f00088f8666622f211110f00000f,0x1f0008f8822221111044000f0000f]
def r6p24 : Keys := .leaf [
0x1f0008ff822221111044000f0000f,0x1f000a22a444411110f0000f0000f,0x1f000aaaa555533330f0000f0000f,0x1f000aaaa66661111060000f0000f]
def r6p25 : Keys := .leaf [
0x1f000aaaa66661f110f0000f0000f,0x1f000aaaa88f8666611110f00000f,0x1f000aafa666611110f0000f0000f,0x1f000aafa88f8666611110f00000f]
def r6p26 : Keys := .leaf [
0x1f000bbbb666611110f0000f0000f,0x1f0084444222211190f0000f0000f,0x1f008444422221f110f0000f0000f,0x1f0084444222a11110f0000f0000f]
def r6p27 : Keys := .leaf [
0x1f008444c222211110f0000f0000f,0x1f008444f222211110f0000f00008,0x1f008444f222211110f0000f0000f,0x1f0084f44222211110f0000f0000f]
def r6p28 : Keys := .leaf [
0x1f0085555222211110f0000f0000f,0x1f0086666222211110f0000f0000f,0x1f00f4444222211110f0f00f00008,0x1f00f4444222211190f0000f0000f]
def r6p29 : Keys := .leaf [
0x1f00f4444222a11110f0000f0000f,0x1f00f444f222211110f0000f00008,0x1f00f9999555522220f0000f0000f,0x1f00fa22a444411110f0000f0000f]
def r6p30 : Keys := .leaf [
0x1f00faaaa666611110f0000f0000f,0x1f040222211110f0000f0000f0008,0x1f0f04444222211110f0000ff0008,0x1f0f04444222211110ff0000f0008]
def r6p31 : Keys := .leaf [
0x1f0f04444222211190f0000f0000f,0x1f0f04444222a11110f0000f0000f,0x1f0f0444f222211110f0000f00008,0x1f0f088885555222211f10f00000f]
def r6p32 : Keys := .leaf [
0x1f22211110f0000f00040000f0008,0x1f22244441111020000f0000f0008,0x1f222444411110f0000f0000f0008,0x1f222444411110f0000f0000f0009]
def r6p33 : Keys := .leaf [
0x1f222444411110f0000f8000f0008,0x1f222444411110f0000ff00f00008,0x1f222444411110f0800f0000f0008,0x1f222444411110f080f0000f0000f]
def r6p34 : Keys := .leaf [
0x1f222444411110f0f00f0000f0008,0x1f222444411110ff000f0000f0008,0x1f222444411190f0000f0000f0008,0x1f2224444111911110f0000f0000f]
def r6p35 : Keys := .leaf [
0x1f22244441f110f0000f0000f0008,0x1f22244441f11111100f0000f0008,0x1f2224444222211190f0000f0000f,0x1f2224444222a11110f0000f0000f]
def r6p36 : Keys := .leaf [
0x1f222444c11110f0000f0000f0008,0x1f222444f11110f0000f0000f0008,0x1f222444f222211110f0000f00008,0x1f2224f4411110f0000f0000f0008]
def r6p37 : Keys := .leaf [
0x1f222555511110f0000f0000f0008,0x1f222666611110f0000f0000f0008,0x1f222888811110f0000f00044000f,0x1f222888811110f0000f0004f000f]
def r6p38 : Keys := .leaf [
0x1f222888811110f00044000f0000f,0x1f222888811110ff0044000f0000f,0x1f222888844441111020f00f0000f,0x1f222888844441111060000f0000f]
def r6p39 : Keys := .leaf [
0x1f2228888444411110f0000f0000f,0x1f2228888444411110f0000f1000f,0x1f2228888444411110f0000f8000f,0x1f2228888444411110f0002f0000f]
def r6p40 : Keys := .leaf [
0x1f2228888444411110f0008f0000f,0x1f2228888444411110f0100f0000f,0x1f2228888444411110f0200f0000f,0x1f2228888444411110f0400f0000f]
def r6p41 : Keys := .leaf [
0x1f2228888444411110f0800f0000f,0x1f2228888444411110ff000ff000f,0x1f2228888444411110fff00f0000f,0x1f2228888444411130f0000f0000f]
def r6p42 : Keys := .leaf [
0x1f2228888444411190f0000f0000f,0x1f22288884444111f0f0000f00001,0x1f2228888444413110f0000f0000f,0x1f2228888444415110f0000f0000f]
def r6p43 : Keys := .leaf [
0x1f222888844441f00111100f0000f,0x1f222888844441f1100f0000f0001,0x1f222888844441f1100f0000f0004,0x1f222888844441f1100f0000f0008]
def r6p44 : Keys := .leaf [
0x1f222888844441f1100ff00f0000f,0x1f222888844441f11040000f0000f,0x1f222888844441f110f0f00f0000f,0x1f222888844441f11111f00f0000f]
def r6p45 : Keys := .leaf [
0x1f222888844441f11120000f0000f,0x1f222888844441f1f111100f0000f,0x1f222888844441f1f1f1100f0000f,0x1f222888844442f221f1100f0000f]
def r6p46 : Keys := .leaf [
0x1f2228888444433331f1100f0000f,0x1f222888844443f331f1100f0000f,0x1f2228888444f11110f0f00f0000f,0x1f2228888444f44441f1100f0000f]
def r6p47 : Keys := .leaf [
0x1f222888844f444441f1100f0000f,0x1f22288884f4411110f0f00f0000f,0x1f22288884f44222f111100f0000f,0x1f22288884f4444441f1100f0000f]
def r6p48 : Keys := .leaf [
0x1f22288884f4f11110f0f00f0000f,0x1f2228888555511110f0f00f0000f,0x1f2228888555544441f1100f0000f,0x1f22288885f5544441f1100f0000f]
def r6p49 : Keys := .leaf [
0x1f222888866661111060000f0000f,0x1f2228888666611110f0f00f0000f,0x1f2228889444411110f0000f0000f,0x1f222888a444411110f0000f0000f]
def r6p50 : Keys := .leaf [
0x1f2228898444411110f0000f0000f,0x1f22288a8444411110f0000f0000f,0x1f22288c8444411110f0000f0000f,0x1f22288f8444411110f0000ff000f]
def r6p51 : Keys := .leaf [
0x1f22288f8444411110f0f00f0000f,0x1f22288f8444411110ff00f00000f,0x1f22288f8444411f111110f00000f,0x1f22288f844441f110f0000f0000f]
def r6p52 : Keys := .leaf [
0x1f22288f844441f11111100f0000f,0x1f22288f8444422f211110f00000f,0x1f22288f844442f2211110f00000f,0x1f22288f8444f11110f0000f0000f]
def r6p53 : Keys := .leaf [
0x1f22288f88888666611110f00000f,0x1f2228988444411110f0000f0000f,0x1f2228a88444411110f0000f0000f,0x1f2228c88444411110f0000f0000f]
def r6p54 : Keys := .leaf [
0x1f2228f88444411110f0f00f0000f,0x1f2228f8844441f110f0000f0000f,0x1f2228f8844441f11111100f0000f,0x1f2228f884444222f111100f0000f]
def r6p55 : Keys := .leaf [
0x1f2228f8844442f22111100f0000f,0x1f2228f8844443333111100f0000f,0x1f2228f88444f11110f0000f0000f,0x1f2228f884f4411110f0000f0000f]
def r6p56 : Keys := .leaf [
0x1f2228f884f444444111100f0000f,0x1f2228f8866664444111100f0000f,0x1f2228ff8444411110f0000f0000f,0x1f2229888444411110f0000f0000f]
def r6p57 : Keys := .leaf [
0x1f2229999444411110f0f00f0000f,0x1f22299994444111f0f0000f0000f,0x1f222999944441f110f0000f0000f,0x1f222999944441f11111100f0000f]
def r6p58 : Keys := .leaf [
0x1f2229999444433330f0000f0000f,0x1f2229999444f11110f0000f0000f,0x1f22299994f4411110f0000f0000f,0x1f2229999555511110f0000f0000f]
def r6p59 : Keys := .leaf [
0x1f2229999555522220f0000f0000f,0x1f2229999555544440f0000f0000f,0x1f22299f9444411110f0000f0000f,0x1f2229f99444411110f0000f0000f]
def r6p60 : Keys := .leaf [
0x1f2229f9944441f110f0000f0000f,0x1f2229f9944441f11111100f0000f,0x1f222a888444411110f0000f0000f,0x1f222aaaa444411110f0f00f0000f]
def r6p61 : Keys := .leaf [
0x1f222aaaa44441f110f0000f0000f,0x1f222aaaa44441f11111100f0000f,0x1f222aaaa444f11110f0000f0000f,0x1f222aaaa4f4411110f0000f0000f]
def r6p62 : Keys := .leaf [
0x1f222aaaa4f444444111100f0000f,0x1f222aaaa555511110f0000f0000f,0x1f222aaaa666611110f0000f0000f,0x1f222aafa444411110f0000f0000f]
def r6p63 : Keys := .leaf [
0x1f222afaa444411110f0000f0000f,0x1f222bbbb444411110f0000f0000f,0x1f222c888444411110f0000f0000f,0x1f222cccc888844441f1100f0000f]
def r6p64 : Keys := .leaf [
0x1f222f000444411110f0000f8000f,0x1f222f000444411190f0000f0000f,0x1f222f00088884444111102f0000f,0x1f222f00088f8666611110f00000f]
def r6p65 : Keys := .leaf [
0x1f222f008444411110f0000f0000f,0x1f2238888444411110f0000f0000f,0x1f22a444411110f0000f0000f0008,0x1f22a4444222a11110f0000f0000f]
def r6p66 : Keys := .leaf [
0x1f22a8888444411110f0000f0000f,0x1f22af000444411110f0000f0000f,0x1f22af008444411110f0000f0000f,0x1f22af222444411110f0000f0000f]
def r6p67 : Keys := .leaf [
0x1f22faaaa444411110f0000f0000f,0x1f44422221111020000f0000f0008,0x1f444222211110f0000f0000f0008,0x1f444222211110f0000f0000f0009]
def r6p68 : Keys := .leaf [
0x1f444222211110f0000f8000f0008,0x1f444222211110f0000ff00f00008,0x1f444222211110f0800f0000f0008,0x1f444222211110f080f0000f0000f]
def r6p69 : Keys := .leaf [
0x1f444222211110f0f00f0000f0008,0x1f444222211110ff000f0000f0008,0x1f444222211190f0000f0000f0008,0x1f44422221f11111100f0000f0008]
def r6p70 : Keys := .leaf [
0x1f444222a11110f0000f0000f0008,0x1f4444444222211190f0000f0000f,0x1f4444444222a11110f0000f0000f,0x1f444444f222211110f0000f00008]
def r6p71 : Keys := .leaf [
0x1f4444f442222111100f0000f0008,0x1f444888822221111020f00f0000f,0x1f4448888222211130f0000f0000f,0x1f4448888222211190f0000f0000f]
def r6p72 : Keys := .leaf [
0x1f4448888222311110f0000f0000f,0x1f4448888222a11110f0000f0000f,0x1f444888f222211110f0000f00008,0x1f44488f8222211110f0f00f0000f]
def r6p73 : Keys := .leaf [
0x1f4448f882222111100f0000f0001,0x1f4448f8822221111040000f0000f,0x1f4448f88222211110f0f00f0000f,0x1f4448f882222111f111100f0000f]
def r6p74 : Keys := .leaf [
0x1f4448f884f442222111100f0000f,0x1f44499992222111f0f0000f0000f,0x1f4449999555522220f0000f0000f,0x1f444aaaa222211110f0f00f0000f]
def r6p75 : Keys := .leaf [
0x1f444aaaa222f11110f0000f0000f,0x1f444aaaa666611110f0000f0000f,0x1f444f000222a11110f0000f0000f,0x1f444f008222211110f0000f0000f]
def r6p76 : Keys := .leaf [
0x1f444f22211110f0000f0000f0008,0x1f444f222888811110f0f00f0000f,0x1f44c222211110f0000f0000f0008,0x1f44cf008222211110f0000f0000f]
def r6p77 : Keys := .leaf [
0x1f44f222211110f0000f0000f0008,0x1f44f444f222211110f0000f00008,0x1f666222211110f0000f0000f0008,0x1f666aaaa444411110f0000f0000f]
def r6p78 : Keys := .leaf [
0x1f666aaaa666611110f0000f0000f,0x1f666f22211110f0000f0000f0008,0x1f666f22288881111060000f0000f,0x1f666f222888811110f0f00f0000f]
def r6p79 : Keys := .leaf [
0x1f888222211110f0000f00044000f,0x1f888222211110f0000f0004f000f,0x1f888222211110f00044000f0000f,0x1f888222211110ff0044000f0000f]
def r6p80 : Keys := .leaf [
0x1f888444422221111020f00f0000f,0x1f8884444222211110f0000f0000f,0x1f8884444222211130f0000f0000f,0x1f8884444222211190f0000f0000f]
def r6p81 : Keys := .leaf [
0x1f88844442222111f0f0000f00001,0x1f8884444222213110f0000f0000f,0x1f8884444222215110f0000f0000f,0x1f8884444222311110f0000f0000f]
def r6p82 : Keys := .leaf [
0x1f8884444222a11110f0000f0000f,0x1f8884444322211110f0000f0000f,0x1f8884445222211110f0000f0000f,0x1f8884446222211110f0000f0000f]
def r6p83 : Keys := .leaf [
0x1f888444c222211110f0000f0000f,0x1f888444f222211110f0000f00008,0x1f888444f222211110f0f00f0000f,0x1f888444f22221f11111100f0000f]
def r6p84 : Keys := .leaf [
0x1f8884454222211110f0000f0000f,0x1f8884464222211110f0000f0000f,0x1f8884544222211110f0000f0000f,0x1f8884644222211110f0000f0000f]
def r6p85 : Keys := .leaf [
0x1f8884c44222211110f0000f0000f,0x1f8884f442222111100f0000f0001,0x1f8884f442222111100f0000f0004,0x1f8884f442222111100f0000f0008]
def r6p86 : Keys := .leaf [
0x1f8884f442222111100ff00f0000f,0x1f8884f4422221111040000f0000f,0x1f8884f44222211110f0f00f0000f,0x1f8884f442222111f111100f0000f]
def r6p87 : Keys := .leaf [
0x1f8884f4422221f11111100f0000f,0x1f8884f442f222222111100f0000f,0x1f8884f4448002222111100f0000f,0x1f8884f4f222211110f0000f0000f]
def r6p88 : Keys := .leaf [
0x1f8884f4f222211110f0f00f0000f,0x1f8884f4f4f442222111100f0000f,0x1f8884ff44f442222111100f0000f,0x1f8885444222211110f0000f0000f]
def r6p89 : Keys := .leaf [
0x1f8885555222211110f0f00f0000f,0x1f888555522221f110f0000f0000f,0x1f8885555333322220f0000f0000f,0x1f888555f222211110f0000f0000f]
def r6p90 : Keys := .leaf [
0x1f8885f55222211110f0000f0000f,0x1f8885f5522221f11111100f0000f,0x1f8886222444411110f0000f0000f,0x1f8886444222211110f0000f0000f]
def r6p91 : Keys := .leaf [
0x1f8886666222211110f0f00f0000f,0x1f8886666333311110f0000f0000f,0x1f888666f222211110f0000f0000f,0x1f8886f66222211110f0000f0000f]
def r6p92 : Keys := .leaf [
0x1f8887777222211110f0000f0000f,0x1f888a222444411110f0000f0000f,0x1f888c444222211110f0000f0000f,0x1f888cccc4f442222111100f0000f]
def r6p93 : Keys := .leaf [
0x1f888cfcc4f442222111100f0000f,0x1f888f222444411110f0f00f0000f,0x1f888f22244441f110f0000f0000f,0x1f888f22244441f11111100f0000f]
def r6p94 : Keys := .leaf [
0x1f888f222444f11110f0000f0000f,0x1f888f2224f4411110f0000f0000f,0x1f888f222555511110f0000f0000f,0x1f888f222666611110f0000f0000f]
def r6p95 : Keys := .leaf [
0x1f888f444222211110f0f00f0000f,0x1f888f44422221f110f0000f0000f,0x1f888f44422221f11111100f0000f,0x1f888f444f22211110f0000f0000f]
def r6p96 : Keys := .leaf [
0x1f8894444222211110f0000f0000f,0x1f88a4444222211110f0000f0000f,0x1f8a84444222211110f0000f0000f,0x1f8c84444222211110f0000f0000f]
def r6p97 : Keys := .leaf [
0x1f8f84444222211110f0000f0000f,0x1f8f8444f222211110f0000f0000f,0x1f8f84f44222211110f0000f0000f,0x1f8f85555222211110f0000f0000f]
def r6p98 : Keys := .leaf [
0x1f8f86666222211110f0000f0000f,0x1f8f8f222444411110f0000f0000f,0x1f8f8f444222211110f0000f0000f,0x1f999f222444411110f0000f0000f]
def r6p99 : Keys := .leaf [
0x1f999f444222211110f0000f0000f,0x1faaa4444222f11110f0000f0000f,0x1faaa4444333311110f0000f0000f,0x1faaa444f222211110f0000f0000f]
def r6p100 : Keys := .leaf [
0x1faaa4f44222211110f0000f0000f,0x1faaa5555222211110f0000f0000f,0x1faaa6666222211110f0000f0000f,0x1faaa6666444411110f0000f0000f]
def r6p101 : Keys := .leaf [
0x1faaaf000666611110f0000f0000f,0x1faaaf222444411110f0000f0000f,0x1faaaf222444411110f0f00f0000f,0x1faaaf22244441f110f0000f0000f]
def r6p102 : Keys := .leaf [
0x1faaaf22244441f11111100f0000f,0x1faaaf222444f11110f0000f0000f,0x1faaaf2224f4411110f0000f0000f,0x1faaaf222555511110f0000f0000f]
def r6p103 : Keys := .leaf [
0x1faaaf222666611110f0000f0000f,0x1faaaf22f444411110f0000f0000f,0x1faaaf333444411110f0000f0000f,0x1faaaf444222211110f0000f0000f]
def r6p104 : Keys := .leaf [
0x1faaaf444f22211110f0000f0000f,0x1faaaf666222211110f0000f0000f,0x1faaaf666444411110f0000f0000f,0x1faaaf666f00011110f0000f0000f]
def r6p105 : Keys := .leaf [
0x1faaaf666f22211110f0000f0000f,0x1faaaf888666611110f0000f0000f,0x1fafa4444222211110f0000f0000f,0x1fafaf222444411110f0000f0000f]
def r6p106 : Keys := .leaf [
0x1fbbbf222444411110f0000f0000f,0x1fc884444222211110f0000f0000f,0x1ff00f222888844441f1100f0000f,0x1ff11f222888844441f1100f0000f]
def r6p107 : Keys := .leaf [
0x1ff33f222888844441f1100f0000f,0x1ff88f222444411110f0000f0000f,0x1ff88f444222211110f0000f0000f,0x1ffaaf222444411110f0000f0000f]
def r6p108 : Keys := .leaf [
0x1ffccf8884f442222111100f0000f]
def r6 : Keys := .branch 0x1f2228f88444411110f0f00f0000f (.branch 0x1f008444c222211110f0000f0000f (.branch 0x1d8885555222211110f0000f0000f (.branch 0x188884444322211110f0000f0000f (.branch 0x1f222999955550f0000f0000f (.branch 0x1f22244441f1100f0000f0008 (r6p0) (.branch 0x1f22288f8666611110f00000f (r6p1) (r6p2))) (.branch 0x1f444222211110f0800f0000f (r6p3) (.branch 0x1faaa666611110f0000f0000f (r6p4) (r6p5)))) (.branch 0x198884444333322220f0000f0000f (.branch 0x18888444432221f11111100f0000f (r6p6) (.branch 0x188f84444322211110f0000f0000f (r6p7) (r6p8))) (.branch 0x199995444222211110f0000f0000f (.branch 0x198894444222211110f0000f0000f (r6p9) (r6p10)) (.branch 0x1b8884444222211110f0000f0000f (r6p11) (r6p12))))) (.branch 0x1f000888822221f11044000f0000f (.branch 0x1f0004444222a11110f0000f0000f (.branch 0x1f000226211110f0000f0000f0008 (r6p13) (.branch 0x1f0004444222211110f0000f0000b (r6p14) (r6p15))) (.branch 0x1f000444f222a11110f0000f00008 (.branch 0x1f000444c222a11110f0000f0000f (r6p16) (r6p17)) (.branch 0x1f0005555222a11110f0000f0000f (r6p18) (r6p19)))) (.branch 0x1f00088f8444f222211110f000004 (.branch 0x1f0008888444422f211310f00000f (r6p20) (.branch 0x1f00088884f442222111f00f00001 (r6p21) (r6p22))) (.branch 0x1f000aaaa66661f110f0000f0000f (.branch 0x1f0008ff822221111044000f0000f (r6p23) (r6p24)) (.branch 0x1f000bbbb666611110f0000f0000f (r6p25) (r6p26)))))) (.branch 0x1f2228888444411110f0008f0000f (.branch 0x1f222444411110f0000f8000f0008 (.branch 0x1f00faaaa666611110f0000f0000f (.branch 0x1f0085555222211110f0000f0000f (r6p27) (.branch 0x1f00f4444222a11110f0000f0000f (r6p28) (r6p29))) (.branch 0x1f0f04444222211190f0000f0000f (r6p30) (.branch 0x1f22211110f0000f00040000f0008 (r6p31) (r6p32)))) (.branch 0x1f222444c11110f0000f0000f0008 (.branch 0x1f222444411110f0f00f0000f0008 (r6p33) (.branch 0x1f22244441f110f0000f0000f0008 (r6p34) (r6p35))) (.branch 0x1f222888811110f00044000f0000f (.branch 0x1f222555511110f0000f0000f0008 (r6p36) (r6p37)) (.branch 0x1f2228888444411110f0000f0000f (r6p38) (r6p39))))) (.branch 0x1f222888844f444441f1100f0000f (.branch 0x1f222888844441f00111100f0000f (.branch 0x1f2228888444411110f0800f0000f (r6p40) (.branch 0x1f2228888444411190f0000f0000f (r6p41) (r6p42))) (.branch 0x1f222888844441f11120000f0000f (.branch 0x1f222888844441f1100ff00f0000f (r6p43) (r6p44)) (.branch 0x1f2228888444433331f1100f0000f (r6p45) (r6p46)))) (.branch 0x1f2228898444411110f0000f0000f (.branch 0x1f22288884f4f11110f0f00f0000f (r6p47) (.branch 0x1f222888866661111060000f0000f (r6p48) (r6p49))) (.branch 0x1f22288f844441f11111100f0000f (.branch 0x1f22288f8444411110f0f00f0000f (r6p50) (r6p51)) (.branch 0x1f22288f88888666611110f00000f (r6p52) (r6p53))))))) (.branch 0x1f88844442222111f0f0000f00001 (.branch 0x1f22faaaa444411110f0000f0000f (.branch 0x1f2229f9944441f110f0000f0000f (.branch 0x1f2229999444411110f0f00f0000f (.branch 0x1f2228f8844442f22111100f0000f (r6p54) (.branch 0x1f2228f884f444444111100f0000f (r6p55) (r6p56))) (.branch 0x1f2229999444433330f0000f0000f (r6p57) (.branch 0x1f2229999555522220f0000f0000f (r6p58) (r6p59)))) (.branch 0x1f222afaa444411110f0000f0000f (.branch 0x1f222aaaa44441f110f0000f0000f (r6p60) (.branch 0x1f222aaaa4f444444111100f0000f (r6p61) (r6p62))) (.branch 0x1f222f008444411110f0000f0000f (.branch 0x1f222f000444411110f0000f8000f (r6p63) (r6p64)) (.branch 0x1f22a8888444411110f0000f0000f (r6p65) (r6p66))))) (.branch 0x1f4448f884f442222111100f0000f (.branch 0x1f444222a11110f0000f0000f0008 (.branch 0x1f444222211110f0000f8000f0008 (r6p67) (.branch 0x1f444222211110f0f00f0000f0008 (r6p68) (r6p69))) (.branch 0x1f4448888222311110f0000f0000f (.branch 0x1f4444f442222111100f0000f0008 (r6p70) (r6p71)) (.branch 0x1f4448f882222111100f0000f0001 (r6p72) (r6p73)))) (.branch 0x1f44f222211110f0000f0000f0008 (.branch 0x1f444aaaa222f11110f0000f0000f (r6p74) (.branch 0x1f444f22211110f0000f0000f0008 (r6p75) (r6p76))) (.branch 0x1f888222211110f0000f00044000f (.branch 0x1f666aaaa666611110f0000f0000f (r6p77) (r6p78)) (.branch 0x1f888444422221111020f00f0000f (r6p79) (r6p80)))))) (.branch 0x1f888f444222211110f0f00f0000f (.branch 0x1f8884f4f222211110f0f00f0000f (.branch 0x1f8884454222211110f0000f0000f (.branch 0x1f8884444222a11110f0000f0000f (r6p81) (.branch 0x1f888444c222211110f0000f0000f (r6p82) (r6p83))) (.branch 0x1f8884f442222111100ff00f0000f (.branch 0x1f8884c44222211110f0000f0000f (r6p84) (r6p85)) (.branch 0x1f8884f4422221f11111100f0000f (r6p86) (r6p87)))) (.branch 0x1f8886666222211110f0f00f0000f (.branch 0x1f8885555222211110f0f00f0000f (r6p88) (.branch 0x1f8885f55222211110f0000f0000f (r6p89) (r6p90))) (.branch 0x1f888cfcc4f442222111100f0000f (.branch 0x1f8887777222211110f0000f0000f (r6p91) (r6p92)) (.branch 0x1f888f222444f11110f0000f0000f (r6p93) (r6p94))))) (.branch 0x1faaaf22244441f11111100f0000f (.branch 0x1f8f86666222211110f0000f0000f (.branch 0x1f8894444222211110f0000f0000f (r6p95) (.branch 0x1f8f84444222211110f0000f0000f (r6p96) (r6p97))) (.branch 0x1faaa4f44222211110f0000f0000f (.branch 0x1f999f444222211110f0000f0000f (r6p98) (r6p99)) (.branch 0x1faaaf000666611110f0000f0000f (r6p100) (r6p101)))) (.branch 0x1faaaf666f22211110f0000f0000f (.branch 0x1faaaf222666611110f0000f0000f (r6p102) (.branch 0x1faaaf444f22211110f0000f0000f (r6p103) (r6p104))) (.branch 0x1ff33f222888844441f1100f0000f (.branch 0x1fbbbf222444411110f0000f0000f (r6p105) (r6p106)) (.branch 0x1ffccf8884f442222111100f0000f (r6p107) (r6p108)))))))

def a6p0 : Keys := .leaf [
0xc444222211110f88880780787,0xc444222211110f8888780007a,0xc444222219110f8880780007a,0xc444222791110888887807804,0xc444222799110888878000784,0xc44427a211110888880780784,0xc44427a21111088888780007c,0xc44427a21911088880780007d,0xc4442a2791110888878000784,0xc47c222211110888880787801,0xc47c222219110888878000079,0xc47c222791110888880007801,0xc47c2a2211110888878000079,0xc7c4222211110888880780781,0xc7c4222211110888887800079,0xc7c4222219110888807800078,0xc7c42a2211110888807800079,0xcc44222791110888878000784,0xcc4427a21111088880780007c,0xcc7c222211110888878000079,0xf800222211110f88807c0007a,0xf800222211110f8c80780007a,0xf800222211150f8880780007a,0xf8002227911108888780007c4,0xf80022279111088c878000786,0xf800222791150888878000784,0xf80027a211110888807c0007b,0xf80027a21111088c80780007a,0xf80027a21115088880780007a,0xf800444411110f8880780027f,0xf800444411110fa880780007f,0xf800444411310f8880780007f]
def a6p1 : Keys := .leaf [
0xf800444422279111088881786,0xf800444422279111098880786,0xf800444423279111088880786,0xf800447c11110888878000279,0xf800447c111108a887800007b,0xf800447c11310888878000079,0xf800447c2222111108888107b,0xf800447c2222111109888007b,0xf800447c22279111088881003,0xf800447c2227911108888787b,0xf800447c22279111088887f86,0xf800447c222791110f888888b,0xf800447c2322111108888007b,0xf800447c27a2222791110888b,0xf800447c27a7a22791110888b,0xf800447c2aaa91110f888007a,0xf800454422279111088880786,0xf800457c2222111108888007b,0xf80047c41111088880780027e,0xf80047c4111108a880780007f,0xf80047c41131088880780007f,0xf80047c4447c222791110888e,0xf80047fc447c222791110888e,0xf8004ccca22791110f8880787,0xf8004cccafaa911100780007f,0xf8004fccaaaa911100780007a,0xf8004fccafaa911100780007a,0xf800555533330f8880780007a,0xf804222211110f8880780007a,0xf80427a21111088880780007a,0xf807c444222791110f8880786,0xf807c44427a79111088880786]
def a6p2 : Keys := .leaf [
0xf807c47c22221111088887879,0xf807c47c22279111088887801,0xf807c7c422279111088880784,0xf820444411110f8880780007f,0xf82047c41111088880780007f,0xf878444422279111088887f84,0xf878447c222211110f888007b,0xf878447c22279111088887804,0xf878447c27a21111088880079,0xf87847fc2222111108888007b,0xf911222208888780007c00078,0xf911222208888784007800078,0xf9112222088c8780007800078,0xf91122220f888078000780040,0xf91144440888878000780027d,0xf9114444088887a000780007d,0xf911444408a8878000780007d,0xf91144440f88807800200007d,0xf911444422220888810780785,0xf911444422220888817800078,0xf911444422220988807800078,0xf911444422278888878780784,0xf911444422278f8880780007d,0xf911444427a20f8880780007d,0xf91144442aaa8f8880780007d,0xf91144442faa8f8880780007d,0xf911444433330f8880780007f,0xf911447c2222088887f800079,0xf911447c22220f88807800078,0xf911447c22279111088887801,0xf911447c33330888878000078,0xf91147c422220f88807800078]
def a6p3 : Keys := .leaf [
0xf91147c427a20888807800078,0xf91147c43333088880780007d,0xf9114ccca2220f88807800078,0xf9114cccaaaa8780007800078,0xf9114fcca2220f88807800078,0xf911555522220f8880780007a,0xf911555522278888878000785,0xf911555527a20888807800078,0xf915222208888780007800078,0xf93144440888878000780007d,0xfa22111108888780007c00079,0xfa22111108888784007800078,0xfa221111088c8780007800078,0xfa22111508888780007800078,0xfa22444411110888810780786,0xfa2244441111088881780007e,0xfa2244441111098880780007f,0xfa22447c1111088887f80007b,0xfa22447c22279111088887801,0xfa22447c27a21111088880079,0xfa2245441111088880780007e,0xfa2247fc1111088880780007a,0xfa224ccc91110f8880780007a,0xfa224fcc9111088880780007b,0xfa22791144440f8880780007f,0xfa27c44411110888878780784,0xfa27c44427a79111088880784,0xfa27c47c22279111088887801,0xfa27c7c41111088880780007d,0xfb3347c41111088880780007c,0xfb3355550888878000780007d,0xfb33791144440f8880780007f]
def a6p4 : Keys := .leaf [
0xfc4411110888878000780027c,0xfc441111088887a000780007d,0xfc44111108a8878000780007d,0xfc4411310888878000780007d,0xfc44222211110888810780783,0xfc4422221111088881780007b,0xfc4422221111098880780007a,0xfc44222791110888878780786,0xfc4423221111088880780007b,0xfc4427a79111088880780007f,0xfc442aaa91110f8880780007f,0xfc442faa9111088880780007e,0xfc44447c22279111088887804,0xfc4447c422279111088880784,0xfc44791122220f8880780007a,0xfc447a2211110f8880780007a,0xfc7c22221111088887f800079,0xfc7c27a211110888807800078,0xfc7c447c22279111088887804,0xfc7c47fc22221111088880079,0xfd5527a211110888807800079,0xfd55333308888780007800078,0xfd55791122220f8880780007a,0xfd557b3308888780007800078,0xa2221111088888000780007c00079,0xa2221111088888000784007800079,0xa222111108888804078000780007a,0xa2221111088888078780007800042,0xa2221111088888780780000780042,0xa2221111088c8800078000780007c,0xa22211110f8888000078000780042,0xa222111508888800078000780007c]
def a6p5 : Keys := .leaf [
0xa2221911088887800078000780040,0xa2279111088888000780007800044,0xa7a21111088888000078000780042,0xaa221111088887800078000780040,0xc444111108888800078000780027c,0xc44411110888880007a000780007c,0xc4441111088888078780007800207,0xc4441111088888200780007800079,0xc444111108888878078000200007f,0xc444111108a888000780007800079,0xc44411110f888800007800200007f,0xc4441131088888000780007800079,0xc444191108888780007800200007d,0xc4442222111108088780007800079,0xc4442222111108888800010780784,0xc4442222111108888800017800079,0xc4442222111108888807810000786,0xc4442222111108888807878000784,0xc4442222111108888807878780784,0xc444222211110888880787f800784,0xc444222211110888880f878000784,0xc444222211110888887801000007b,0xc4442222111108888878078000079,0xc4442222111108888878078780079,0xc444222211110888887807f800079,0xc4442222111108888878080787801,0xc4442222111108888878878000079,0xc44422221111088f8800878000781,0xc4442222111108f8880807800007c,0xc4442222111109000888807800079,0xc4442222111109888800007800079,0xc444222211110f800888880780784]
def a6p6 : Keys := .leaf [
0xc444222211110f800888887800079,0xc444222211110f878888880780784,0xc444222211110f888800007800079,0xc444222211110f888800807800079,0xc444222211110f88880780780007a,0xc444222211110f888807878000787,0xc444222211110f888807880000784,0xc444222211110f88880800780007c,0xc444222211110f88887800780007f,0xc444222211110f88887807800007a,0xc444222211110f888878080000079,0xc444222211110f888888880780784,0xc444222211110f888888887800079,0xc444222211110f88890000780007b,0xc444222211110ff80888887800079,0xc4442222180011110f8880780007b,0xc444222219110888810000780007b,0xc4442222191108888780007800078,0xc4442222191108888787807800078,0xc44422221911088887f800780007d,0xc4442222191108888807878000784,0xc4442222191108888878078000079,0xc444222219110f800888807800078,0xc444222219110f888780007800078,0xc444222219110f888800007800079,0xc444222219110f888888807800078,0xc4442222191111110f8880780007b,0xc4442222191188888780007800078,0xc444222219190888878000780007d,0xc4442222199988000100007800079,0xc4442222199991110807878000786,0xc444222219999111087807800007b]
def a6p7 : Keys := .leaf [
0xc4442227911108888800010000784,0xc4442227911108888800078000784,0xc4442227911108888800078780784,0xc444222791110888880007f800784,0xc4442227911108888800878000781,0xc4442227911108888807878000784,0xc4442227911108888808078000784,0xc444222791110888887807800007c,0xc4442227911108888878078000784,0xc4442227911108888878080007804,0xc444222791110f800888880000784,0xc444222791110f88880000780007c,0xc444222791110f888888880000784,0xc4442227980011110888878000786,0xc444222799110888878000780007d,0xc4442227991108888800078000784,0xc4442227991111110888878000786,0xc4442227999991110800078000784,0xc4442227a22211110888887807804,0xc4442227a22219110888878000784,0xc444232211110888880000780007c,0xc44427a211110888880000780007c,0xc44427a2111108888800807800079,0xc44427a211110888880780780007a,0xc44427a2111108888807878000784,0xc44427a2111108888807880000784,0xc44427a211110888880800780007c,0xc44427a211110888887800780007f,0xc44427a211110888887807800007c,0xc44427a211110888887808000007c,0xc44427a211110f88880000780007c,0xc44427a218001111088880780007e]
def a6p8 : Keys := .leaf [
0xc44427a219110888878000780007d,0xc44427a219110888880000780007c,0xc44427a219111111088880780007e,0xc44427a219999111080000780007c,0xc44427a2222211110888880780784,0xc44427a2222211110888887800079,0xc44427a2222219110888807800078,0xc44427a2222791110888880000784,0xc44427a791110888880000780007c,0xc44427a7a22791110888880000784,0xc4442800222211110f8880780007a,0xc4442800222791110888878000783,0xc444280027a21111088880780007b,0xc4442807a22211110888878000784,0xc444282811110888878000780007a,0xc4442a2211110888810000780007e,0xc4442a2211110888878000780007d,0xc4442a2211110888878780780007c,0xc4442a221111088887f800780007c,0xc4442a22111108888807878000784,0xc4442a2211110888887807800007c,0xc4442a2211110f80088880780007c,0xc4442a2211110f88880000780007c,0xc4442a2211110f88888880780007c,0xc4442a2219110888878000780007d,0xc4442a2219999111078000780007d,0xc4442a22222791110888878000784,0xc4442a2227a21111088880780007c,0xc4442a2291110888878000780007d,0xc4442a2791110888878000780007d,0xc4442a27911108888800078000784,0xc4442a27911108888807878000784]
def a6p9 : Keys := .leaf [
0xc4442a27a22211110888878000784,0xc4442a27a22791110888878000784,0xc4442a27aa2211110888878000784,0xc4442a2a11110888878000780007d,0xc4442aaa911108008780007800079,0xc4442aaa911108888807878000784,0xc4442aaa91110888887807800007c,0xc4442aaa91110f88880000780007c,0xc4442aaa99110888878000780007d,0xc4442aaaa80011110f8880780007a,0xc4442aaaa80791110888878000784,0xc4442fa211110888880000780007c,0xc4442fa22a221111088880780007c,0xc4442faa91110888880000780007c,0xc4442faa91110f88880000780007c,0xc4442faaa8001111088880780007b,0xc4442faaa80011110f8880780007a,0xc4443333111108888807878000784,0xc444333311110888887807800007c,0xc444333311110f88880000780007c,0xc444333319110888878000780007d,0xc444333319998800078000780007c,0xc4443911222208888780007800078,0xc44439112aaa8888878000780007d,0xc4443a2211110888878000780007d,0xc4443b3311110888878000780007d,0xc4443b3319110888878000780007d,0xc47c1111088888000780002000079,0xc47c2222111108888800010000079,0xc47c2222111108888800078000079,0xc47c2222111108888800078780079,0xc47c222211110888880007f800079]
def a6p10 : Keys := .leaf [
0xc47c2222111108888800878000079,0xc47c2222111108888807878000079,0xc47c2222111108888807878000781,0xc47c2222111108888807880007801,0xc47c222211110888880807800007c,0xc47c2222111108888878078000079,0xc47c222211110f800888880000079,0xc47c222211110f888800007800079,0xc47c222211110f888888880000079,0xc47c222218001111088887800007b,0xc47c2222191108888780007800078,0xc47c2222191108888800078000079,0xc47c222219111111088887800007b,0xc47c2222199991110800078000079,0xc47c2227911108888800078000079,0xc47c2227911108888800078000784,0xc47c2227a22211110888880007801,0xc47c27a211110888880000780007c,0xc47c27a2222211110888880000079,0xc47c280022221111088887800007b,0xc47c2a2211110888878000780007d,0xc47c2a22111108888800078000079,0xc47c2a22222211110888878000079,0xc47c2aaa911108888800078000079,0xc47c2aaaa8001111088887800007b,0xc47c3333111108888800078000079,0xc47c4444222211110888880787801,0xc47c4444222219110888878000079,0xc47c4444222791110888880007804,0xc47c44442a221111088887800007c,0xc5442222111108888800007800079,0xc7c41111088888000078002000079]
def a6p11 : Keys := .leaf [
0xc7c42222111108888800007800079,0xc7c42222111108888800807800079,0xc7c4222211110888880780780007a,0xc7c42222111108888807878000781,0xc7c42222111108888807880000781,0xc7c4222211110888880800780007c,0xc7c4222211110888887800780007f,0xc7c42222111108888878078000079,0xc7c42222111108888878080000079,0xc7c4222211110f888800007800079,0xc7c4222218001111088880780007b,0xc7c42222191108888780007800078,0xc7c42222191108888800007800079,0xc7c4222219111111088880780007b,0xc7c42222199991110800007800079,0xc7c42227911108888800007800079,0xc7c427a2111108888800007800079,0xc7c4280022221111088880780007b,0xc7c42a2211110888878000780007d,0xc7c42a22111108888800007800079,0xc7c42a22222211110888807800079,0xc7c42aaa911108888800007800079,0xc7c42aaaa8001111088880780007b,0xc7c43333111108888800007800079,0xc7c44444222211110888880780784,0xc7c44444222211110888887800079,0xc7c4444422221911088880780007d,0xc7c44444222791110888880000784,0xc7c444442a221111088880780007c,0xc7c4447c222211110888880000079,0xc7fc2222111108888800007800079,0xc7fc447c222211110888880000079]
def a6p12 : Keys := .leaf [
0xc8004444222211110f8880780007f,0xc8004444222791110888878000786,0xc800444427a21111088880780007e,0xc800447c22221111088887800007e,0xc80047c422221111088880780007e,0xc804a22211110888878000780007e,0xc8784444222211110888878000079,0xcc44111108888780007800200007d,0xcc44222211110888810000780007b,0xcc442222111108888780007800078,0xcc442222111108888787807800079,0xcc4422221111088887f8007800079,0xcc442222111108888807878000781,0xcc442222111108888878078000079,0xcc44222211110f800888807800079,0xcc44222211110f888800007800079,0xcc44222211110f888888807800079,0xcc442222191108888780007800078,0xcc442222199991110780007800078,0xcc442227911108888780007800078,0xcc442227911108888800078000784,0xcc442227a22211110888878000781,0xcc4427a2111108888780007800078,0xcc4427a211110888880000780007c,0xcc4427a2222211110888807800079,0xcc442a22111108888780007800078,0xcc442aaa91110888878000780007d,0xcc44333311110888878000780007d,0xcc444444222791110888878000784,0xcc44444427a21111088880780007c,0xcc44447c222211110888878000079,0xcc4447c4222211110888807800079]
def a6p13 : Keys := .leaf [
0xcc44a222111108888780007800078,0xcc4c2222111108888780007800078,0xcc7c2222111108888780007800078,0xcc7c2222111108888800078000079,0xcc7c2222111108888878078000079,0xcc7c4444222211110888878000079,0xcc7c447c222211110888878000079,0xcc7c4c44222211110888878000079,0xcccca22211110808078000780007c,0xcccca222111108888807878000781,0xcccca222111108888878078000079,0xcccca22211110f888800007800079,0xcccca222191108888780007800078,0xcccca227911108888800078000784,0xcccca7a211110888880000780007c,0xccccaa22111108888780007800078,0xccccaaaa911108000780007800079,0xccccaaaaa8001111078000780007a,0xccccc800222211110f8880780007f,0xccccc800222791110888878000786,0xccccc80027a21111088880780007e,0xccccc8002aaa9111078000780007f,0xccccc878222211110888878000079,0xcfc42222111108888800007800079,0xcfc44c44222211110888807800079,0xcfcca222111108888800007800079,0xcfcca22211110f888800007800079,0xcfccc80022221111088880780007e,0xcfccc800222211110f8880780007f,0xd5552222111108888807878000781,0xd5552222111108888878078000079,0xd555222211110f888800007800079]
def a6p14 : Keys := .leaf [
0xd5552222191108888780007800078,0xd5552222199988000780007800079,0xd5552227911108888800078000784,0xd55527a211110888880000780007c,0xd5552a22111108888780007800078,0xd5553333088888000780007800079,0xd911444422220888878000780007d,0xd9114ccca22208888780007800078,0xdc442222111108888780007800078,0xdd552222111108888780007800078,0xdd552222191108888780007800078,0xea22444411110888878000780007d,0xea224ccc91110888878000780007d,0xec442222111108888780007800078,0xec442aaa911108888780007800078,0xf8001111088887800078002400078,0xf8001111088887800078002780040,0xf800111108888780007c00200007d,0xf800111108888780007f802000040,0xf800111108888784007800200007f,0xf8001111088887a00078000780042,0xf8001111088c8780007800200007f,0xf800111108a887800078000780042,0xf80011110f8880780020000780042,0xf800111508888780007800200007d,0xf8001131088887800078000780040,0xf8002222111108888100007c0007b,0xf8002222111108888104007800078,0xf8002222111108888107807800040,0xf8002222111108888178000780040,0xf800222211110888850500780007c,0xf8002222111108888780007800058]
def a6p15 : Keys := .leaf [
0xf8002222111108888780007c00079,0xf8002222111108888780007c80079,0xf8002222111108888780007d0007b,0xf8002222111108888780047c00079,0xf800222211110888878400780007b,0xf8002222111108888784007c0007b,0xf8002222111108888784007f80783,0xf800222211110888878480780007b,0xf800222211110888878500780007b,0xf8002222111108888787807800048,0xf8002222111108888787807c0007b,0xf8002222111108888787847c0007b,0xf80022221111088887c400780007b,0xf80022221111088887f8007c0007b,0xf80022221111088887f8007f80042,0xf80022221111088887fc00780007b,0xf80022221111088887fc007c0007b,0xf80022221111088c810000780007e,0xf80022221111088c878000780007a,0xf80022221111088c8780007c0007a,0xf80022221111088c8780007f80787,0xf80022221111088c878400780007a,0xf80022221111088c878780780007a,0xf80022221111088c87f800780007a,0xf80022221111088d878000780007a,0xf80022221111088f8780007800048,0xf8002222111109888078000780042,0xf800222211110c8c878000780007a,0xf800222211110c8c878780780007a,0xf800222211110f888078000780042,0xf800222211110f888078000780048,0xf800222211110f888078000780052]
def a6p16 : Keys := .leaf [
0xf800222211110f88807800440007f,0xf800222211110f88807c000780042,0xf800222211110f88807c00780007f,0xf800222211110f88807f807800042,0xf800222211110f88840400780007d,0xf800222211110f888780007c0007a,0xf800222211110f88878400780007a,0xf800222211110f888888807c0007b,0xf800222211110f88888c80780007a,0xf800222211110f8c8078000780042,0xf800222211110f8c878000780007a,0xf800222211110f8c878400780007a,0xf800222211110f8c888880780007b,0xf800222211110f8c888c80780007a,0xf800222211110f8c8f8880780007a,0xf800222211150888810000780007e,0xf8002222111508888780007800078,0xf8002222111508888780007c00078,0xf8002222111508888780007f80785,0xf800222211150888878400780007a,0xf800222211150888878780780007a,0xf80022221115088887f800780007a,0xf80022221115088c8780007800078,0xf800222211150f888078000780042,0xf800222211150f88878000780007a,0xf800222211150f88888880780007a,0xf8002222111511110f8880780007a,0xf8002222111588888780007800078,0xf8002222111788888780007800052,0xf8002226111108888780007c00079,0xf800222611110888878400780007a,0xf80022261111088c878000780007a]
def a6p17 : Keys := .leaf [
0xf800222611110f888078000780042,0xf8002226111508888780007800078,0xf8002227911108888100007800046,0xf8002227911108888780007800040,0xf8002227911108888780007800048,0xf8002227911108888780007800052,0xf8002227911108888780007800245,0xf8002227911108888780007800445,0xf8002227911108888780007c00040,0xf8002227911108888780007c00079,0xf8002227911108888780007c00785,0xf8002227911108888780040400784,0xf8002227911108888784007800042,0xf800222791110888878400780007a,0xf8002227911108888787807800042,0xf8002227911108888787840400784,0xf80022279111088887f8007800042,0xf80022279111088c8780007800042,0xf80022279111088c878000780007a,0xf80022279111088c8888878000784,0xf800222791110f888078000780042,0xf800222791110f888888807800042,0xf8002227911508888780007800040,0xf8002227911508888780007800078,0xf8002227911511110888878000786,0xf8002227a222111108888780007c1,0xf8002227a2221111088c878000786,0xf8002227a22211150888878000784,0xf8002322111108888078000780042,0xf80027a2111108888078000780042,0xf80027a2111108888078000780048,0xf80027a2111108888078000780052]
def a6p18 : Keys := .leaf [
0xf80027a211110888807800440007f,0xf80027a211110888807c000780042,0xf80027a211110888807c00780007f,0xf80027a211110888807f807800042,0xf80027a211110888840400780007d,0xf80027a2111108888780007c00079,0xf80027a211110888878400780007a,0xf80027a21111088c8078000780042,0xf80027a21111088c878000780007a,0xf80027a21111088c888880780007c,0xf80027a211110f888078000780042,0xf80027a2111508888078000780042,0xf80027a2111508888780007800078,0xf80027a211151111088880780007e,0xf80027a2222211110888807c0007b,0xf80027a222221111088c80780007a,0xf80027a222221115088880780007a,0xf80027a2222791110888807800042,0xf80027a6111108888078000780042,0xf80027a611110888878400780007a,0xf80027a7911108888078000780042,0xf80027a791110888840400780007d,0xf80027a7a22791110888807800042,0xf80027a7a22791110888840400784,0xf8002aaa911108888780007c00079,0xf8002aaa91110888878400780007a,0xf8002aaa9111088c878000780007a,0xf8002aaa91110f888078000780042,0xf8002aaa911508888780007800078,0xf8002aae9111088c878000780007a,0xf8002faa911108888078000780042,0xf8002faa91110f888078000780042]
def a6p19 : Keys := .leaf [
0xf8003333111108888780007c0007b,0xf800333311110888878400780007a,0xf80033331111088c878000780007a,0xf800333311110f888078000780042,0xf8003333111508888780007800078,0xf8003337111508888780007800078,0xf8004004222211110f8880780007f,0xf8004004222791110888878000786,0xf800400427a21111088880780007f,0xf800407c22221111088887800007b,0xf800444411110888810000780027e,0xf8004444111108888107807800205,0xf800444411110888812000780007b,0xf800444411110888817800200007d,0xf8004444111108888330007800078,0xf800444411110888878000380007d,0xf800444411110888878000780027c,0xf80044441111088887800078002fc,0xf800444411110888878000780037e,0xf8004444111108888780022780784,0xf800444411110888878780780027e,0xf8004444111108888787807f80207,0xf80044441111088887a000780007e,0xf80044441111088887a000780027e,0xf80044441111088887a0007f8007e,0xf80044441111088887a200780007e,0xf80044441111088887a780780007e,0xf80044441111088887a780780027e,0xf80044441111088887a800780007e,0xf80044441111088887b000780007e,0xf80044441111088887f800280007d,0xf80044441111088887f800780027e]
def a6p20 : Keys := .leaf [
0xf80044441111088887f8022780786,0xf8004444111108a8810000780007b,0xf8004444111108a8878000780007f,0xf8004444111108a8878000780027f,0xf8004444111108a88780007f8007a,0xf8004444111108a8878780780007f,0xf8004444111108a887a000780007f,0xf8004444111108a887f800780007f,0xf8004444111108b8878000780007f,0xf8004444111108f8878000280007d,0xf800444411110988807800200007f,0xf800444411110aa8878000780007f,0xf800444411110aa887f800780007f,0xf800444411110f88807800200007f,0xf800444411110f88807800220007a,0xf800444411110f88807800278007a,0xf800444411110f888078002780207,0xf800444411110f88807800280007d,0xf800444411110f88807800300007f,0xf800444411110f88807f80200007f,0xf800444411110f888220007800078,0xf800444411110f88878000780027f,0xf800444411110f8887a000780007f,0xf800444411110f88888880780027e,0xf800444411110f8888a880780007f,0xf800444411110fa8807800200007f,0xf800444411110fa8878000780007f,0xf800444411110fa887a000780007f,0xf800444411110fa8888880780007e,0xf800444411110fa888a880780007f,0xf800444411110fa88f8880780007f,0xf800444411310888810000780007b]
def a6p21 : Keys := .leaf [
0xf800444411310888878000780007d,0xf800444411310888878000780027d,0xf8004444113108888780007f80078,0xf800444411310888878780780007f,0xf80044441131088887a000780007f,0xf80044441131088887f800780007f,0xf8004444113108a8878000780007d,0xf800444411310f88807800200007f,0xf800444411310f88878000780007f,0xf800444411310f88888880780007f,0xf8004444113111110f8880780007f,0xf800444411390888878000780007d,0xf800444411790888878000300007f,0xf8004444202011110f8880780007a,0xf8004444202791110888878000786,0xf800444422220888811100780007b,0xf8004444222211110888810780786,0xf8004444222211110888811780786,0xf800444422221111088881780007b,0xf800444422221111088881780107b,0xf800444422221111088881790007b,0xf8004444222211110888830780786,0xf800444422221111088885780007b,0xf800444422221111088f87800078e,0xf80044442222111108f88780000fb,0xf800444422221111098880780007a,0xf8004444222211110988810780786,0xf800444422221111098881780007b,0xf800444422221111098980780007a,0xf800444422221111099880780007f,0xf8004444222211110b8880780007a,0xf8004444222211110d8880780007f]
def a6p22 : Keys := .leaf [
0xf8004444222211110f8880780007a,0xf8004444222211110f888078000fd,0xf8004444222211110f8880780017f,0xf8004444222211110f8880780027f,0xf8004444222211110f88807880078,0xf8004444222211110f8880790007a,0xf8004444222211110f88807c0007a,0xf8004444222211110f88810780785,0xf8004444222211110f88817800078,0xf8004444222211110f88880780787,0xf8004444222211110f8888780007a,0xf8004444222211110f8980780007a,0xf8004444222211110f8c80780007a,0xf8004444222211110f9880780007f,0xf8004444222211110fa880780007f,0xf800444422221111888f878000787,0xf8004444222211118f8880780007a,0xf8004444222211150f8880780007a,0xf8004444222211178888810100783,0xf8004444222211178888878000794,0xf8004444222211178888878100784,0xf8004444222211178889878000785,0xf8004444222211178f88807800012,0xf80044442222111908f887800007a,0xf8004444222211190f8880780007f,0xf8004444222211310f8880780007f,0xf800444422221179088881100007e,0xf8004444222211790888878000179,0xf8004444222211790888879000079,0xf8004444222211790898878000078,0xf8004444222211790f8880100007f,0xf8004444222217910888810780785]
def a6p23 : Keys := .leaf [
0xf8004444222217910888817800078,0xf8004444222219110f8880780007a,0xf8004444222219998888810780784,0xf8004444222219998888817800079,0xf80044442222200791110f8880787,0xf8004444222291110f8880780007f,0xf8004444222311110f8880780007f,0xf8004444222611110f8880780007f,0xf8004444222791110888810000786,0xf8004444222791110888810100783,0xf8004444222791110888810780786,0xf8004444222791110888811000786,0xf800444422279111088881780007e,0xf8004444222791110888817800786,0xf8004444222791110888817801006,0xf8004444222791110888818000784,0xf8004444222791110888830000781,0xf8004444222791110888850000784,0xf8004444222791110888878000784,0xf800444422279111088887800078c,0xf8004444222791110888878000796,0xf80044442227911108888780007c4,0xf8004444222791110888878001786,0xf8004444222791110888878004784,0xf8004444222791110888878080786,0xf8004444222791110888878100786,0xf8004444222791110888878200786,0xf8004444222791110888878400786,0xf8004444222791110888878800786,0xf8004444222791110888879000786,0xf800444422279111088887a000786,0xf800444422279111088887c000786]
def a6p24 : Keys := .leaf [
0xf800444422279111088887f8007fe,0xf800444422279111088887ff80786,0xf8004444222791110888887807804,0xf8004444222791110889878000783,0xf800444422279111088c878000786,0xf8004444222791110898878000786,0xf80044442227911108a8878000783,0xf80044442227911108f8878000084,0xf800444422279111098880780007f,0xf8004444222791110988810000786,0xf8004444222791110988878000786,0xf8004444222791110988888880784,0xf8004444222791110c88878000786,0xf8004444222791110f80088880786,0xf8004444222791110f88807800008,0xf8004444222791110f88807f80787,0xf8004444222791110f88888f80786,0xf8004444222791110f8888f880786,0xf8004444222791110f8f888880786,0xf8004444222791110ff8888880786,0xf8004444222791118888878000781,0xf8004444222791150888878000784,0xf80044442227911791110f8880787,0xf8004444222791190888878000784,0xf8004444222791310888878000781,0xf8004444222791790888878000106,0xf8004444222791791111088887f86,0xf8004444222799110888878000784,0xf8004444222799998888810000786,0xf80044442227999991110f8880786,0xf80044442227a2221111088881786,0xf80044442227a2221111098880786]
def a6p25 : Keys := .leaf [
0xf8004444222a111108f887800007a,0xf8004444222a11110f8880780007f,0xf8004444222f91110888878000784,0xf8004444223211110f8880780007f,0xf8004444223211790888878000078,0xf8004444223791110888878000786,0xf8004444227a111108a887800007b,0xf8004444227a11310888878000079,0xf800444422a211110f8880780007f,0xf800444423221111088880780007f,0xf8004444232211110888810780786,0xf800444423221111088881780007e,0xf800444423221111098880780007f,0xf8004444232211110f8880780007f,0xf800444423221999888880780007f,0xf8004444232222279111088880786,0xf800444423231111088880780007f,0xf800444423279111088880780007f,0xf8004444232791110888810000786,0xf8004444232791110888810780786,0xf8004444232791110888878000786,0xf80044442327a2221111088880786,0xf80044442327a2279111088880786,0xf80044442327a3221111088880786,0xf800444423321111088880780007f,0xf800444423a21111088880780007f,0xf8004444262211110f8880780007f,0xf800444427221111088880780007f,0xf8004444278022279111088880786,0xf800444427a01111088880780007e,0xf800444427a21111088880780007e,0xf800444427a2111108888078000fc]
def a6p26 : Keys := .leaf [
0xf800444427a21111088880780017e,0xf800444427a21111088880780027e,0xf800444427a21111088880788007c,0xf800444427a21111088880790007e,0xf800444427a211110888807c0007e,0xf800444427a211110888810780786,0xf800444427a21111088881780007e,0xf800444427a211110888820780786,0xf800444427a211110888880780784,0xf800444427a21111088888780007c,0xf800444427a21111088980780007a,0xf800444427a21111088c80780007a,0xf800444427a21111088f807800008,0xf800444427a21111089880780007f,0xf800444427a2111108a880780007f,0xf800444427a21111098880780007f,0xf800444427a211110a8880780007f,0xf800444427a211110c8880780007f,0xf800444427a21111888880780007a,0xf800444427a21115088880780007a,0xf800444427a21119088880780007f,0xf800444427a21131088880780007f,0xf800444427a21179088880100007e,0xf800444427a21911088880780007f,0xf800444427a220079111088880786,0xf800444427a29111088880780007e,0xf800444427a31111088880780007e,0xf800444427a61111088880780007f,0xf800444427a79111088880780007f,0xf800444427a791110888807f80786,0xf800444427a791110f8880780007f,0xf800444427a791179111088880786]
def a6p27 : Keys := .leaf [
0xf800444427a7a2279111088880786,0xf800444427a7a27f9111088880786,0xf800444427aa1111088880780007f,0xf800444427b21111088880780007e,0xf800444427fa22279111088880786,0xf800444427ffa2279111088880786,0xf80044442a2211110f8880780007f,0xf80044442a2791110888878000784,0xf80044442aaa91110888810780786,0xf80044442aaa9111088881780007e,0xf80044442aaa9111098880780007f,0xf80044442aaa91110ff880780007f,0xf80044442aaa9999810000780007e,0xf80044442aaf91110f8880780007f,0xf80044442baa9111088880780007f,0xf80044442baa9111098880780007f,0xf80044442fa21111088880780007e,0xf80044442faa9111088880780007e,0xf80044442faa911108f880780007f,0xf80044442faa91110f8880780007f,0xf80044442faa91110ff880780007f,0xf80044442faa9999911100780007f,0xf80044442faa9f99911100780007f,0xf80044442faaa2279111088880786,0xf80044442faf9111088880780007e,0xf80044442faf91110f8880780007f,0xf80044442fafa2279111088880786,0xf8004444311122220f8880780007a,0xf800444431310888878000780007d,0xf8004444322211110f8880780007f,0xf800444433330888810100780007b,0xf8004444333311110888810780786]
def a6p28 : Keys := .leaf [
0xf800444433331111088881780007e,0xf8004444333311110888830780786,0xf800444433331111098880780007f,0xf8004444333311110b8880780007f,0xf800444433331179088887f80007a,0xf8004444333311790f8880780007f,0xf8004444333319998f8880780007f,0xf8004444333791110888878780786,0xf8004444333791110f8880780007f,0xf80044443337a7a79111088880786,0xf800444437b311110f8880780007f,0xf80044443bbb91110f8880780007f,0xf80044443fbb91110f8880780007f,0xf80044444078222211110f888007a,0xf8004444407822279111088887806,0xf8004444407827a2111108888007e,0xf8004444a2221111088f878000787,0xf8004444a22211110f8880780007a,0xf8004444a22791110888878000784,0xf8004444a7a21111088880780007f,0xf8004445222211110f8880780007a,0xf8004445222211178888878000785,0xf8004445222791110888878000786,0xf800444527a21111088880780007f,0xf8004447a2221111088c878000786,0xf8004447a22211150888878000784,0xf8004447a7a211110888807800042,0xf8004447c444222791110f8880786,0xf800444c222211110f8880780007a,0xf800444c222791110888878000784,0xf800444c27a21111088880780007f,0xf8004454222211110f8880780007a]
def a6p29 : Keys := .leaf [
0xf8004454222791110888878000786,0xf800445427a21111088880780007f,0xf800446411110888878000780027c,0xf80044641111088887a000780007f,0xf8004464111108a8878000780007f,0xf800446411110f88807800200007f,0xf800446411310888878000780007d,0xf8004464222211110f8880780007a,0xf8004464222791110888878000784,0xf800446427a21111088880780007f,0xf800447c11110888810000200007b,0xf800447c11110888878000200007d,0xf800447c111108888780002200078,0xf800447c111108888780002400078,0xf800447c111108888780002780078,0xf800447c111108888780002780205,0xf800447c11110888878000280007d,0xf800447c11110888878000300007f,0xf800447c11110888878000780027c,0xf800447c111108888780022000079,0xf800447c11110888878780200007f,0xf800447c1111088887a000200007f,0xf800447c1111088887a000780007f,0xf800447c1111088887f800200007f,0xf800447c1111088887f8022000079,0xf800447c111108a8878000200007f,0xf800447c111108a8878000780007f,0xf800447c111108a88888878000079,0xf800447c11110f88807800200007f,0xf800447c11110f88888880200007f,0xf800447c11310888878000200007d,0xf800447c11310888878000780007d]
def a6p30 : Keys := .leaf [
0xf800447c11311111088887800007b,0xf800447c20201111088887800007b,0xf800447c22221111088881000007b,0xf800447c22221111088881010007b,0xf800447c22221111088881078007b,0xf800447c222211110888810780783,0xf800447c222211110888810781003,0xf800447c22221111088881100007e,0xf800447c22221111088881780007b,0xf800447c222211110888818000079,0xf800447c222211110888830000079,0xf800447c22221111088885000007c,0xf800447c222211110888878000079,0xf800447c2222111108888780000f9,0xf800447c22221111088887800017b,0xf800447c222211110888878000279,0xf800447c22221111088887800107b,0xf800447c222211110888878002079,0xf800447c22221111088887808007b,0xf800447c22221111088887810007b,0xf800447c22221111088887820007b,0xf800447c22221111088887840007b,0xf800447c2222111108888787807fb,0xf800447c22221111088887880007b,0xf800447c22221111088887900007b,0xf800447c22221111088887a00007b,0xf800447c22221111088887c00007b,0xf800447c22221111088887ff8007b,0xf800447c222211110888880787801,0xf800447c22221111088987800007b,0xf800447c22221111088c87800007e,0xf800447c22221111088f878000009]
def a6p31 : Keys := .leaf [
0xf800447c22221111089887800007e,0xf800447c2222111108a887800007b,0xf800447c22221111098880780007a,0xf800447c22221111098881000007b,0xf800447c22221111098887800007b,0xf800447c222211110988888880079,0xf800447c222211110a8887800007b,0xf800447c222211110f8008888007b,0xf800447c222211110f8880080007c,0xf800447c222211110f88807f8007a,0xf800447c222211110f88888f8007b,0xf800447c222211110f8888f88007a,0xf800447c222211110f8f88888007b,0xf800447c222211110ff888888007b,0xf800447c222211118888878000079,0xf800447c22221115088887800007c,0xf800447c222211178888878000013,0xf800447c22221117911108888787b,0xf800447c22221119088887800007c,0xf800447c222211310888878000079,0xf800447c2222117911110f888007a,0xf800447c222219110888878000079,0xf800447c22221999888881000007b,0xf800447c2222199991110f888007b,0xf800447c222220079111088887803,0xf800447c222291110888878000079,0xf800447c22231111088887800007b,0xf800447c222611110888878000079,0xf800447c22279111088881000007b,0xf800447c222791110888810000786,0xf800447c222791110888878000009,0xf800447c222791110888878000013]
def a6p32 : Keys := .leaf [
0xf800447c222791110888878000020,0xf800447c222791110888878000040,0xf800447c222791110888878000084,0xf800447c222791110888878000106,0xf800447c222791110888878000205,0xf800447c222791110888878000241,0xf800447c222791110888878000405,0xf800447c2227911108888780007f9,0xf800447c222791110888878000801,0xf800447c222791110888878001003,0xf800447c222791110888878002001,0xf800447c222791110888878004004,0xf800447c22279111088887878007b,0xf800447c222791110888878780786,0xf800447c222791110888878787801,0xf800447c22279111088887f80007b,0xf800447c22279111088887f800786,0xf800447c22279111088887f807804,0xf800447c222791110888880007801,0xf800447c22279111088f888887801,0xf800447c2227911108f8888887804,0xf800447c222791110f8880780007a,0xf800447c222791110f8888888007b,0xf800447c222791110f88888880786,0xf800447c222791110f88888887801,0xf800447c222791111000088887803,0xf800447c222791179111088887803,0xf800447c222791791111088887806,0xf800447c222797911111088887801,0xf800447c222799999111088887801,0xf800447c2227a0001111088887803,0xf800447c2227a2221111088881003]
def a6p33 : Keys := .leaf [
0xf800447c2227a222111108888787b,0xf800447c2227a2221111088887f83,0xf800447c2227a22211110f888888b,0xf800447c222a11110888878000079,0xf800447c22321111088887800007b,0xf800447c227a222211110f888007b,0xf800447c227a22279111088887801,0xf800447c227fa2279111088887801,0xf800447c22a211110888878000079,0xf800447c23221111088880780007f,0xf800447c23221111088881000007b,0xf800447c23221111088887800007b,0xf800447c23222222111108888007b,0xf800447c27802222111108888007b,0xf800447c27a21111088880200007f,0xf800447c27a211110888807f8007b,0xf800447c27a2111108f8888880079,0xf800447c27a211110f8880780007f,0xf800447c27a21179111108888007b,0xf800447c27a22227911108888007b,0xf800447c27a222279111088880786,0xf800447c27a222279111088887801,0xf800447c27a22227a22211110888b,0xf800447c27a2227a111108888007b,0xf800447c27a79111088880780007f,0xf800447c27a7a222111108888007b,0xf800447c27a7a227911108888007b,0xf800447c27a7a2279111088880786,0xf800447c27a7a2279111088887801,0xf800447c27a7a227a22211110888b,0xf800447c27fa2222111108888007b,0xf800447c2a2211110888878000079]
def a6p34 : Keys := .leaf [
0xf800447c2aaa9111088881000007b,0xf800447c2aaa91110888878780079,0xf800447c2aaa9111088887f800079,0xf800447c2aaa911108f887800007a,0xf800447c2aaa91110f8880780007f,0xf800447c2aaa91110f8887800007a,0xf800447c2aaa91110f88888880079,0xf800447c2aaa9999911107800007b,0xf800447c2aaaa22211110f888007b,0xf800447c2aaaa2279111088887801,0xf800447c2aaaa7a21111088880079,0xf800447c2aaf91110888878000079,0xf800447c2aafa2279111088887801,0xf800447c2faa9111088880780007f,0xf800447c2faa91110f8880780007f,0xf800447c2faaa222111108888007b,0xf800447c2faaaaaa9111088880079,0xf800447c311122220888878000079,0xf800447c32221111088887800007b,0xf800447c33331111088881000007b,0xf800447c333311110888830000079,0xf800447c33331111088887878007b,0xf800447c33331111088887f80007b,0xf800447c333311110f8880780007f,0xf800447c333311110f8888888007b,0xf800447c333311790888878000078,0xf800447c333319998888878000079,0xf800447c333322279111088887803,0xf800447c333327a2111108888007b,0xf800447c33379111088887800007b,0xf800447c3337a2279111088887803,0xf800447c3bbb91110888878000079]
def a6p35 : Keys := .leaf [
0xf800447c400022279111088887806,0xf800447c44441111088887800027c,0xf800447c4444111108a887800007b,0xf800447c444411310888878000079,0xf800447c44442222111108888107b,0xf800447c44442222111109888007b,0xf800447c444422279111088881006,0xf800447c44442227911108888787e,0xf800447c444422279111088887f86,0xf800447c4444222791110f888888e,0xf800447c44442322111108888007e,0xf800447c444427a2222791110888e,0xf800447c444427a7a22791110888e,0xf800447c44442aaa91110f888007a,0xf800447c4447a2279111088887804,0xf800447ca22211110888878000079,0xf800447d22221111088887800007b,0xf800447fc47c22279111088887804,0xf80044c4222211110f8880780007a,0xf80044c4222791110888878000784,0xf80044c427a21111088880780007f,0xf800454411110888807800200007f,0xf800454422221111088880780007a,0xf8004544222211110888810780783,0xf800454422221111088881780007b,0xf800454422221111098880780007a,0xf8004544222211110f8880780007a,0xf800454422221999888880780007a,0xf800454422279111088880780007a,0xf8004544222791110888810000786,0xf8004544222791110888878000786,0xf80045442227a2221111088880783]
def a6p36 : Keys := .leaf [
0xf800454423221111088880780007a,0xf800454427a21111088880780007f,0xf80045442aaa9111088880780007f,0xf800454433331111088880780007f,0xf8004544444422279111088880786,0xf8004544447c2222111108888007b,0xf800454522221111088880780007a,0xf800455422221111088880780007a,0xf800457c22221111088880780007a,0xf800457c22221111088881000007b,0xf800457c22221111088881780007b,0xf800457c22221111088887800007b,0xf800457c44442222111108888007b,0xf800457c447c2222111108888007b,0xf800457c45442222111108888007b,0xf80045c422221111088880780007a,0xf8004644222211110f8880780007a,0xf800464427a21111088880780007f,0xf800474422221111088880780007a,0xf800474433331111088880780007a,0xf8004780444422279111088880786,0xf8004780447c2222111108888007b,0xf800478422221111088880780007b,0xf80047c411110888807800200007f,0xf80047c411110888807800220007a,0xf80047c411110888807800278007a,0xf80047c4111108888078002780207,0xf80047c411110888807800280007d,0xf80047c411110888807800300007f,0xf80047c411110888807f80200007f,0xf80047c4111108888220007800078,0xf80047c411110888878000780027c]
def a6p37 : Keys := .leaf [
0xf80047c41111088887a000780007f,0xf80047c4111108a8807800200007f,0xf80047c4111108a8878000780007f,0xf80047c4111108a88888807800079,0xf80047c411110f88807800200007f,0xf80047c411310888807800200007f,0xf80047c411310888878000780007d,0xf80047c411311111088880780007b,0xf80047c420201111088880780007a,0xf80047c422221111088880780007a,0xf80047c42222111108888078000f9,0xf80047c422221111088880780017b,0xf80047c422221111088880780027b,0xf80047c4222211110888807880079,0xf80047c422221111088880790007b,0xf80047c4222211110888807c0007b,0xf80047c4222211110888810780783,0xf80047c422221111088881780007b,0xf80047c422221111088884780007b,0xf80047c4222211110888880780781,0xf80047c4222211110888887800079,0xf80047c422221111088980780007a,0xf80047c422221111088c80780007a,0xf80047c422221111089880780007f,0xf80047c42222111108a880780007f,0xf80047c42222111108f880080007c,0xf80047c422221111098880780007a,0xf80047c4222211110a8880780007a,0xf80047c4222211110c8880780007a,0xf80047c422221111888880780007a,0xf80047c422221115088880780007a,0xf80047c4222211178888807800012]
def a6p38 : Keys := .leaf [
0xf80047c422221119088880780007f,0xf80047c422221131088880780007f,0xf80047c422221911088880780007a,0xf80047c4222220079111088880783,0xf80047c422229111088880780007a,0xf80047c422231111088880780007a,0xf80047c422261111088880780007a,0xf80047c4222791110888807800042,0xf80047c4222791110888807f80786,0xf80047c422279111088f888880784,0xf80047c4222791110f8880780007a,0xf80047c4222791179111088880786,0xf80047c4222a1111088880780007a,0xf80047c422321111088880780007a,0xf80047c4227a1111088880200007f,0xf80047c422a21111088880780007a,0xf80047c423221111088880780007a,0xf80047c426221111088880780007a,0xf80047c427a211110f8880780007a,0xf80047c427a79111088880780007f,0xf80047c42a221111088880780007a,0xf80047c42aaa911108f880780007f,0xf80047c42aaa91110f8880780007a,0xf80047c42aaa9999911100780007a,0xf80047c42aaf9111088880780007a,0xf80047c42faa9111088880780007f,0xf80047c42faa91110f8880780007f,0xf80047c431112222088880780007a,0xf80047c432221111088880780007a,0xf80047c4333311110f8880780007a,0xf80047c433331179088880780007f,0xf80047c433331999888880780007a]
def a6p39 : Keys := .leaf [
0xf80047c433379111088880780007a,0xf80047c437b31111088880780007f,0xf80047c43bbb9111088880780007a,0xf80047c440782222111108888007b,0xf80047c444441111088880780027e,0xf80047c44444111108a880780007f,0xf80047c444441131088880780007f,0xf80047c44447a2279111088880786,0xf80047c4447c1111088880200007f,0xf80047c4447c2227911108888007b,0xf80047c4447c22279111088880786,0xf80047c4447c22279111088887804,0xf80047c4447c2227a22211110888b,0xf80047c4447c2aaa9111088880079,0xf80047c4447c3333111108888007b,0xf80047c4447c4444222791110888e,0xf80047c4a2221111088880780007a,0xf80047c522221111088880780007a,0xf80047c7c44422279111088880786,0xf80047c7c47c2222111108888007b,0xf80047cc22221111088880780007a,0xf80047d422221111088880780007b,0xf80047e411110888807800200007f,0xf80047e41111088887a000780007f,0xf80047e422221111088880780007a,0xf80047fc11110888807800200007f,0xf80047fc111108888220007800078,0xf80047fc22221111088880780007a,0xf80047fc222211110888807f8007b,0xf80047fc222211110f8880780007a,0xf80047fc22221179111108888007b,0xf80047fc22279111088880780007a]
def a6p40 : Keys := .leaf [
0xf80047fc27a21111088880780007a,0xf80047fc2aaa9111088880780007a,0xf80047fc33331111088880780007a,0xf80047fc444422279111088880786,0xf80047fc447c1111088880200007f,0xf80047fc447c11110888822000079,0xf80047fc447c2222111108888007b,0xf80047fc447c2227911108888007b,0xf80047fc447c22279111088880786,0xf80047fc447c22279111088887804,0xf80047fc447c2227a22211110888b,0xf80047fc447c2aaa9111088880079,0xf80047fc447c3333111108888007b,0xf80047fc447c4444222791110888e,0xf80047fc447fa222111108888007b,0xf80047ffc47c2222111108888007b,0xf8004c44222211110f8880780007a,0xf8004c44222791110888878000784,0xf8004c4427a21111088880780007f,0xf8004c7c222211110888878000079,0xf8004ccc91110888878000780027c,0xf8004ccc9111088887a000780007f,0xf8004ccc911108a8878000780007f,0xf8004ccc91110f88807800200007f,0xf8004ccc91310888878000780007d,0xf8004ccca22211110888810780783,0xf8004ccca2221111088881780007b,0xf8004ccca2221111098880780007a,0xf8004ccca22211110f8f80780007a,0xf8004ccca2221999810000780007b,0xf8004ccca22791110888810000786,0xf8004ccca22791110888878780784]
def a6p41 : Keys := .leaf [
0xf8004ccca2279111088887f800784,0xf8004ccca2279111088f878000787,0xf8004ccca22791110f8880780007a,0xf8004ccca22791110f88878000787,0xf8004ccca22791110f88888880784,0xf8004ccca22799999111078000786,0xf8004ccca227a22211110f8880787,0xf8004ccca3221111088880780007a,0xf8004ccca7a21111088f80780007a,0xf8004ccca7a211110f8880780007f,0xf8004ccca7a21999911100780007f,0xf8004ccca7a222279111088880784,0xf8004ccca7a79111088880780007f,0xf8004ccca7a7a2279111088880784,0xf8004cccaaaa9111010000780007b,0xf8004cccaaaa9111078780780007a,0xf8004cccaaaa911107f800780007f,0xf8004cccaaaa91110f8880780007a,0xf8004cccaaaaa2279111078000787,0xf8004cccaaaaa7a2111100780007a,0xf8004cccaaaf9111078000780007f,0xf8004cccaaafa2279111078000787,0xf8004cccafaa9111078000780007f,0xf8004cccafaa9111088880780007f,0xf8004cccafaa91110f8880780007f,0xf8004cccafaaa222111100780007a,0xf8004cccafaaa7a2111100780007f,0xf8004cccafaaaaaa911100780007a,0xf8004cccb33311110f8880780007a,0xf8004cccb3331999878000780007a,0xf8004cccbbbb9111078000780007f,0xf8004cccc444222791110f8880786]
def a6p42 : Keys := .leaf [
0xf8004cccc4442faa911100780007f,0xf8004cccc47c22279111088887804,0xf8004cccc47c2aaa911107800007a,0xf8004cccc7c422279111088880784,0xf8004cccc7c42aaa911100780007f,0xf8004cec911108a8878000780007f,0xf8004cfca22211110f8880780007a,0xf8004cfca22791110888878000784,0xf8004cfca7a21111088880780007f,0xf8004cfcaaaa9111078000780007a,0xf8004cfcc47c22279111088887804,0xf8004cfcc47c2aaa911107800007a,0xf8004dcca2221111088880780007a,0xf8004dcca2221111098880780007a,0xf8004fc422221111088880780007b,0xf8004fcc91110888807800200007f,0xf8004fcc91110f88807800200007f,0xf8004fcca2221111088880780007b,0xf8004fcca2221111088f80780007a,0xf8004fcca22211110f8880780007a,0xf8004fcca22211110f8f80780007a,0xf8004fcca2221999911100780007a,0xf8004fcca2221f99911100780007a,0xf8004fcca2279111088880780007a,0xf8004fcca22791110f8880780007a,0xf8004fcca7a21111088880780007a,0xf8004fcca7a211110f8880780007a,0xf8004fccaaaa9111078000780007a,0xf8004fccaaaa9111088880780007a,0xf8004fccaaaa91110f8880780007a,0xf8004fccaaaaa222111100780007a,0xf8004fccafaa9111078000780007a]
def a6p43 : Keys := .leaf [
0xf8004fccafaa9111088880780007a,0xf8004fccafaa91110f8880780007a,0xf8004fccafaaa222111100780007a,0xf8004fccb3331111088880780007a,0xf8004fccb33311110f8880780007a,0xf8004fccc44422279111088880786,0xf8004fccc4442aaa911100780007f,0xf8004fccc4442faa911100780007f,0xf8004fccc47c2222111108888007b,0xf8004fccc7c42aaa911100780007a,0xf8004fcccccca2279111088880784,0xf8004fccccccaaaa911100780007f,0xf8004ffca2221111088880780007a,0xf8004ffca22211110f8880780007a,0xf8004ffcc47c2222111108888007b,0xf8005111444422220f8880780007f,0xf8005111444422278888878000784,0xf8005111444427a2088880780007f,0xf8005115222208888780007800078,0xf8005444222211110f8880780007a,0xf8005444222791110888878000786,0xf800544427a21111088880780007f,0xf800555511110888878000780027e,0xf80055551111088887a000780007f,0xf8005555111108a8878000780007f,0xf800555511110f88807800200007f,0xf800555511310888878000780007d,0xf800555522220888811000780007e,0xf8005555222211110888810780783,0xf800555522221111088881780007b,0xf800555522221111088885780007b,0xf800555522221111098880780007a]
def a6p44 : Keys := .leaf [
0xf8005555222211110d8880780007a,0xf8005555222211178888878780781,0xf8005555222211178f8880780007a,0xf8005555222219998f8880780007a,0xf8005555222791110888810000786,0xf8005555222791110888850000784,0xf8005555222791110888878780786,0xf800555522279111088887f800786,0xf8005555222791110f8880780007a,0xf8005555222791110f88888880786,0xf8005555222791178888878000785,0xf8005555222799998888878000784,0xf800555523221111088880780007a,0xf800555527221111088880780007f,0xf800555527a211110f8880780007f,0xf800555527a21117888880780007a,0xf800555527a21999888880780007f,0xf800555527a222279111088880786,0xf800555527a79111088880780007f,0xf800555527a7a2279111088880786,0xf80055552aaa91110f8880780007f,0xf80055552aaa99998780007800078,0xf80055552faa9111088880780007f,0xf80055552faa91110f8880780007f,0xf800555533330888810000780007b,0xf8005555333308888300007800078,0xf800555533330888850000780007d,0xf800555533330888878780780007a,0xf80055553333088887f800780007f,0xf800555533330f888780007800078,0xf800555533330f88888880780007a,0xf8005555333311110f8880780007a]
def a6p45 : Keys := .leaf [
0xf8005555333322220f8880780007a,0xf8005555333322278888878000785,0xf8005555333327a2088880780007a,0xf800555533378888878000780007d,0xf80055553337a2278888878000785,0xf80055553bbb8888878000780007d,0xf8005555444433330f8880780007f,0xf8005555447c22279111088887806,0xf8005555447c33330888878000078,0xf800555547c422279111088880786,0xf800555547c43333088880780007f,0xf800557511310888878000780007d,0xf800557d22221111088887f80007b,0xf800557d222211110f8880780007a,0xf800557d222791110888878000786,0xf800557d27a21111088880780007f,0xf800557d333308888780007800078,0xf800557d447c22279111088887806,0xf800557d447c33330888878000078,0xf800557d47fc2222111108888007b,0xf80057d5222211110f8880780007a,0xf80057d527a21111088880780007a,0xf8005ddda22211110f8880780007a,0xf8005ddda22791110888878000784,0xf8005ddda7a21111088880780007f,0xf8005dddaaaa9111078000780007a,0xf8005dddb33308888780007800078,0xf8005fdda22211110f8880780007a,0xf8006222444411110f8880780007f,0xf800622247c41111088880780007a,0xf8006444222211110f8880780007a,0xf800644427a21111088880780007f]
def a6p46 : Keys := .leaf [
0xf8006666447c22279111088887801,0xf8006667c47c22279111088887801,0xf800667e447c22279111088887804,0xf800667fc47c22279111088887801,0xf80067a244441111088880780007e,0xf80067c422221111088880780007a,0xf80067e6444422279111088880786,0xf80067e6447c2222111108888007b,0xf80067e7c44422279111088880786,0xf80067fe447c2222111108888007b,0xf800c44422221111088f878000786,0xf800c444222211110f8880780007a,0xf800c444222791110888878000784,0xf800c44427a21111088880780007e,0xf800c47c222211110888878000079,0xf800c7c422221111088880780007b,0xf8014444222211110f8880780007a,0xf8014444222791110888878000784,0xf801444427a21111088880780007e,0xf801447c222211110888878000079,0xf80147c422221111088880780007b,0xf8024444222211110f8880780007a,0xf8024444222791110888878000784,0xf802444427a21111088880780007e,0xf802447c222211110888878000079,0xf80247c422221111088880780007b,0xf804111108888780007800200007d,0xf804222211110888810000780007b,0xf8042222111108888780007800079,0xf8042222111108888780007c00079,0xf8042222111108888780007f80781,0xf8042222111108888784007800079]
def a6p47 : Keys := .leaf [
0xf804222211110888878780780007b,0xf80422221111088887f800780007b,0xf80422221111088c8780007800078,0xf804222211110f888078000780042,0xf804222211110f888780007800078,0xf804222211110f888888807800079,0xf8042222111508888780007800078,0xf8042226111108888780007800078,0xf8042227911108888780007800040,0xf8042227911108888780007800078,0xf80427a2111108888078000780042,0xf80427a2111108888780007800078,0xf80427a2222211110888807800079,0xf8042aaa911108888780007800078,0xf8043333111108888780007800078,0xf8044444222211110f8880780007a,0xf8044444222791110888878000784,0xf804444427a21111088880780007e,0xf804447c222211110888878000079,0xf80447c422221111088880780007b,0xf8047800222211110f8880780007a,0xf804780027a21111088880780007a,0xf804a222111108888780007800079,0xf8052222111108888780007800079,0xf807a222111108888780007800052,0xf807a222111108888780007c00079,0xf807a222111108888784007800079,0xf807a222111108888787807800040,0xf807a222111108888787840400784,0xf807a2221111088c8780007800078,0xf807a22211110f888078000780042,0xf807a222111508888780007800078]
def a6p48 : Keys := .leaf [
0xf807a227911108888780007800040,0xf807a7a2111108888078000780042,0xf807c004222211110888878780786,0xf807c004222211110f8880780007f,0xf807c004222791110888878000786,0xf807c00427a21111088880780007f,0xf807c07c222211110888878000079,0xf807c44411110888878000780027c,0xf807c444111108888780007f80205,0xf807c444111108888787807800205,0xf807c4441111088887a000780007c,0xf807c444111108a8878000780007d,0xf807c44411110f88807800200007f,0xf807c44411310888878000780007d,0xf807c444222211110888810780786,0xf807c44422221111088881780007b,0xf807c44422221111088887f8007fb,0xf807c44422221111088887ff80786,0xf807c44422221111098880780007a,0xf807c444222211110f88807f80787,0xf807c444222211110f88878780786,0xf807c444222211110f88888f80786,0xf807c444222211110f8f888880786,0xf807c444222211110f8f8f8880786,0xf807c444222791110888810000786,0xf807c444222791110888878780784,0xf807c44422279111088887f800784,0xf807c444222791110f8880780007a,0xf807c444222791110f88878000786,0xf807c444222791110f88888880784,0xf807c4442227a22211110f8880786,0xf807c44423221111088880780007e]
def a6p49 : Keys := .leaf [
0xf807c44427a211110888807f80786,0xf807c44427a211110888878780784,0xf807c44427a21111088f888880784,0xf807c44427a211110f8880780007a,0xf807c44427a222279111088880786,0xf807c44427a79111088880780007e,0xf807c44427a791110888878000784,0xf807c44427a791110888878780784,0xf807c44427a7a2221111088880786,0xf807c44427a7a2279111088880786,0xf807c44427a7a7a21111088880786,0xf807c4442aaa91110888878780784,0xf807c4442aaa91110f8880780007a,0xf807c4442aaf91110888878000784,0xf807c4442faa9111088880780007e,0xf807c4442faa91110f8880780007a,0xf807c444333311110888878780786,0xf807c444333311110f8880780007a,0xf807c47c11110888878000200007d,0xf807c47c22221111088881000007b,0xf807c47c2222111108888780007f9,0xf807c47c222211110888878780079,0xf807c47c222211110888878780781,0xf807c47c222211110888878787801,0xf807c47c22221111088887f80007b,0xf807c47c22221111088f888887801,0xf807c47c222211110f8880780007a,0xf807c47c222211110f88888880079,0xf807c47c222791110888878000079,0xf807c47c222791110888878000784,0xf807c47c2227a2221111088887801,0xf807c47c27a21111088880780007a]
def a6p50 : Keys := .leaf [
0xf807c47c27a222221111088880079,0xf807c47c2aaa91110888878000079,0xf807c47c33331111088887800007b,0xf807c47c44442222111108888787c,0xf807c47c444422279111088887804,0xf807c54422221111088880780007b,0xf807c78422221111088880780007b,0xf807c7c411110888807800200007f,0xf807c7c4222211110888807f80783,0xf807c7c4222211110888878780781,0xf807c7c422221111088f888880781,0xf807c7c4222211110f8880780007a,0xf807c7c422279111088880780007a,0xf807c7c4222791110888878000784,0xf807c7c42227a2221111088880783,0xf807c7c427a21111088880780007a,0xf807c7c42aaa9111088880780007a,0xf807c7c433331111088880780007a,0xf807c7c4444422279111088880784,0xf807c7c4447c2222111108888007b,0xf807c7fc22221111088880780007b,0xf807c7fc447c2222111108888007b,0xf807cccca22211110888878780781,0xf807cccca2221111088f878000783,0xf807cccca22211110f8880780007a,0xf807cccca22791110888878000784,0xf807cccca7a21111088880780007a,0xf807ccccaaaa91110780007800078,0xf807cfcca2221111088880780007b,0xf807cfcca22211110f8880780007a,0xf807d115222208888780007800078,0xf807d555222211110888878780783]
def a6p51 : Keys := .leaf [
0xf807d555222211110f8880780007a,0xf807d555222791110888878000786,0xf807d55527a21111088880780007e,0xf807d555333308888780007800078,0xf807f8004444222791110f8880787,0xf807f800444427a79111088880786,0xf807f800447c2222111108888787b,0xf807f800447c22279111088887803,0xf807f80047c422279111088880786,0xf80844442222111108f887800007b,0xf8084444222211110f8880780007f,0xf8084444222791110888878000784,0xf808444427a21111088880780007e,0xf808447c222211110888878000079,0xf80847c422221111088880780007b,0xf8104444222211110f8880780007f,0xf8104444222791110888878000784,0xf810444427a21111088880780007e,0xf810447c222211110888878000079,0xf81047c422221111088880780007b,0xf8201111088887800078000780040,0xf820444411110888810000780007e,0xf820444411110888878000780007c,0xf820444411110888878000780027c,0xf8204444111108888780007f8007c,0xf820444411110888878780780007e,0xf82044441111088887a000780007c,0xf82044441111088887f800780007e,0xf8204444111108a8878000780007d,0xf820444411110f88807800200007f,0xf820444411110f88878000780007d,0xf820444411110f88888880780007c]
def a6p52 : Keys := .leaf [
0xf820444411310888878000780007d,0xf8204444222211110f8880780007f,0xf8204444222791110888878000784,0xf820444427a21111088880780007e,0xf820446411110888878000780007d,0xf820447c11110888878000200007d,0xf820447c11110888878000780007d,0xf820447c222211110888878000079,0xf82047c411110888807800200007f,0xf82047c411110888878000780007d,0xf82047c422221111088880780007b,0xf82047c444441111088880780007c,0xf8204ccc91110888878000780007d,0xf820555511110888878000780007d,0xf8207800444411110f8880780007f,0xf820780047c41111088880780007f,0xf822444411110888878000780007c,0xf827c44411110888878000780007c,0xf827c44411110888878000780027c,0xf828444411110888878000780007c,0xf830444411110888878000780007c,0xf8404444222211110f8880780007f,0xf8404444222791110888878000784,0xf840444427a21111088880780007e,0xf840447c222211110888878000079,0xf84047c422221111088880780007b,0xf8442222111108888780007800079,0xf8782222111108888780007c00079,0xf8782222111108888780007f80040,0xf8782222111108888784007800079,0xf87822221111088887f8000780040,0xf87822221111088c8780007800078]
def a6p53 : Keys := .leaf [
0xf878222211110f888078000780042,0xf8782222111508888780007800078,0xf8782227911108888780007800040,0xf87827a2111108888078000780042,0xf878444411110888878000300007f,0xf878444411110888878000780027c,0xf87844441111088887a000780007c,0xf87844441111088887f800200007d,0xf87844441111088887f8022000079,0xf8784444111108a8878000780007d,0xf878444411110f88807800200007f,0xf878444411310888878000780007d,0xf878444420201111088887f80007b,0xf8784444202011110f8880780007a,0xf8784444202791110888878000784,0xf8784444222211110888810780786,0xf878444422221111088881780007b,0xf87844442222111108888787807f9,0xf878444422221111088887ff8007b,0xf878444422221111098880780007f,0xf8784444222211110f88807f8007a,0xf8784444222211110f8887f80007b,0xf8784444222211110f8888f88007b,0xf8784444222211110ff888888007b,0xf8784444222211110ff88f888007b,0xf8784444222791110888810000786,0xf87844442227911108888780007fc,0xf8784444222791110888878780786,0xf878444422279111088887f80007c,0xf878444422279111088887f800784,0xf878444422279111088887f807804,0xf87844442227911108f8888887804]
def a6p54 : Keys := .leaf [
0xf8784444222791110f8880780007f,0xf8784444222791110f88888880784,0xf87844442227a2221111088887f81,0xf878444423221111088880780007e,0xf878444427a01111088880780007e,0xf878444427a211110888807f8007e,0xf878444427a21111088887f80007c,0xf878444427a2111108f888888007c,0xf878444427a211110f8880780007f,0xf878444427a222279111088880786,0xf878444427a79111088880780007e,0xf878444427a7a2279111088880786,0xf87844442aaa9111088887f80007c,0xf87844442aaa911108f8878000078,0xf87844442aaa91110f8880780007f,0xf87844442faa9111088880780007e,0xf87844442faa91110f8880780007f,0xf878444431310888878000780007d,0xf878444433331111088887f80007e,0xf8784444333311110f8880780007f,0xf878447c11110888878000200007d,0xf878447c20201111088887800007b,0xf878447c22221111088881000007b,0xf878447c222211110888878780079,0xf878447c22221111088887f800079,0xf878447c222211110f8880780007f,0xf878447c222211110f8887800007b,0xf878447c222211110f88888880079,0xf878447c222791110888878000079,0xf878447c222791110888878000784,0xf878447c2227a2221111088887801,0xf878447c27a21111088880780007f]
def a6p55 : Keys := .leaf [
0xf878447c27a211110888878000079,0xf878447c27a222221111088880079,0xf878447c2aaa91110888878000079,0xf878447c33331111088887800007b,0xf878447c4444222211110f888007b,0xf878447c444422279111088887804,0xf878447c444427a2111108888007e,0xf878454422221111088880780007b,0xf87847c411110888807800200007f,0xf87847c420201111088880780007a,0xf87847c4222211110888807f8007b,0xf87847c422221111088887f800079,0xf87847c42222111108f8888880079,0xf87847c4222211110f8880780007f,0xf87847c422279111088880780007f,0xf87847c427a21111088880780007f,0xf87847c42aaa91110888807800079,0xf87847c433331111088880780007b,0xf87847c4444422279111088880784,0xf87847c4447c2222111108888007b,0xf87847fc22221111088880780007b,0xf87847fc222211110888878000079,0xf87847fc22221111088887f800079,0xf87847fc44442222111108888007b,0xf87847fc447c2222111108888007b,0xf87847fc47c42222111108888007b,0xf8784ccca2221111088887f800079,0xf8784ccca22211110f8880780007f,0xf8784ccca22791110888878000784,0xf8784ccca7a21111088880780007f,0xf8784cccaaaa9111078000780007d,0xf8784cfca22211110888878000079]
def a6p56 : Keys := .leaf [
0xf8784fcca2221111088880780007b,0xf8784fcca22211110f8880780007f,0xf878555522221111088887f80007b,0xf8785555222211110f8880780007f,0xf8785555222791110888878000786,0xf878555527a21111088880780007e,0xf878555533330888878000780007d,0xf8787800444422279111088887f86,0xf8787800447c222211110f888007a,0xf8787800447c22279111088887806,0xf8787800447c27a2111108888007b,0xf878780047fc2222111108888007b,0xf87c2222111108888780007800079,0xf87c2222111108888780007c00079,0xf87fc444222211110888878780784,0xf87fc44422221111088887f800079,0xf87fc444222211110f8880780007a,0xf87fc444222791110888878000784,0xf87fc44427a21111088880780007e,0xf87fc47c222211110888878000079,0xf87fc7c422221111088880780007b,0xf888c444222211110807878000787,0xf888c44422221111087807800007a,0xf888c44427a21111080000780007c,0xf888c7c4222211110800007800079,0xf888f8004444222791110f8880787,0xf888f800447c222211110f888007a,0xf888f800447c22279111088887803,0xf9004444222211110888810780786,0xf900444422221111088881780007b,0xf900444422221111098880780007a,0xf9004444222211110f8880780007a]
def a6p57 : Keys := .leaf [
0xf9004444222791110888810000786,0xf9004444222791110888878000784,0xf900444423221111088880780007e,0xf900444427a21111088880780007e,0xf900447c22221111088881000007b,0xf900447c222211110888878000079,0xf900454422221111088880780007b,0xf90047c422221111088880780007b,0xf907c444222211110888810780786,0xf9110888878000780020000780040,0xf9112222088881000078000780040,0xf9112222088887800078000780040,0xf9112222088887800078000780048,0xf9112222088887800078000780052,0xf911222208888780007800440007d,0xf911222208888780007c000780040,0xf911222208888780007c00780007d,0xf911222208888780007f807800040,0xf911222208888780040400780007d,0xf9112222088887840078000780040,0xf9112222088887840780007800078,0xf9112222088887878078000780040,0xf911222208888787840400780007d,0xf9112222088887f80078000780040,0xf9112222088c87800078000780040,0xf9112222088c88888780007800078,0xf91122220f8887800078000780040,0xf91122220f8888888078000780040,0xf9112222111108888780007c00079,0xf911222211110888878400780007b,0xf91122221111088c8780007800078,0xf911222211110f888078000780042]
def a6p58 : Keys := .leaf [
0xf9112222111508888780007800078,0xf9112226088887800078000780040,0xf9112227888887800078000780040,0xf9112227911108888780007800040,0xf91127a2088887800078000780040,0xf91127a2111108888078000780042,0xf9112aaa888887800078000780040,0xf9113333088887800078000780040,0xf911400422220888878000780007f,0xf911444408888100007800200007d,0xf911444408888780007800200007d,0xf9114444088887800078002200078,0xf9114444088887800078002780078,0xf9114444088887800078002780205,0xf911444408888780007800280007d,0xf911444408888780007800300007f,0xf911444408888780007f80200007d,0xf9114444088887800220007800078,0xf911444408888787807800200007d,0xf9114444088887a0007800200007d,0xf9114444088887a0078000780007d,0xf9114444088887f8007800200007d,0xf9114444088887f80220007800078,0xf911444408a88780007800200007d,0xf911444408a88888878000780007d,0xf91144440f888780007800200007d,0xf91144440f888888807800200007d,0xf911444411110888878000780027c,0xf91144441111088887a000780007e,0xf9114444111108a8878000780007d,0xf911444411110f88807800200007f,0xf911444411310888878000780007d]
def a6p59 : Keys := .leaf [
0xf911444420200888878000780007a,0xf911444422220888810000780007b,0xf911444422220888810100780007b,0xf9114444222208888107807800078,0xf9114444222208888107810000786,0xf911444422220888811000780007e,0xf911444422220888817800780007d,0xf911444422220888817801000007b,0xf9114444222208888180007800079,0xf9114444222208888300007800078,0xf911444422220888850000780007d,0xf9114444222208888780007800078,0xf91144442222088887800078000fd,0xf911444422220888878000780017f,0xf911444422220888878000780027d,0xf9114444222208888780007880078,0xf911444422220888878000790007a,0xf9114444222208888780007c00078,0xf9114444222208888780010780785,0xf9114444222208888780017800078,0xf9114444222208888780020780785,0xf9114444222208888780047800078,0xf9114444222208888780807800078,0xf9114444222208888781007800078,0xf9114444222208888782007800078,0xf9114444222208888784007800078,0xf9114444222208888787807f80785,0xf911444422220888878800780007d,0xf911444422220888879000780007d,0xf91144442222088887a000780007d,0xf91144442222088887c000780007d,0xf91144442222088887f8007f80078]
def a6p60 : Keys := .leaf [
0xf91144442222088887ff807800078,0xf9114444222208888807878000787,0xf911444422220888887807800007a,0xf9114444222208898780007800078,0xf91144442222088c8780007800078,0xf91144442222088f8780007800008,0xf911444422220898878000780007d,0xf9114444222208a8878000780007d,0xf9114444222208f8878000080007d,0xf9114444222209000888807800079,0xf911444422220988810000780007b,0xf9114444222209888780007800078,0xf9114444222209888888807800079,0xf911444422220a888780007800078,0xf911444422220c88878000780007d,0xf911444422220f800888807800078,0xf911444422220f888078000780008,0xf911444422220f888078000780012,0xf911444422220f888078000780020,0xf911444422220f888078000780040,0xf911444422220f88807800080007d,0xf911444422220f88807800100007f,0xf911444422220f88807800200007d,0xf911444422220f88807800400007d,0xf911444422220f88807f807800078,0xf911444422220f888080007800079,0xf911444422220f88810000780007b,0xf911444422220f888200007800078,0xf911444422220f88840000780007d,0xf911444422220f888787807800078,0xf911444422220f8887f800780007d,0xf911444422220f888800007800079]
def a6p61 : Keys := .leaf [
0xf911444422220f88888f807800078,0xf911444422220f8888f880780007d,0xf911444422220f888900007800078,0xf911444422220f8f8888807800078,0xf911444422220f8f8f88807800078,0xf911444422220ff8888880780007d,0xf911444422220ff88f8880780007d,0xf9114444222210000f8880780007b,0xf9114444222211110888810780786,0xf911444422221111088881780007b,0xf911444422221111098880780007a,0xf9114444222211178888878780784,0xf9114444222211178f8880780007a,0xf911444422221179088887f800079,0xf9114444222211790f8880780007f,0xf9114444222217910f88807800078,0xf9114444222219998f88807800078,0xf911444422221f998f88807800078,0xf9114444222220000f8880780007a,0xf911444422228888878000780007d,0xf911444422230888878000780007d,0xf911444422260888878000780007d,0xf911444422278888810000780007e,0xf9114444222788888780007800012,0xf9114444222788888780007f80785,0xf9114444222788888787807800078,0xf9114444222788888787878000785,0xf91144442227888887f800780007d,0xf91144442227888f8888878000785,0xf911444422278f88878000780007d,0xf911444422278f88888880780007d,0xf9114444222791110888810000786]
def a6p62 : Keys := .leaf [
0xf9114444222791110888878780786,0xf911444422279111088887f800786,0xf9114444222791110f8880780007f,0xf9114444222791110f88888880784,0xf9114444222791178888878000784,0xf9114444222791790888878000784,0xf9114444222797910888878000785,0xf9114444222799998888878000784,0xf91144442227a2220888878780784,0xf91144442227a2220f88807800078,0xf9114444222a0888878000780007d,0xf911444422320888878000780007d,0xf9114444227a22220f88807800078,0xf911444422a20888878000780007d,0xf911444423220888810000780007e,0xf911444423220888878000780007d,0xf911444423221111088880780007e,0xf911444426220888878000780007d,0xf911444427a20888810000780007e,0xf911444427a208888787807800078,0xf911444427a2088887f800780007d,0xf911444427a20f88878000780007d,0xf911444427a20f88888880780007d,0xf911444427a211110f8880780007f,0xf911444427a211178888807800078,0xf911444427a21179088880780007d,0xf911444427a21791088880780007d,0xf911444427a21999888880780007d,0xf911444427a222220f88807800078,0xf911444427a222279111088880786,0xf911444427a78888878000780007d,0xf911444427a788888787807800078]
def a6p63 : Keys := .leaf [
0xf911444427a79111088880780007e,0xf911444427a7a2279111088880786,0xf91144442a220888878000780007d,0xf91144442aaa8888810000780007e,0xf91144442aaa88888787807800078,0xf91144442aaa888887f800780007d,0xf91144442aaa88f8878000780007d,0xf91144442aaa8f88878000780007d,0xf91144442aaa8f88888880780007d,0xf91144442aaa91110f8880780007f,0xf91144442aaa9999878000780007d,0xf91144442aaaa2220f88807800078,0xf91144442aaf8888878000780007d,0xf91144442faa8888878000780007d,0xf91144442faa8f88878000780007d,0xf91144442faa8f88888880780007d,0xf91144442faa9111088880780007e,0xf91144442faa91110f8880780007f,0xf91144442faaa2220f88807800078,0xf911444432220888878000780007d,0xf911444433330888810000780007e,0xf9114444333308888300007800078,0xf9114444333308888787807800078,0xf91144443333088887f800780007d,0xf911444433330f88878000780007d,0xf911444433330f88888880780007d,0xf9114444333311110f8880780007f,0xf9114444333322220f8880780007a,0xf911444433378888878000780007d,0xf911444437b30888878000780007d,0xf91144443bbb8888878000780007d,0xf9114444400022220f8880780007f]
def a6p64 : Keys := .leaf [
0xf9114444a22208888780007800078,0xf9114445222208888780007800078,0xf9114447c44422220f8880780007d,0xf9114447c44422278888878000784,0xf911444c222208888780007800078,0xf9114454222208888780007800078,0xf911446408888780007800200007d,0xf9114464222208888780007800078,0xf911447c08888780007800200007d,0xf911447c11110888878000200007d,0xf911447c22220888810000780007b,0xf911447c22220888878000100007e,0xf911447c222208888780007f80078,0xf911447c222208888787807800078,0xf911447c2222088887f800780007d,0xf911447c2222088887f8078000078,0xf911447c222208f88888878000078,0xf911447c22220f888780007800078,0xf911447c22220f888888807800078,0xf911447c22221111088881000007b,0xf911447c22221111088887878007b,0xf911447c22221111088887f80007b,0xf911447c222211110f8880780007a,0xf911447c222211110f88888880079,0xf911447c222211178888878000079,0xf911447c222211790888878000078,0xf911447c222217910888878000078,0xf911447c222219998888878000079,0xf911447c222788888780007800078,0xf911447c222791110888878000079,0xf911447c222791110888878000784,0xf911447c2227a2221111088887801]
def a6p65 : Keys := .leaf [
0xf911447c227a22220888878000079,0xf911447c27a20888878000780007d,0xf911447c27a21111088880780007e,0xf911447c27a22222111108888007b,0xf911447c2aaa8888878000780007d,0xf911447c2aaa91110888878000079,0xf911447c33330888878000780007d,0xf911447c33331111088887800007b,0xf911447c333322220888878000079,0xf911447c44442222088887f800079,0xf911447c444422220f8880780007d,0xf911447c444422279111088887804,0xf911447c444433330888878000078,0xf91144c4222208888780007800078,0xf911454422220888810000780007b,0xf9114544222208888780007800078,0xf911454422221111088880780007b,0xf9114644222208888780007800078,0xf91147c408888780007800200007d,0xf91147c411110888807800200007f,0xf91147c422220888810000780007b,0xf91147c4222208888787807800078,0xf91147c42222088887f800780007d,0xf91147c422220f888780007800078,0xf91147c422220f888888807800078,0xf91147c4222211110f8880780007a,0xf91147c4222211178888807800078,0xf91147c422221179088880780007d,0xf91147c4222217910888807800078,0xf91147c4222219998888807800078,0xf91147c4222788888780007800078,0xf91147c422279111088880780007a]
def a6p66 : Keys := .leaf [
0xf91147c427a208888780007800078,0xf91147c427a21111088880780007a,0xf91147c427a222220888807800078,0xf91147c42aaa8888878000780007d,0xf91147c42aaa91110888807800079,0xf91147c433330888878000780007d,0xf91147c433331111088880780007b,0xf91147c4333322220888807800078,0xf91147c4444422220f8880780007d,0xf91147c4444422279111088880786,0xf91147c4444427a2088880780007d,0xf91147c444443333088880780007d,0xf91147c4447c2222111108888007b,0xf91147fc222208888780007800078,0xf91147fc2222088887f800780007d,0xf91147fc22221111088880780007b,0xf91147fc447c2222111108888007b,0xf9114c44222208888780007800078,0xf9114ccc88888780007800200007d,0xf9114ccca2220888810000780007b,0xf9114ccca22208888787807800078,0xf9114ccca222088887f800780007d,0xf9114ccca222088f8780007800078,0xf9114ccca2220f888780007800078,0xf9114ccca2220f888888807800078,0xf9114ccca22211110f8880780007a,0xf9114ccca22219998780007800078,0xf9114ccca22788888780007800078,0xf9114ccca22791110888878000784,0xf9114ccca7a208888780007800078,0xf9114ccca7a21111088880780007c,0xf9114cccaaaa88888780007800078]
def a6p67 : Keys := .leaf [
0xf9114cccaaaa91110780007800078,0xf9114cccaaaaa2220780007800078,0xf9114cccb3330888878000780007d,0xf9114cccc44422220f8880780007d,0xf9114cccc4442aaa878000780007d,0xf9114cfca22208888780007800078,0xf9114fcca22208888780007800078,0xf9114fcca2220f888780007800078,0xf9114fcca2220f888888807800078,0xf9114fcca2221111088880780007b,0xf9114fcca22211110f8880780007a,0xf9114fccc44422220f8880780007d,0xf9115444222208888780007800078,0xf911555508888780007800200007d,0xf911555522220888810000780007b,0xf911555522220888850000780007d,0xf9115555222208888787807800078,0xf91155552222088887f800780007d,0xf911555522220f888780007800078,0xf911555522220f888888807800078,0xf9115555222211110f8880780007a,0xf9115555222788888780007800078,0xf9115555222791110888878000786,0xf91155552227a2220888878000785,0xf911555527a208888780007800078,0xf911555527a21111088880780007e,0xf911555527a222220888807800078,0xf91155552aaa88888780007800078,0xf9115555333308888780007800078,0xf9115555444422220f8880780007f,0xf9115555444422278888878000784,0xf9115555444427a2088880780007d]
def a6p68 : Keys := .leaf [
0xf911557d222208888780007800078,0xf91157d5222208888780007800078,0xf9115ddda22208888780007800078,0xf911622244440888878000780007d,0xf9116444222208888780007800078,0xf9116666444422220f88807800078,0xf9117800222208888780007c00078,0xf911780022220888878400780007a,0xf91178002222088c8780007800078,0xf911780022220f888078000780042,0xf911780044440888878000780027d,0xf91178004444088887a000780007f,0xf9117800444408a8878000780007d,0xf911780044440f88807800200007f,0xf9117800444422220888810780785,0xf9117800444422220888817800078,0xf911780044442222098880780007a,0xf9117800444422278888878780784,0xf9117800444422278f8880780007f,0xf9117800444427a20f8880780007f,0xf911780044442aaa8f8880780007f,0xf911780044442faa8f8880780007f,0xf9117800444433330f8880780007f,0xf9117800447c2222088887f800079,0xf9117800447c22220f8880780007a,0xf9117800447c22279111088887803,0xf9117800447c33330888878000078,0xf911780047c422220f8880780007a,0xf911780047c427a2088880780007a,0xf911780047c43333088880780007a,0xf91178004ccca2220f8880780007a,0xf91178004cccaaaa878000780007a]
def a6p69 : Keys := .leaf [
0xf91178004fcca2220f8880780007a,0xf9117800555522220f8880780007a,0xf9117800555522278888878000785,0xf9117800555527a2088880780007f,0xf9117804222208888780007800078,0xf9117807c44422220888878780784,0xf9117807c44422220f8880780007a,0xf911782044440888878000780007d,0xf911787844442222088887f800079,0xf9117878444422220f8880780007f,0xf9117888c44422220f8880780007a,0xf911c444222208888780007800078,0xf9152222088887800078000780040,0xf9152222111108888780007800079,0xf9152222111508888780007800078,0xf9154444222208888780007800078,0xf9157800222208888780007800078,0xf9157804222208888780007800078,0xf9157911222208888780007800078,0xf917c444222211110888878780784,0xf917c444222211110f8880780007a,0xf917c444222791110888878000784,0xf917c44427a21111088880780007e,0xf917c47c222211110888878000079,0xf917c7c422221111088880780007b,0xf917d555222208888780007800078,0xf917f911444422220888878780784,0xf917f911444422220f8880780007a,0xf919444422220888878000780007d,0xf931444408888780007800200007d,0xf931444411110888878000780007c,0xf931444411310888878000780007d]
def a6p70 : Keys := .leaf [
0xf931444422220888878000780007d,0xf931780044440888878000780007d,0xf931782044440888878000780007d,0xf931791144440888878000780007d,0xf978444422221111088881780007b,0xf979444422221111088887f800079,0xf9794444222211110f8880780007f,0xf9794444222791110888878000784,0xf979444427a21111088880780007e,0xf979444433330888878000780007d,0xf979447c222211110888878000079,0xf97947c422221111088880780007b,0xf979791144442222088887f800079,0xf9797911444422220f8880780007f,0xf999f911444422220f8880780007a,0xfa004444222791110888878000784,0xfa00444427a21111088880780007e,0xfa00447c222211110888878000079,0xfa0047c422221111088880780007b,0xfa20444411110888878000780007c,0xfa2044441111088887f800780007c,0xfa221111088881000078000780040,0xfa221111088887800078000780040,0xfa221111088887800078000780048,0xfa221111088887800078000780052,0xfa22111108888780007800440007d,0xfa22111108888780007c000780040,0xfa22111108888780007c00780007d,0xfa22111108888780007f807800040,0xfa22111108888780040400780007d,0xfa221111088887840078000780040,0xfa221111088887840780007800078]
def a6p71 : Keys := .leaf [
0xfa221111088887878078000780040,0xfa22111108888787840400780007d,0xfa221111088887f80078000780040,0xfa221111088c87800078000780040,0xfa221111088c8888878000780007c,0xfa2211110f8888888078000780040,0xfa221115088887800078000780040,0xfa22111511110888878000780007e,0xfa222222111108888780007c00079,0xfa22222211110888878400780007b,0xfa2222221111088c8780007800078,0xfa222222111508888780007800078,0xfa222227911108888780007800040,0xfa2227a2111108888078000780040,0xfa22400411110888878000780007f,0xfa22444411110888810000780007e,0xfa22444411110888810100780007b,0xfa224444111108888107807800078,0xfa224444111108888107810000786,0xfa22444411110888811000780007e,0xfa22444411110888817800780007d,0xfa22444411110888817801000007e,0xfa22444411110888818000780007c,0xfa224444111108888300007800079,0xfa22444411110888850000780007c,0xfa22444411110888878000780007c,0xfa2244441111088887800078000fc,0xfa22444411110888878000780017e,0xfa22444411110888878000780027c,0xfa22444411110888878000788007c,0xfa22444411110888878000790007e,0xfa224444111108888780007c0007c]
def a6p72 : Keys := .leaf [
0xfa224444111108888780010780786,0xfa22444411110888878001780007e,0xfa224444111108888780020780784,0xfa22444411110888878004780007c,0xfa22444411110888878080780007c,0xfa22444411110888878100780007c,0xfa22444411110888878200780007c,0xfa22444411110888878400780007c,0xfa224444111108888787807f80784,0xfa22444411110888878800780007c,0xfa22444411110888879000780007c,0xfa2244441111088887a000780007c,0xfa2244441111088887c000780007c,0xfa2244441111088887f8007f8007c,0xfa2244441111088887ff80780007c,0xfa224444111108888807878000784,0xfa22444411110888887807800007c,0xfa224444111108898780007800078,0xfa2244441111088c8780007800078,0xfa22444411110898878000780007d,0xfa224444111108a8878000780007d,0xfa224444111108f8878000080007c,0xfa22444411110988810000780007e,0xfa22444411110988878000780007d,0xfa22444411110988888880780007c,0xfa22444411110c88878000780007d,0xfa22444411110f80088880780007c,0xfa22444411110f88880000780007c,0xfa22444411110f88888f80780007a,0xfa22444411110f8888f880780007f,0xfa22444411110f8f888880780007c,0xfa22444411110ff8888880780007c]
def a6p73 : Keys := .leaf [
0xfa224444111188888780007800078,0xfa224444111508888780007800078,0xfa224444111788888780007800012,0xfa224444111791110888878780786,0xfa22444411190888878000780007d,0xfa22444411310888878000780007d,0xfa22444411791111088887f80007e,0xfa22444417910888810000780007e,0xfa22444419110888878000780007d,0xfa22444419998888810000780007e,0xfa224444199991110f8880780007f,0xfa224444200791110888878000784,0xfa224444222211110888810780786,0xfa22444422221111088881780007b,0xfa22444422221111098880780007a,0xfa224444222791110888810000786,0xfa224444222791110888878780784,0xfa22444422279111088887f800784,0xfa224444222791110f88888880784,0xfa22444423221111088880780007e,0xfa22444427801111088880780007c,0xfa22444427a222279111088880784,0xfa22444427a79111088880780007e,0xfa22444427a7a2279111088880786,0xfa22444427fa1111088880780007e,0xfa2244442faa9111088880780007e,0xfa22444431110888878000780007d,0xfa22444491110888878000780007d,0xfa22444511110888878000780007d,0xfa224447911108888780007800040,0xfa22444c11110888878000780007d,0xfa22445411110888878000780007d]
def a6p74 : Keys := .leaf [
0xfa22446411110888878000780007d,0xfa22447c11110888810000780007e,0xfa22447c11110888878000200007d,0xfa22447c111108888780007f80079,0xfa22447c111108888787807800078,0xfa22447c1111088887f800780007d,0xfa22447c1111088887f8078000079,0xfa22447c111108f88888878000079,0xfa22447c11110f88888880780007c,0xfa22447c11791111088887800007b,0xfa22447c22221111088881000007b,0xfa22447c22221111088887878007b,0xfa22447c22221111088887f80007b,0xfa22447c222211110f88888880079,0xfa22447c222791110888878000079,0xfa22447c222791110888878000784,0xfa22447c2227a2221111088887801,0xfa22447c227a11110888878000079,0xfa22447c27a21111088880780007c,0xfa22447c27a211110888878000079,0xfa22447c27a222221111088880079,0xfa22447c2aaa91110888878000079,0xfa22447c33331111088887800007b,0xfa22447c44441111088887f80007c,0xfa22447c444422279111088887804,0xfa22447c444427a2111108888007c,0xfa2244c411110888878000780007d,0xfa22454411110888810000780007e,0xfa22454411110888878000780007d,0xfa22454422221111088880780007b,0xfa22454444441111088880780007e,0xfa22464411110888878000780007d]
def a6p75 : Keys := .leaf [
0xfa22478044441111088880780007c,0xfa2247c4111108888078000780008,0xfa2247c4111108888078000780012,0xfa2247c4111108888078000780022,0xfa2247c4111108888078000780042,0xfa2247c411110888807800080007c,0xfa2247c411110888807800100007e,0xfa2247c411110888807800200007d,0xfa2247c411110888807800400007d,0xfa2247c411110888807f80780007a,0xfa2247c411110888808000780007c,0xfa2247c411110888810000780007b,0xfa2247c4111108888200007800078,0xfa2247c411110888840000780007c,0xfa2247c4111108888787807800078,0xfa2247c41111088887f800780007d,0xfa2247c411110888880000780007c,0xfa2247c41111088f8888807800078,0xfa2247c4111108f8888880780007c,0xfa2247c411110f88888880780007d,0xfa2247c411111000088880780007b,0xfa2247c411179111088880780007a,0xfa2247c411791111088880780007e,0xfa2247c417911111088880780007d,0xfa2247c419999111088880780007b,0xfa2247c420001111088880780007a,0xfa2247c422279111088880780007b,0xfa2247c4227a1111088880780007b,0xfa2247c427a211110888807800078,0xfa2247c42aaa91110888807800079,0xfa2247c433331111088880780007b,0xfa2247c440001111088880780007e]
def a6p76 : Keys := .leaf [
0xfa2247c442001111088880780007a,0xfa2247c4444422279111088880784,0xfa2247c444479111088880780007c,0xfa2247c4447c1111088880780007c,0xfa2247c4447c2222111108888007b,0xfa2247c7c4441111088880780007c,0xfa2247c7c7c41111088880780007d,0xfa2247fc11110888878000780007d,0xfa2247fc1111088887f800780007d,0xfa2247fc22221111088880780007b,0xfa2247fc44441111088880780007c,0xfa2247fc447c1111088880780007c,0xfa2247fc447c2222111108888007b,0xfa2247fc47c41111088880780007d,0xfa224c4411110888878000780007d,0xfa224ccc91110888810000780007e,0xfa224ccc91110888878780780007c,0xfa224ccc9111088887f800780007c,0xfa224ccc9111088f8780007800078,0xfa224ccc91110f88878000780007d,0xfa224ccc91110f88888880780007c,0xfa224ccc99999111078000780007d,0xfa224ccca22211110f8880780007a,0xfa224ccca22791110888878000784,0xfa224ccca7a21111088880780007c,0xfa224cccaaaa91110780007800078,0xfa224cccc44411110f8880780007f,0xfa224cccc7c41111088880780007c,0xfa224cfc91110888878000780007d,0xfa224fcc91110888878000780007d,0xfa224fcc91110f88888880780007d,0xfa224fcca2221111088880780007b]
def a6p77 : Keys := .leaf [
0xfa224fccc4441111088880780007c,0xfa224fccc7c41111088880780007c,0xfa224fcccccc9111088880780007c,0xfa22511144440888878000780007d,0xfa22544411110888878000780007d,0xfa22555511110888810000780007e,0xfa22555511110888850000780007c,0xfa225555111108888787807800078,0xfa2255551111088887f800780007d,0xfa22555511110f88888880780007e,0xfa225555111788888780007800078,0xfa22555519998888878000780007d,0xfa225555222791110888878000786,0xfa22555527a21111088880780007e,0xfa225555333308888780007800078,0xfa22555547c41111088880780007e,0xfa22557d11110888878000780007d,0xfa2257d511110888878000780007d,0xfa2257d547c41111088880780007c,0xfa225ddd91110888878000780007d,0xfa22644411110888878000780007d,0xfa22666647c41111088880780007a,0xfa2267e644441111088880780007e,0xfa2267e647c41111088880780007d,0xfa227800111108888780007c0007b,0xfa22780011110888878400780007a,0xfa2278001111088c878000780007a,0xfa22780011110f888078000780042,0xfa227800111508888780007800078,0xfa227800444411110888810780786,0xfa22780044441111088881780007e,0xfa22780044441111098880780007f]
def a6p78 : Keys := .leaf [
0xfa227800447c1111088887f80007b,0xfa227800447c11110f8880780007f,0xfa227800447c22279111088887803,0xfa227800447c27a2111108888007b,0xfa22780045441111088880780007a,0xfa22780047c411110f8880780007a,0xfa22780047fc1111088880780007a,0xfa2278004ccc91110f8880780007a,0xfa2278004fcc9111088880780007a,0xfa2278004fcc91110f8880780007a,0xfa227800555511110f8880780007a,0xfa227804111108888780007800078,0xfa227807c44411110888878780786,0xfa227807c44411110f8880780007a,0xfa227807c7c41111088880780007a,0xfa22787844441111088887f80007e,0xfa227878444411110f8880780007f,0xfa22787847c41111088880780007f,0xfa227888c44411110f8880780007f,0xfa227888c7c41111088880780007a,0xfa227911088887800078000780040,0xfa22791144440888810000780007e,0xfa227911444408888787807800078,0xfa2279114444088887f800780007d,0xfa22791144440f88878000780007d,0xfa22791144440f88888880780007d,0xfa227911444411110f8880780007f,0xfa227911444422220f8880780007a,0xfa227911447c0888878000780007d,0xfa22791147c40888878000780007d,0xfa22791147c41111088880780007a,0xfa2279114ccc8888878000780007d]
def a6p79 : Keys := .leaf [
0xfa22791155550888878000780007d,0xfa227911780044440f8880780007f,0xfa22c44411110888878000780007c,0xfa23444411110888878000780007c,0xfa261111088887800078000780040,0xfa26444411110888878000780007d,0xfa267804111108888780007800078,0xfa279111088887800078000780040,0xfa27a227911108888780007800040,0xfa27c00411110888878000780007f,0xfa27c004222791110888878000786,0xfa27c44411110888810000780007e,0xfa27c44411110888878000780007d,0xfa27c444111108888780007f80784,0xfa27c44411110888878780780007c,0xfa27c444111108888787878000784,0xfa27c4441111088887f800780007c,0xfa27c4441111088f8888878000784,0xfa27c44411110f88888880780007c,0xfa27c444222211110888878780784,0xfa27c444222791110888810000786,0xfa27c444222791110888878000784,0xfa27c444222791110888878780784,0xfa27c44422279111088887f800784,0xfa27c444222791110f88888880784,0xfa27c444227f91110888878000784,0xfa27c44427a21111088880780007c,0xfa27c44427a222279111088880784,0xfa27c44427a79111088880780007c,0xfa27c44427a791110888878000784,0xfa27c44427a7a2221111088880784,0xfa27c44427a7a2279111088880784]
def a6p80 : Keys := .leaf [
0xfa27c4442aaf91110888878000784,0xfa27c47c11110888878000780007d,0xfa27c47c222211110888878000079,0xfa27c47c222791110888878000079,0xfa27c47c222791110888878000784,0xfa27c47c2227a2221111088887801,0xfa27c47c444422279111088887804,0xfa27c7c411110888878000780007d,0xfa27c7c422221111088880780007b,0xfa27c7c422279111088880780007b,0xfa27c7c444441111088880780007c,0xfa27c7c4444422279111088880784,0xfa27cccc91110888878000780007d,0xfa27cccca22791110888878000784,0xfa27d55511110888878000780007d,0xfa27d555222791110888878000786,0xfa27f800444411110888878780786,0xfa27f800444411110f8880780007f,0xfa27f800444427a79111088880786,0xfa27f800447c22279111088887803,0xfa27f80047c41111088880780007a,0xfa27f807c44411110888878780786,0xfa27f807c44411110f8880780007a,0xfa27f807c7c41111088880780007a,0xfa27f91144440888878000780007d,0xfa27fa22444411110888878780784,0xfa27fa2247c41111088880780007a,0xfa2a444411110888878000780007c,0xfa32444411110888878000780007d,0xfa7a4444222791110888878000784,0xfa7a444427a21111088880780007c,0xfa7a447c222211110888878000079]
def a6p81 : Keys := .leaf [
0xfa7a47c422221111088880780007b,0xfa7a7a2247c41111088880780007a,0xfa7fc444222791110888878000784,0xfaaaf800444411110f8880780007f,0xfaaaf80047c41111088880780007a,0xfaaaf91144440888878000780007d,0xfaaafa2247c41111088880780007b,0xfb22444411110888810000780007e,0xfb22444411110888878000780007c,0xfb22444423221111088880780007e,0xfb331111088887800078000780040,0xfb33444411110888810000780007e,0xfb334444111108888300007800079,0xfb33444411110888878000780007c,0xfb33444411110888878780780007c,0xfb3344441111088887f800780007c,0xfb33444411110f88888880780007c,0xfb33444411790888878000780007d,0xfb33444419998888878000780007d,0xfb334444222791110888878000784,0xfb33444427a21111088880780007c,0xfb33447c11110888878000780007d,0xfb33447c222211110888878000079,0xfb33447c33331111088887800007b,0xfb3347c411110888878000780007d,0xfb3347c422221111088880780007b,0xfb3347c433331111088880780007b,0xfb3347c444441111088880780007c,0xfb334ccc91110888878000780007d,0xfb33555511110888878000780007d,0xfb335555222208888780007800078,0xfb335555333308888780007800078]
def a6p82 : Keys := .leaf [
0xfb33555544440888878000780007d,0xfb337800444411110f8880780007f,0xfb33780047c41111088880780007a,0xfb33780055550888878000780007d,0xfb337911088887800078000780040,0xfb33791144440888810000780007e,0xfb337911444408888300007800078,0xfb33791144440888878000780007d,0xfb337911444408888787807800078,0xfb3379114444088887f800780007d,0xfb33791144440f88878000780007d,0xfb33791144440f88888880780007d,0xfb337911444411110f8880780007f,0xfb337911444422220f8880780007a,0xfb337911447c0888878000780007d,0xfb33791147c40888878000780007d,0xfb33791147c41111088880780007a,0xfb3379114ccc8888878000780007d,0xfb33791155550888878000780007d,0xfb337911780044440f8880780007f,0xfb33797944440888878000780007d,0xfb337999c4440888878000780007d,0xfb337a2247c41111088880780007b,0xfb337a2255550888878000780007d,0xfb37c44411110888878000780007c,0xfb37c444222791110888878000784,0xfb37f91144440888878000780007d,0xfbbbf91144440888878000780007d,0xfc004444222791110888878000784,0xfc00444427a21111088880780007e,0xfc00447c222211110888878000079,0xfc0047c422221111088880780007b]
def a6p83 : Keys := .leaf [
0xfc042222111108888780007800079,0xfc042222111108888787807800079,0xfc44111108888100007800200007b,0xfc44111108888780007800200007d,0xfc441111088887800078002200078,0xfc441111088887800078002780078,0xfc441111088887800078002780205,0xfc44111108888780007800280007d,0xfc44111108888780007800300007f,0xfc44111108888780007f80200007d,0xfc441111088887800220007800078,0xfc44111108888787807800200007d,0xfc441111088887a0007800200007d,0xfc441111088887a0078000780007d,0xfc441111088887f8007800200007d,0xfc441111088887f80220007800078,0xfc44111108a88780007800200007d,0xfc44111108a888888780007800079,0xfc4411110f888888807800200007d,0xfc44113108888780007800200007d,0xfc44113111110888878000780007b,0xfc44202011110888878000780007a,0xfc44222211110888810000780007b,0xfc44222211110888810100780007b,0xfc442222111108888107807800078,0xfc442222111108888107810000783,0xfc44222211110888811000780007e,0xfc44222211110888817800780007d,0xfc44222211110888817801000007b,0xfc442222111108888180007800079,0xfc442222111108888300007800079,0xfc44222211110888850000780007c]
def a6p84 : Keys := .leaf [
0xfc442222111108888780007800078,0xfc4422221111088887800078000f9,0xfc44222211110888878000780017b,0xfc442222111108888780007800279,0xfc442222111108888780007880079,0xfc44222211110888878000790007b,0xfc442222111108888780007c00079,0xfc442222111108888780010780783,0xfc44222211110888878001780007b,0xfc442222111108888780020780781,0xfc442222111108888780047800079,0xfc442222111108888780807800079,0xfc442222111108888781007800079,0xfc442222111108888782007800079,0xfc442222111108888784007800079,0xfc442222111108888787807f80781,0xfc442222111108888788007800079,0xfc442222111108888790007800079,0xfc4422221111088887a0007800079,0xfc4422221111088887c0007800079,0xfc4422221111088887f8007f80079,0xfc4422221111088887ff807800079,0xfc442222111108888807878000781,0xfc442222111108888878078000079,0xfc442222111108898780007800078,0xfc4422221111088c8780007800078,0xfc4422221111088f8780007800008,0xfc44222211110898878000780007d,0xfc442222111108a8878000780007d,0xfc44222211110988810000780007b,0xfc442222111109888780007800078,0xfc442222111109888888807800079]
def a6p85 : Keys := .leaf [
0xfc44222211110a888780007800078,0xfc44222211110f800888807800079,0xfc44222211110f888800007800079,0xfc44222211110f88888f80780007a,0xfc44222211110f8888f880780007f,0xfc44222211110f8f8888807800079,0xfc44222211110ff88888807800079,0xfc442222111188888780007800078,0xfc442222111508888780007800078,0xfc442222111791110888878780783,0xfc44222211190888878000780007d,0xfc44222211310888878000780007d,0xfc44222211790888878000100007e,0xfc44222211791111088887f80007b,0xfc44222217910888810000780007b,0xfc442222191108888780007800078,0xfc44222219998888810000780007b,0xfc442222199991110f8880780007a,0xfc442222911108888780007800078,0xfc442223111108888780007800078,0xfc442226111108888780007800078,0xfc44222791110888810000780007b,0xfc442227911108888780007800040,0xfc442227911108888780007f80784,0xfc442227911108888787807800078,0xfc442227911108888787878000784,0xfc4422279111088887f800780007d,0xfc4422279111088f8888878000784,0xfc44222791110f888888807800078,0xfc442227911791110888878000786,0xfc442227a22211110888878780781,0xfc44222a111108888780007800078]
def a6p86 : Keys := .leaf [
0xfc442232111108888780007800078,0xfc44227a11110888878000200007d,0xfc4422a2111108888780007800078,0xfc44232211110888810000780007b,0xfc442322111108888780007800078,0xfc44232222221111088880780007b,0xfc442622111108888780007800078,0xfc442780222211110888807800079,0xfc4427a2111108888078000780008,0xfc4427a2111108888078000780012,0xfc4427a2111108888078000780020,0xfc4427a2111108888078000780040,0xfc4427a211110888807800080007c,0xfc4427a211110888807800100007e,0xfc4427a211110888807800200007f,0xfc4427a211110888807800400007f,0xfc4427a211110888807f807800078,0xfc4427a2111108888080007800079,0xfc4427a211110888810000780007e,0xfc4427a2111108888200007800078,0xfc4427a211110888840000780007c,0xfc4427a2111108888787807800078,0xfc4427a21111088887f800780007d,0xfc4427a2111108888800007800079,0xfc4427a21111088f8888807800078,0xfc4427a2111108f8888880780007c,0xfc4427a211110f888888807800078,0xfc4427a211111000088880780007e,0xfc4427a211179111088880780007a,0xfc4427a211791111088880780007e,0xfc4427a2179111110888807800078,0xfc4427a2199991110888807800079]
def a6p87 : Keys := .leaf [
0xfc4427a220001111088880780007a,0xfc4427a2222791110888807800079,0xfc4427a2227a11110888807800079,0xfc4427a2240011110888807800078,0xfc4427a7911108888780007800078,0xfc4427a7911108888787807800078,0xfc4427a7a22211110888807800079,0xfc4427a7a22791110888807800079,0xfc4427a7a7a211110888807800078,0xfc4427fa222211110888807800079,0xfc4427fa27a211110888807800078,0xfc442a22111108888780007800078,0xfc442aaa91110888810000780007b,0xfc442aaa911108888787807800078,0xfc442aaa9111088887f8007800079,0xfc442aaa911108f8878000780007d,0xfc442aaa91110f888780007800078,0xfc442aaa91110f888888807800079,0xfc442aaa999991110780007800078,0xfc442aaaa22211110f8880780007a,0xfc442aaaa7a211110888807800079,0xfc442aaf911108888780007800078,0xfc442faa911108888780007800078,0xfc442faa91110f888888807800078,0xfc442faaa22211110888807800079,0xfc442faaa7a211110888807800079,0xfc442faaaaaa91110888807800079,0xfc443111222208888780007800078,0xfc443222111108888780007800078,0xfc44333311110888810000780007b,0xfc443333111108888300007800079,0xfc443333111108888787807800078]
def a6p88 : Keys := .leaf [
0xfc4433331111088887f800780007b,0xfc44333311110f88888880780007b,0xfc44333311790888878000780007d,0xfc443333199988888780007800078,0xfc44333327a21111088880780007b,0xfc443337911108888780007800078,0xfc4437b3111108888780007800078,0xfc4437b327a211110888807800079,0xfc443bbb911108888780007800078,0xfc44400027a21111088880780007e,0xfc444078222211110888878000079,0xfc44444411110888878000780027c,0xfc4444441111088887a000780007e,0xfc444444111108a8878000780007d,0xfc44444411310888878000780007d,0xfc444444222211110888810780786,0xfc44444422221111088881780007b,0xfc44444422221111098880780007f,0xfc444444222791110888810000786,0xfc444444222791110888878780786,0xfc44444422279111088887f800786,0xfc444444222791110f88888880784,0xfc44444423221111088880780007e,0xfc44444427a222279111088880786,0xfc44444427a79111088880780007e,0xfc44444427a7a2279111088880786,0xfc4444442aaa91110f8880780007f,0xfc4444442faa9111088880780007e,0xfc444447a22791110888878000784,0xfc444447a7a21111088880780007e,0xfc44447c11110888878000200007d,0xfc44447c22221111088881000007b]
def a6p89 : Keys := .leaf [
0xfc44447c222211110888878780079,0xfc44447c22221111088887f800079,0xfc44447c222211110f88888880079,0xfc44447c222791110888878000079,0xfc44447c222791110888878000784,0xfc44447c2227a2221111088887801,0xfc44447c27a21111088880780007e,0xfc44447c27a222221111088880079,0xfc44447c2aaa91110888878000079,0xfc44447c33331111088887800007b,0xfc44447c444422279111088887804,0xfc44454422221111088880780007b,0xfc444780222211110888807800079,0xfc4447c411110888807800200007d,0xfc4447c4222791110888807800079,0xfc4447c4222791110888878000784,0xfc4447c42227a2221111088880781,0xfc4447c427a21111088880780007c,0xfc4447c42aaa91110888807800079,0xfc4447c433331111088880780007b,0xfc4447c4444422279111088880784,0xfc4447c4447c22221111088880079,0xfc4447c7a2221111088880780007b,0xfc4447fc22221111088880780007b,0xfc4447fc447c2222111108888007b,0xfc444ccca22791110888878000784,0xfc444ccca7a21111088880780007c,0xfc444cccaaaa9111078000780007d,0xfc444fcca2221111088880780007b,0xfc445111222208888780007800078,0xfc445555222791110888878000786,0xfc44555527a21111088880780007e]
def a6p90 : Keys := .leaf [
0xfc44555533330888878000780007d,0xfc446222111108888780007800078,0xfc44666627a211110888807800078,0xfc4467e622221111088880780007b,0xfc4467e627a211110888807800078,0xfc44780011110888878000780027e,0xfc4478001111088887a000780007f,0xfc447800111108a8878000780007f,0xfc44780011110f88807800200007f,0xfc44780011310888878000780007d,0xfc447800222211110888810780783,0xfc44780022221111088881780007b,0xfc44780022221111098880780007a,0xfc447800222791110888878780786,0xfc447800222791110f8880780007a,0xfc44780023221111088880780007f,0xfc44780027a211110f8880780007f,0xfc44780027a79111088880780007f,0xfc4478002aaa91110f8880780007f,0xfc4478002faa9111088880780007f,0xfc4478002faa91110f8880780007f,0xfc447800333311110f8880780007f,0xfc447800447c22279111088887806,0xfc44780047c422279111088880786,0xfc447807a22211110888878780783,0xfc447807a22211110f8880780007a,0xfc447807a7a21111088880780007a,0xfc44782011110888878000780007d,0xfc44787822221111088887f80007b,0xfc447878222211110f8880780007f,0xfc44787827a21111088880780007f,0xfc447888a22211110f8880780007a]
def a6p91 : Keys := .leaf [
0xfc447888a7a21111088880780007f,0xfc44791108888780007800200007d,0xfc44791122220888810000780007b,0xfc447911222208888787807800078,0xfc4479112222088887f800780007d,0xfc44791122220f888780007800078,0xfc44791122220f888888807800078,0xfc447911222211110f8880780007a,0xfc447911222788888780007800078,0xfc44791127a208888780007800078,0xfc44791127a21111088880780007f,0xfc4479112aaa88888780007800078,0xfc447911333308888780007800078,0xfc447911444422220f8880780007f,0xfc447911780022220f8880780007a,0xfc447a2211110888810000780007b,0xfc447a22111108888787807800078,0xfc447a221111088887f800780007d,0xfc447a2211110f888780007800078,0xfc447a2211110f888888807800078,0xfc447a22222211110f8880780007a,0xfc447a2227a21111088880780007a,0xfc447a22444411110f8880780007f,0xfc447a2247c41111088880780007e,0xfc447a22780011110f8880780007a,0xfc447a22791108888780007800078,0xfc447a2791110888878000780007d,0xfc447aaa91110888878000780007d,0xfc447b3311110888878000780007d,0xfc447b3379110888878000780007d,0xfc44a222111108888780007800078,0xfc452222111108888780007800078]
def a6p92 : Keys := .leaf [
0xfc47c444222791110888878000784,0xfc47c44427a21111088880780007e,0xfc47c47c222211110888878000079,0xfc47c7c4222211110888807800079,0xfc47fc4427a21111088880780007f,0xfc4c2222111108888780007800079,0xfc542222111108888780007800078,0xfc64111108888780007800200007d,0xfc642222111108888780007800078,0xfc64782011110888878000780007d,0xfc7c111108888780007800200007d,0xfc7c202011110888878000780007a,0xfc7c222211110888810000780007b,0xfc7c2222111108888780007800078,0xfc7c2222111108888780007f80079,0xfc7c2222111108888787807800079,0xfc7c22221111088887f8007800079,0xfc7c22221111088887f8078000079,0xfc7c2222111108f88888878000079,0xfc7c222211110f888888807800079,0xfc7c2227911108888780007800078,0xfc7c27a2111108888780007800078,0xfc7c27a2222211110888807800079,0xfc7c2aaa911108888780007800078,0xfc7c3333111108888780007800078,0xfc7c444422221111088887f800079,0xfc7c4444222791110888878000784,0xfc7c444427a21111088880780007e,0xfc7c447c11110888878000200007d,0xfc7c447c20201111088887800007b,0xfc7c447c22221111088881000007b,0xfc7c447c222211110888878000079]
def a6p93 : Keys := .leaf [
0xfc7c447c222211110888878780079,0xfc7c447c22221111088887f800079,0xfc7c447c222211110f88888880079,0xfc7c447c222791110888878000079,0xfc7c447c222791110888878000784,0xfc7c447c2227a2221111088887801,0xfc7c447c27a21111088880780007e,0xfc7c447c27a222221111088880079,0xfc7c447c2aaa91110888878000079,0xfc7c447c33331111088887800007b,0xfc7c447c444422279111088887804,0xfc7c447fa22211110888878000079,0xfc7c47c4222211110888807800079,0xfc7c47c4447c22221111088880079,0xfc7c47fc222211110888807800079,0xfc7c47fc222211110888878000079,0xfc7c47fc444422221111088880079,0xfc7c47fc447c22221111088880079,0xfc7c4cfca22211110888878000079,0xfc7c780022221111088887f80007b,0xfc7c7800222211110f8880780007a,0xfc7c780027a21111088880780007f,0xfc7c7800447c22279111088887806,0xfc7c780047fc2222111108888007b,0xfc7c787822221111088887f80007b,0xfc7c7878222211110f8880780007f,0xfc7c787827a21111088880780007f,0xfc7c7911222208888780007800078,0xfc7c7a22111108888780007800078,0xfc7c7c4422221111088887f800079,0xfc7c7c4427a21111088880780007f,0xfc7fc47c222211110888878000079]
def a6p94 : Keys := .leaf [
0xfcccf800222211110f8880780007a,0xfcccf80027a21111088880780007f,0xfcccf911222208888780007800078,0xfcccfa22111108888780007800078,0xfcccfc4427a21111088880780007e,0xfd44222211110888810000780007b,0xfd442222111108888780007800079,0xfd44454422221111088880780007b,0xfd55111108888780007800200007d,0xfd55222211110888810000780007b,0xfd55222211110888850000780007c,0xfd552222111108888780007800079,0xfd552222111108888787807800079,0xfd5522221111088887f8007800079,0xfd55222211110f888888807800079,0xfd552222111788888780007800078,0xfd552222199988888780007800078,0xfd552227911108888780007800078,0xfd5527a2111108888780007800078,0xfd5527a2222211110888807800079,0xfd552aaa911108888780007800078,0xfd553333111108888780007800078,0xfd553333222208888780007800078,0xfd554444222791110888878000784,0xfd55444427a21111088880780007e,0xfd55444433330888878000780007d,0xfd55447c222211110888878000079,0xfd5547c4222211110888807800079,0xfd555555222791110888878000786,0xfd55555527a21111088880780007e,0xfd55555533330888878000780007d,0xfd557800222211110f8880780007a]
def a6p95 : Keys := .leaf [
0xfd55780027a21111088880780007f,0xfd557800333308888780007800078,0xfd55791108888780007800200007d,0xfd55791122220888810000780007b,0xfd55791122220888850000780007d,0xfd557911222208888780007800078,0xfd557911222208888787807800078,0xfd5579112222088887f800780007d,0xfd55791122220f888780007800078,0xfd55791122220f888888807800078,0xfd557911222211110f8880780007a,0xfd557911222788888780007800078,0xfd55791127a208888780007800078,0xfd55791127a21111088880780007f,0xfd5579112aaa88888780007800078,0xfd557911333308888780007800078,0xfd557911444422220f8880780007f,0xfd557911780022220f8880780007a,0xfd557917a22208888780007800078,0xfd557999a22208888780007800078,0xfd557a22111108888780007800078,0xfd557a22791108888780007800078,0xfd557b33111108888780007800078,0xfd557b33222208888780007800078,0xfd557b3344440888878000780007d,0xfd557b33780008888780007800078,0xfd557b33791108888780007800078,0xfd557c4427a21111088880780007e,0xfd557c44333308888780007800078,0xfd7d2222111108888780007800078,0xfd7d447c222211110888878000079,0xfd7d7911222208888780007800078]
def a6p96 : Keys := .leaf [
0xfdddf911222208888780007800078,0xfe22444411110888878000780007c,0xfe442222111108888780007800078,0xfe664444222791110888878000784,0xfe66444427a21111088880780007c,0xfe66447c222211110888878000079,0xfe6647c4222211110888807800079,0xfe667a2247c41111088880780007a,0xfe667c4427a21111088880780007f,0xfe67c444222791110888878000784,0xfe7e447c222211110888878000079,0xff807800447c22279111088887801,0xff807911444422220f88807800078,0xff807a2247c41111088880780007b,0xff807c4427a211110888807800079,0xff88f911444422220f88807800078,0xff917911444422220f8880780007a,0xff99f911444422220f88807800078,0xffa27800444411110f8880780007f,0xffa2780047c41111088880780007f,0xffa2791144440888878000780007d,0xffa27a2247c41111088880780007b,0xffa27c4411110888878000780007d,0xffa27c4427a211110888807800079,0xffaaf800444411110f8880780007f,0xffb3791144440888878000780007d,0xffc47800222211110f8880780007a,0xffc4780027a21111088880780007a,0xffc47911222208888780007800078,0xffc47a22111108888780007800078,0xffc47a2247c41111088880780007c,0xffc47c4427a21111088880780007e]
def a6p97 : Keys := .leaf [
0xffccf800222211110f8880780007a,0xffd57911222208888780007800078,0xffe67a2247c41111088880780007a,0xffe67c4427a211110888807800078]
def a6 : Keys := .branch 0x1f00f88884f442222111100ff00f0 (.branch 0x1f0008888444f222211110ff000ff (.branch 0x190008888444422221f1100f0000f (.branch 0x18888444422221f00111110f0000f (.branch 0x1f2228f884f44111100f0000f (.branch 0x1f0008888444f2222111102f0 (a6p0) (.branch 0x1f00f88f84444222211110f0f (a6p1) (a6p2))) (.branch 0x1f888222211110f0000f0004f (a6p3) (.branch 0x14444322211110f0000f0000f0008 (a6p4) (a6p5)))) (.branch 0x18888544f4444222211110f0000f0 (.branch 0x18888444f222211111000020000f0 (a6p6) (.branch 0x188884f44322211110f0000f0000f (a6p7) (a6p8))) (.branch 0x188f844442222111110010f00000f (a6p9) (.branch 0x18f88444422221111100000f0000f (a6p10) (a6p11))))) (.branch 0x1f0004f442222111100f00088000f (.branch 0x1f0004444222211110f0000f8000f (.branch 0x198894444222211110f0000f0000f (a6p12) (.branch 0x1aaaa4444322211110f0000f0000f (a6p13) (a6p14))) (.branch 0x1f000444422221f1100f00088000f (a6p15) (.branch 0x1f000444c22221f1100f0000f0008 (a6p16) (a6p17)))) (.branch 0x1f0008888226211110f0000f0000f (.branch 0x1f0006666222211110f0000f8000f (a6p18) (.branch 0x1f0008888222211110ff0044f00f0 (a6p19) (a6p20))) (.branch 0x1f0008888444422221f1100f0000f (a6p21) (.branch 0x1f000888844442f22111102f0000f (a6p22) (a6p23)))))) (.branch 0x1f0008a8846442222111100f0000f (.branch 0x1f00088f82262222211110f00000f (.branch 0x1f00088884f4f444f2222111100f0 (.branch 0x1f00088884454222211f10f00000f (a6p24) (.branch 0x1f00088884f442222111100f0002f (a6p25) (a6p26))) (.branch 0x1f000888866662222111102f0000f (a6p27) (.branch 0x1f00088a8444f222211110f0000f0 (a6p28) (a6p29)))) (.branch 0x1f00088f8444f4444222211110f0f (.branch 0x1f00088f84444222211310f00000f (a6p30) (.branch 0x1f00088f8444f222211110f000004 (a6p31) (a6p32))) (.branch 0x1f00088f85555222211110200000f (a6p33) (.branch 0x1f00088f88000444f222211110f00 (a6p34) (a6p35))))) (.branch 0x1f000999988885f55222200f0000f (.branch 0x1f0008f88666f2222111100f0000f (.branch 0x1f0008f88222211110f4000f0000f (a6p36) (.branch 0x1f0008f8844442232111100f0000f (a6p37) (a6p38))) (.branch 0x1f0008ff84f442222111100f0000f (a6p39) (.branch 0x1f0009999444f222211110ff000f0 (a6p40) (a6p41)))) (.branch 0x1f000aaaa666644441f1100f0000f (.branch 0x1f0009f995f552222111100f0000f (a6p42) (.branch 0x1f000aaaa444422221b1100f0000f (a6p43) (a6p44))) (.branch 0x1f0084444222211110f0f00f0000f (.branch 0x1f000cccc88f8444f222211110f00 (a6p45) (a6p46)) (.branch 0x1f00f444f222211110f0000f00008 (a6p47) (a6p48))))))) (.branch 0x1f4448888222311110f0000f0000f (.branch 0x1f222888844441f11111f00f0000f (.branch 0x1f0f088f84f44222211110f00000f (.branch 0x1f0408888226211110f0000f0000f (.branch 0x1f00f88f84f44444422221111000f (a6p49) (.branch 0x1f00faaaa444422221f1100f0000f (a6p50) (a6p51))) (.branch 0x1f0f0444422221f1100f0000f0008 (a6p52) (.branch 0x1f0f08888444f22221f1100f0000f (a6p53) (a6p54)))) (.branch 0x1f2224444222a11110f0000f0000f (.branch 0x1f0f09f9944442222111100f0000f (a6p55) (.branch 0x1f2008888444f22221111020000f0 (a6p56) (a6p57))) (.branch 0x1f2228888404011110f0000f0000f (a6p58) (.branch 0x1f2228888444411110fff00f0000f (a6p59) (a6p60))))) (.branch 0x1f2229999555522220f0000f0000f (.branch 0x1f2228889444411110f0000f0000f (.branch 0x1f2228888444f222211110f0f00f0 (a6p61) (.branch 0x1f22288884f4f2222111100f0000f (a6p62) (a6p63))) (.branch 0x1f22288f844f4444411110f00000f (a6p64) (.branch 0x1f2228f884f4411110f0000f0000f (a6p65) (a6p66)))) (.branch 0x1f2628888444411110f0000f0000f (.branch 0x1f222aafa444411110f0000f0000f (a6p67) (.branch 0x1f222f0009f9944441f1100f0000f (a6p68) (a6p69))) (.branch 0x1f444222211110f0f00f0000f0008 (a6p70) (.branch 0x1f4448888222211110f00020f00f0 (a6p71) (a6p72)))))) (.branch 0x1f8884444222215110f0000f0000f (.branch 0x1f444f222aaaa11110f0000f0000f (.branch 0x1f4448f8884002222111100f0000f (.branch 0x1f44488c8222211110f0000f0000f (a6p73) (.branch 0x1f4448f0088882222111100f0000f (a6p74) (a6p75))) (.branch 0x1f4449f9988882222111100f0000f (a6p76) (.branch 0x1f444f00088f8222211110ff0000f (a6p77) (a6p78)))) (.branch 0x1f666aaaa888811110f0000f0000f (.branch 0x1f44f8888555f222211110f0000f0 (a6p79) (.branch 0x1f4f48f8844442222111100f0000f (a6p80) (a6p81))) (.branch 0x1f8084444222211110f0000f0000f (a6p82) (.branch 0x1f8884444222211110f0000f0000f (a6p83) (a6p84))))) (.branch 0x1f888f1114f442222111100f0000f (.branch 0x1f8886666222211110ff000f0000f (.branch 0x1f8884464222211110f0000f0000f (a6p85) (.branch 0x1f8884f4440002222111100f0000f (a6p86) (a6p87))) (.branch 0x1f88888f84444222211110f0f000f (a6p88) (.branch 0x1f888aaaa666611110f0000f0000f (a6p89) (a6p90)))) (.branch 0x1f999f000444422221f1100f0000f (.branch 0x1f88f8888444f222211110f0000f0 (a6p91) (.branch 0x1f8f888f84444222211110f0f000f (a6p92) (a6p93))) (.branch 0x1fbbbf222444411110f0000f0000f (.branch 0x1faaaf0004f442222111100f0000f (a6p94) (a6p95)) (.branch 0x1ff99f000444422221f1100f0000f (a6p96) (a6p97)))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p0 : r6p0.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p1 : r6p1.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p2 : r6p2.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p3 : r6p3.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p4 : r6p4.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p5 : r6p5.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p6 : r6p6.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p7 : r6p7.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p8 : r6p8.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p9 : r6p9.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p10 : r6p10.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p11 : r6p11.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p12 : r6p12.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p13 : r6p13.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p14 : r6p14.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p15 : r6p15.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p16 : r6p16.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p17 : r6p17.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p18 : r6p18.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p19 : r6p19.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p20 : r6p20.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p21 : r6p21.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p22 : r6p22.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p23 : r6p23.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p24 : r6p24.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p25 : r6p25.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p26 : r6p26.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p27 : r6p27.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p28 : r6p28.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p29 : r6p29.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p30 : r6p30.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p31 : r6p31.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p32 : r6p32.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p33 : r6p33.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p34 : r6p34.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p35 : r6p35.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p36 : r6p36.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p37 : r6p37.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p38 : r6p38.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p39 : r6p39.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p40 : r6p40.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p41 : r6p41.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p42 : r6p42.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p43 : r6p43.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p44 : r6p44.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p45 : r6p45.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p46 : r6p46.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p47 : r6p47.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p48 : r6p48.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p49 : r6p49.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p50 : r6p50.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p51 : r6p51.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p52 : r6p52.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p53 : r6p53.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p54 : r6p54.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p55 : r6p55.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p56 : r6p56.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p57 : r6p57.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p58 : r6p58.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p59 : r6p59.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p60 : r6p60.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p61 : r6p61.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p62 : r6p62.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p63 : r6p63.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p64 : r6p64.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p65 : r6p65.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p66 : r6p66.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p67 : r6p67.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p68 : r6p68.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p69 : r6p69.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p70 : r6p70.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p71 : r6p71.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p72 : r6p72.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p73 : r6p73.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p74 : r6p74.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p75 : r6p75.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p76 : r6p76.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p77 : r6p77.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p78 : r6p78.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p79 : r6p79.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p80 : r6p80.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p81 : r6p81.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p82 : r6p82.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p83 : r6p83.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p84 : r6p84.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p85 : r6p85.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p86 : r6p86.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p87 : r6p87.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p88 : r6p88.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p89 : r6p89.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p90 : r6p90.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p91 : r6p91.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p92 : r6p92.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p93 : r6p93.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p94 : r6p94.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p95 : r6p95.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p96 : r6p96.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p97 : r6p97.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p98 : r6p98.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p99 : r6p99.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p100 : r6p100.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p101 : r6p101.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p102 : r6p102.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p103 : r6p103.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p104 : r6p104.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p105 : r6p105.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p106 : r6p106.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p107 : r6p107.all (checkFast 5 a5) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr6p108 : r6p108.all (checkFast 5 a5) = true := by
  decide +kernel

lemma badR6 : Rejects 6 r6 :=
  verifyFast 5 a5 r6 badA5 (by
    unfold r6
    simp only [allBranch, Bool.and_true, goodr6p0, goodr6p1, goodr6p2, goodr6p3, goodr6p4, goodr6p5, goodr6p6, goodr6p7, goodr6p8, goodr6p9, goodr6p10, goodr6p11, goodr6p12, goodr6p13, goodr6p14, goodr6p15, goodr6p16, goodr6p17, goodr6p18, goodr6p19, goodr6p20, goodr6p21, goodr6p22, goodr6p23, goodr6p24, goodr6p25, goodr6p26, goodr6p27, goodr6p28, goodr6p29, goodr6p30, goodr6p31, goodr6p32, goodr6p33, goodr6p34, goodr6p35, goodr6p36, goodr6p37, goodr6p38, goodr6p39, goodr6p40, goodr6p41, goodr6p42, goodr6p43, goodr6p44, goodr6p45, goodr6p46, goodr6p47, goodr6p48, goodr6p49, goodr6p50, goodr6p51, goodr6p52, goodr6p53, goodr6p54, goodr6p55, goodr6p56, goodr6p57, goodr6p58, goodr6p59, goodr6p60, goodr6p61, goodr6p62, goodr6p63, goodr6p64, goodr6p65, goodr6p66, goodr6p67, goodr6p68, goodr6p69, goodr6p70, goodr6p71, goodr6p72, goodr6p73, goodr6p74, goodr6p75, goodr6p76, goodr6p77, goodr6p78, goodr6p79, goodr6p80, goodr6p81, goodr6p82, goodr6p83, goodr6p84, goodr6p85, goodr6p86, goodr6p87, goodr6p88, goodr6p89, goodr6p90, goodr6p91, goodr6p92, goodr6p93, goodr6p94, goodr6p95, goodr6p96, goodr6p97, goodr6p98, goodr6p99, goodr6p100, goodr6p101, goodr6p102, goodr6p103, goodr6p104, goodr6p105, goodr6p106, goodr6p107, goodr6p108])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p0 : a6p0.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p1 : a6p1.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p2 : a6p2.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p3 : a6p3.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p4 : a6p4.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p5 : a6p5.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p6 : a6p6.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p7 : a6p7.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p8 : a6p8.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p9 : a6p9.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p10 : a6p10.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p11 : a6p11.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p12 : a6p12.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p13 : a6p13.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p14 : a6p14.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p15 : a6p15.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p16 : a6p16.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p17 : a6p17.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p18 : a6p18.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p19 : a6p19.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p20 : a6p20.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p21 : a6p21.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p22 : a6p22.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p23 : a6p23.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p24 : a6p24.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p25 : a6p25.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p26 : a6p26.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p27 : a6p27.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p28 : a6p28.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p29 : a6p29.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p30 : a6p30.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p31 : a6p31.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p32 : a6p32.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p33 : a6p33.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p34 : a6p34.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p35 : a6p35.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p36 : a6p36.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p37 : a6p37.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p38 : a6p38.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p39 : a6p39.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p40 : a6p40.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p41 : a6p41.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p42 : a6p42.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p43 : a6p43.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p44 : a6p44.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p45 : a6p45.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p46 : a6p46.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p47 : a6p47.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p48 : a6p48.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p49 : a6p49.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p50 : a6p50.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p51 : a6p51.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p52 : a6p52.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p53 : a6p53.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p54 : a6p54.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p55 : a6p55.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p56 : a6p56.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p57 : a6p57.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p58 : a6p58.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p59 : a6p59.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p60 : a6p60.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p61 : a6p61.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p62 : a6p62.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p63 : a6p63.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p64 : a6p64.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p65 : a6p65.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p66 : a6p66.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p67 : a6p67.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p68 : a6p68.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p69 : a6p69.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p70 : a6p70.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p71 : a6p71.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p72 : a6p72.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p73 : a6p73.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p74 : a6p74.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p75 : a6p75.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p76 : a6p76.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p77 : a6p77.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p78 : a6p78.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p79 : a6p79.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p80 : a6p80.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p81 : a6p81.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p82 : a6p82.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p83 : a6p83.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p84 : a6p84.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p85 : a6p85.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p86 : a6p86.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p87 : a6p87.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p88 : a6p88.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p89 : a6p89.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p90 : a6p90.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p91 : a6p91.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p92 : a6p92.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p93 : a6p93.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p94 : a6p94.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p95 : a6p95.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p96 : a6p96.all (checkAlias r6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda6p97 : a6p97.all (checkAlias r6) = true := by
  decide +kernel

lemma badA6 : RejectsAlias 6 a6 :=
  verifyAliases 6 r6 a6 badR6 (by
    unfold a6
    simp only [allBranch, Bool.and_true, gooda6p0, gooda6p1, gooda6p2, gooda6p3, gooda6p4, gooda6p5, gooda6p6, gooda6p7, gooda6p8, gooda6p9, gooda6p10, gooda6p11, gooda6p12, gooda6p13, gooda6p14, gooda6p15, gooda6p16, gooda6p17, gooda6p18, gooda6p19, gooda6p20, gooda6p21, gooda6p22, gooda6p23, gooda6p24, gooda6p25, gooda6p26, gooda6p27, gooda6p28, gooda6p29, gooda6p30, gooda6p31, gooda6p32, gooda6p33, gooda6p34, gooda6p35, gooda6p36, gooda6p37, gooda6p38, gooda6p39, gooda6p40, gooda6p41, gooda6p42, gooda6p43, gooda6p44, gooda6p45, gooda6p46, gooda6p47, gooda6p48, gooda6p49, gooda6p50, gooda6p51, gooda6p52, gooda6p53, gooda6p54, gooda6p55, gooda6p56, gooda6p57, gooda6p58, gooda6p59, gooda6p60, gooda6p61, gooda6p62, gooda6p63, gooda6p64, gooda6p65, gooda6p66, gooda6p67, gooda6p68, gooda6p69, gooda6p70, gooda6p71, gooda6p72, gooda6p73, gooda6p74, gooda6p75, gooda6p76, gooda6p77, gooda6p78, gooda6p79, gooda6p80, gooda6p81, gooda6p82, gooda6p83, gooda6p84, gooda6p85, gooda6p86, gooda6p87, gooda6p88, gooda6p89, gooda6p90, gooda6p91, gooda6p92, gooda6p93, gooda6p94, gooda6p95, gooda6p96, gooda6p97])
def r7p0 : Keys := .leaf [
0x1f222888844441f1100f0000f,0x1f8884f442222111100f0000f,0x188884444322211110f0000f0000f,0x198884444222211110f0000f0000f]
def r7p1 : Keys := .leaf [
0x1f0004444222a11110f0000f0000f,0x1f000444f222211110f0000f00008,0x1f000aaaa666611110f0000f0000f,0x1f222444411110f0000f0000f0008]
def r7p2 : Keys := .leaf [
0x1f2228888444411110f0f00f0000f,0x1f222888844441f110f0000f0000f,0x1f222888844441f11111100f0000f,0x1f22288f8444411110f0000f0000f]
def r7p3 : Keys := .leaf [
0x1f2228f88444411110f0000f0000f,0x1f2229999444411110f0000f0000f,0x1f222aaaa444411110f0000f0000f,0x1f444222211110f0000f0000f0008]
def r7p4 : Keys := .leaf [
0x1f888444f222211110f0000f0000f,0x1f8884f44222211110f0000f0000f,0x1f8885555222211110f0000f0000f,0x1f8886666222211110f0000f0000f]
def r7p5 : Keys := .leaf [
0x1f888f222444411110f0000f0000f,0x1f888f444222211110f0000f0000f,0x1f8f84444222211110f0000f0000f,0x1faaaf222444411110f0000f0000f]
def r7p6 : Keys := .leaf [
0x1f000222211110f0000f00040000f0008,0x1f000444422221111020000f0000f0008,0x1f0004444222211110f0000f0000f0008,0x1f0004444222211110f0000f0000f0009]
def r7p7 : Keys := .leaf [
0x1f0004444222211110f0000f8000f0008,0x1f0004444222211110f0000ff00f00008,0x1f0004444222211110f080f0000f0000f,0x1f0004444222a11110f0000f0000f0008]
def r7p8 : Keys := .leaf [
0x1f000444c222211110f0000f0000f0008,0x1f000444f222211110f0000f0000f0008,0x1f000444f4444222211110f0000f00008,0x1f0004f44222211110f0000f0000f0008]
def r7p9 : Keys := .leaf [
0x1f0005555222211110f0000f0000f0008,0x1f0008888222211110f0000f00044000f,0x1f0008888222211110f0000f0004f000f,0x1f0008888222211110f00044000f0000f]
def r7p10 : Keys := .leaf [
0x1f0008888222211110ff0044000f0000f,0x1f0008888444422221111020f00f0000f,0x1f000888844442222111f0f0000f00001,0x1f0008888444422221f1100f0000f0001]
def r7p11 : Keys := .leaf [
0x1f0008888444422221f11040000f0000f,0x1f00088884444222311110f0000f0000f,0x1f00088884444222a11110f0000f0000f,0x1f00088884444322211110f0000f0000f]
def r7p12 : Keys := .leaf [
0x1f0008888444f222211110f0000f00004,0x1f0008888444f222211110f0000f00008,0x1f00088884f442222111100f0000f0001,0x1f00088884f4422221111040000f0000f]
def r7p13 : Keys := .leaf [
0x1f00088886222444411110f0000f0000f,0x1f000888f4444222211110f0000f00008,0x1f00088f84444222211110f00000f0004,0x1f00088f84444222211110f00000f0008]
def r7p14 : Keys := .leaf [
0x1f00088f8444f222211110f0000f0000f,0x1f0008f88444f222211110f0000f0000f,0x1f0008f884f44222211110f0000f0000f,0x1f0009999444f222211110f0000f0000f]
def r7p15 : Keys := .leaf [
0x1f00099994f44222211110f0000f0000f,0x1f00099995555222211110f0000f0000f,0x1f000aaaa4444222f11110f0000f0000f,0x1f000aaaa4444333311110f0000f0000f]
def r7p16 : Keys := .leaf [
0x1f000aaaa4f44222211110f0000f0000f,0x1f000aaaa5555222211110f0000f0000f,0x1f000aaaa6666444411110f0000f0000f,0x1f00188884444222211110f0000f0000f]
def r7p17 : Keys := .leaf [
0x1f00288884444222211110f0000f0000f,0x1f00488884444222211110f0000f0000f,0x1f0084444222211110f0000f0000f0008,0x1f00888884444222211110f0000f0000f]
def r7p18 : Keys := .leaf [
0x1f00f4444222211110f0000f0000f0008,0x1f00f8888444422221f110f0000f0000f,0x1f00f88f84444222211110f0000f0000f,0x1f00f8f884444222211110f0000f0000f]
def r7p19 : Keys := .leaf [
0x1f00f99994444222211110f0000f0000f,0x1f0f04444222211110f0000f0000f0008,0x1f0f088f84444222211110f0000f0000f,0x1f0f08f884444222211110f0000f0000f]
def r7p20 : Keys := .leaf [
0x1f0f099994444222211110f0000f0000f,0x1f0f0aaaa4444222211110f0000f0000f,0x1f0ff88884444222211110f0000f0000f,0x1f20088884444222211110f0000f0000f]
def r7p21 : Keys := .leaf [
0x1f2224444222211110f0000f0000f0008,0x1f2228888444411110f0000f0000f0001,0x1f2228888444411110f0000f0000f0004,0x1f2228888444411110f0000f0000f0008]
def r7p22 : Keys := .leaf [
0x1f2228888444411110f0000ff00f0000f,0x1f2228888444411110f00040000f0000f,0x1f2228888444411110f0f0f0000f0000f,0x1f22288884444111f11110f0000f0000f]
def r7p23 : Keys := .leaf [
0x1f222888844441f1111110f0000f0000f,0x1f2228888444422221f110f0000f0000f,0x1f22288884444222f11110f0000f0000f,0x1f222888844442f2211110f0000f0000f]
def r7p24 : Keys := .leaf [
0x1f22288884444333311110f0000f0000f,0x1f2228888444f444411110f0000f0000f,0x1f222888844f4444411110f0000f0000f,0x1f22288884f44444411110f0000f0000f]
def r7p25 : Keys := .leaf [
0x1f22288885555444411110f0000f0000f,0x1f22288886666444411110f0000f0000f,0x1f22288f84444222211110f0000f0000f,0x1f222cccc8888444411110f0000f0000f]
def r7p26 : Keys := .leaf [
0x1f222f000444411110f0000f0000f0008,0x1f222f000888844441f110f0000f0000f,0x1f222f00088f8444411110f0000f0000f,0x1f222f0008f88444411110f0000f0000f]
def r7p27 : Keys := .leaf [
0x1f222f0009999444411110f0000f0000f,0x1f222f000aaaa444411110f0000f0000f,0x1f222f00f8888444411110f0000f0000f,0x1f222f1118888444411110f0000f0000f]
def r7p28 : Keys := .leaf [
0x1f22f88884444222211110f0000f0000f,0x1f22ff2228888444411110f0000f0000f,0x1f333f2228888444411110f0000f0000f,0x1f40088884444222211110f0000f0000f]
def r7p29 : Keys := .leaf [
0x1f4444444222211110f0000f0000f0008,0x1f4448888222211110f0000f0000f0001,0x1f4448888222211110f0000f0000f0004,0x1f4448888222211110f0000f0000f0008]
def r7p30 : Keys := .leaf [
0x1f4448888222211110f00040000f0000f,0x1f4448888222211110f0f0f0000f0000f,0x1f44488882222111f11110f0000f0000f,0x1f4448888222f222211110f0000f0000f]
def r7p31 : Keys := .leaf [
0x1f44488f84444222211110f0000f0000f,0x1f4448f884444222211110f0000f0000f,0x1f444f2228888444411110f0000f0000f,0x1f44f88884444222211110f0000f0000f]
def r7p32 : Keys := .leaf [
0x1f4f488884444222211110f0000f0000f,0x1f66688884444222211110f0000f0000f,0x1f666f2228888444411110f0000f0000f,0x1f8884444222211110f0000f0000f0001]
def r7p33 : Keys := .leaf [
0x1f8884444222211110f0000f0000f0004,0x1f8884444222211110f0000f0000f0008,0x1f8884444222211110f0000ff00f0000f,0x1f8884444222211110f00040000f0000f]
def r7p34 : Keys := .leaf [
0x1f8884444222211110f0f0f0000f0000f,0x1f88844442222111f11110f0000f0000f,0x1f888444422221f1111110f0000f0000f,0x1f88844442f22222211110f0000f0000f]
def r7p35 : Keys := .leaf [
0x1f8884f444444222211110f0000f0000f,0x1f888888f4444222211110f0000f0000f,0x1f88888f84444222211110f0000f0000f,0x1f8888f884444222211110f0000f0000f]
def r7p36 : Keys := .leaf [
0x1f88899994444222211110f0000f0000f,0x1f888aaaa4444222211110f0000f0000f,0x1f888cccc4444222211110f0000f0000f,0x1f888f0004f44222211110f0000f0000f]
def r7p37 : Keys := .leaf [
0x1f888f222f000444411110f0000f0000f,0x1f88ff8884444222211110f0000f0000f,0x1f8f888f84444222211110f0000f0000f,0x1f8f8f8884444222211110f0000f0000f]
def r7p38 : Keys := .leaf [
0x1faaaaaaa4444222211110f0000f0000f,0x1faaaf222f000444411110f0000f0000f,0x1fccc88884444222211110f0000f0000f,0x1fcccf8884444222211110f0000f0000f]
def r7p39 : Keys := .leaf [
0x1ff00f2228888444411110f0000f0000f,0x1ff22f2228888444411110f0000f0000f]
def r7 : Keys := .branch 0x1f0f099994444222211110f0000f0000f (.branch 0x1f0008888222211110ff0044000f0000f (.branch 0x1f888f222444411110f0000f0000f (.branch 0x1f2228888444411110f0f00f0000f (.branch 0x1f0004444222a11110f0000f0000f (r7p0) (r7p1)) (.branch 0x1f2228f88444411110f0000f0000f (r7p2) (.branch 0x1f888444f222211110f0000f0000f (r7p3) (r7p4)))) (.branch 0x1f0004444222211110f0000f8000f0008 (.branch 0x1f000222211110f0000f00040000f0008 (r7p5) (r7p6)) (.branch 0x1f000444c222211110f0000f0000f0008 (r7p7) (.branch 0x1f0005555222211110f0000f0000f0008 (r7p8) (r7p9))))) (.branch 0x1f00099994f44222211110f0000f0000f (.branch 0x1f0008888444f222211110f0000f00004 (.branch 0x1f0008888444422221f11040000f0000f (r7p10) (r7p11)) (.branch 0x1f00088886222444411110f0000f0000f (r7p12) (.branch 0x1f00088f8444f222211110f0000f0000f (r7p13) (r7p14)))) (.branch 0x1f00288884444222211110f0000f0000f (.branch 0x1f000aaaa4f44222211110f0000f0000f (r7p15) (r7p16)) (.branch 0x1f00f4444222211110f0000f0000f0008 (r7p17) (.branch 0x1f00f99994444222211110f0000f0000f (r7p18) (r7p19)))))) (.branch 0x1f4448888222211110f00040000f0000f (.branch 0x1f22288885555444411110f0000f0000f (.branch 0x1f2228888444411110f0000ff00f0000f (.branch 0x1f2224444222211110f0000f0000f0008 (r7p20) (r7p21)) (.branch 0x1f222888844441f1111110f0000f0000f (r7p22) (.branch 0x1f22288884444333311110f0000f0000f (r7p23) (r7p24)))) (.branch 0x1f222f0009999444411110f0000f0000f (.branch 0x1f222f000444411110f0000f0000f0008 (r7p25) (r7p26)) (.branch 0x1f22f88884444222211110f0000f0000f (r7p27) (.branch 0x1f4444444222211110f0000f0000f0008 (r7p28) (r7p29))))) (.branch 0x1f8884f444444222211110f0000f0000f (.branch 0x1f4f488884444222211110f0000f0000f (.branch 0x1f44488f84444222211110f0000f0000f (r7p30) (r7p31)) (.branch 0x1f8884444222211110f0000f0000f0004 (r7p32) (.branch 0x1f8884444222211110f0f0f0000f0000f (r7p33) (r7p34)))) (.branch 0x1f888f222f000444411110f0000f0000f (.branch 0x1f88899994444222211110f0000f0000f (r7p35) (r7p36)) (.branch 0x1faaaaaaa4444222211110f0000f0000f (r7p37) (.branch 0x1ff00f2228888444411110f0000f0000f (r7p38) (r7p39))))))

def a7p0 : Keys := .leaf [
0xf800447c22279111088887801,0xf911444422220f88807800078,0xfa2247c41111088880780007a,0xfc4427a211110888807800078,0xc4442222111108888807878000784,0xc4442222111108888878078000079,0xc444222211110f888800007800079,0xc4442222191108888780007800078,0xc4442227911108888800078000784,0xc44427a211110888880000780007c,0xc4442a2211110888878000780007d,0xc47c2222111108888800078000079,0xc7c42222111108888800007800079,0xcc442222111108888780007800078,0xf8002222111108888780007c00079,0xf800222211110888878400780007b,0xf80022221111088c878000780007a,0xf800222211110f888078000780042,0xf8002222111508888780007800078,0xf8002227911108888780007800040,0xf80027a2111108888078000780042,0xf800444411110888878000780027c,0xf80044441111088887a000780007e,0xf8004444111108a8878000780007f,0xf800444411110f88807800200007f,0xf800444411310888878000780007d,0xf8004444222211110888810780786,0xf800444422221111088881780007b,0xf800444422221111098880780007a,0xf8004444222791110888810000786,0xf8004444222791110888878780786,0xf800444422279111088887f800786]
def a7p1 : Keys := .leaf [
0xf8004444222791110f8880780007f,0xf8004444222791110f88888880786,0xf800444423221111088880780007f,0xf800444427a211110f8880780007f,0xf800444427a222279111088880786,0xf800444427a79111088880780007f,0xf800444427a7a2279111088880786,0xf80044442aaa91110f8880780007f,0xf80044442faa9111088880780007e,0xf80044442faa91110f8880780007f,0xf8004444333311110f8880780007f,0xf800447c11110888878000200007d,0xf800447c22221111088881000007b,0xf800447c22221111088887878007b,0xf800447c22221111088887f80007b,0xf800447c222211110f8880780007a,0xf800447c222211110f8888888007b,0xf800447c222791110888878000079,0xf800447c222791110888878000784,0xf800447c2227a2221111088887801,0xf800447c27a21111088880780007f,0xf800447c27a22222111108888007b,0xf800447c2aaa91110888878000079,0xf800447c33331111088887800007b,0xf800447c444422279111088887804,0xf800454422221111088880780007a,0xf80047c411110888807800200007f,0xf80047c4222211110f8880780007a,0xf80047c422279111088880780007a,0xf80047c427a21111088880780007a,0xf80047c42aaa9111088880780007a,0xf80047c433331111088880780007a]
def a7p2 : Keys := .leaf [
0xf80047c4444422279111088880786,0xf80047c4447c2222111108888007b,0xf80047fc22221111088880780007a,0xf80047fc447c2222111108888007b,0xf8004ccca22211110f8880780007a,0xf8004ccca22791110888878000784,0xf8004ccca7a21111088880780007f,0xf8004cccaaaa9111078000780007a,0xf8004fcca2221111088880780007b,0xf8004fcca22211110f8880780007a,0xf8005555222211110f8880780007a,0xf8005555222791110888878000786,0xf800555527a21111088880780007f,0xf8005555333308888780007800078,0xf8042222111108888780007800079,0xf807c444222211110888878780784,0xf807c444222211110f8880780007a,0xf807c444222791110888878000784,0xf807c44427a21111088880780007e,0xf807c47c222211110888878000079,0xf807c7c422221111088880780007b,0xf820444411110888878000780007c,0xf878444422221111088887f800079,0xf8784444222211110f8880780007f,0xf8784444222791110888878000784,0xf878444427a21111088880780007e,0xf878447c222211110888878000079,0xf87847c422221111088880780007b,0xf9112222088887800078000780040,0xf911444408888780007800200007d,0xf911444422220888810000780007b,0xf9114444222208888787807800078]
def a7p3 : Keys := .leaf [
0xf91144442222088887f800780007d,0xf911444422220f888780007800078,0xf911444422220f888888807800078,0xf9114444222211110f8880780007a,0xf911444422278888878000780007d,0xf9114444222791110888878000784,0xf911444427a20888878000780007d,0xf911444427a21111088880780007e,0xf91144442aaa8888878000780007d,0xf911444433330888878000780007d,0xf911447c222208888780007800078,0xf911447c222211110888878000079,0xf91147c4222208888780007800078,0xf91147c422221111088880780007b,0xf9114ccca22208888780007800078,0xf9115555222208888780007800078,0xf9117800444422220f8880780007a,0xfa221111088887800078000780040,0xfa22444411110888810000780007e,0xfa22444411110888878780780007c,0xfa2244441111088887f800780007c,0xfa22444411110f88888880780007c,0xfa224444222791110888878000784,0xfa22444427a21111088880780007c,0xfa22447c11110888878000780007d,0xfa22447c222211110888878000079,0xfa2247c411110888878000780007d,0xfa2247c422221111088880780007b,0xfa2247c444441111088880780007c,0xfa224ccc91110888878000780007d,0xfa22555511110888878000780007d,0xfa227800444411110f8880780007f]
def a7p4 : Keys := .leaf [
0xfa22780047c41111088880780007a,0xfa22791144440888878000780007d,0xfa27c44411110888878000780007d,0xfa27c444222791110888878000784,0xfb33444411110888878000780007c,0xfb33791144440888878000780007d,0xfc44111108888780007800200007d,0xfc44222211110888810000780007b,0xfc442222111108888787807800079,0xfc4422221111088887f8007800079,0xfc44222211110f888888807800079,0xfc442227911108888780007800078,0xfc4427a2111108888780007800078,0xfc4427a2222211110888807800079,0xfc442aaa911108888780007800078,0xfc443333111108888780007800078,0xfc444444222791110888878000784,0xfc44444427a21111088880780007e,0xfc44447c222211110888878000079,0xfc4447c4222211110888807800079,0xfc447800222211110f8880780007a,0xfc44780027a21111088880780007f,0xfc447911222208888780007800078,0xfc447a22111108888780007800078,0xfc7c2222111108888780007800078,0xfc7c447c222211110888878000079,0xfd552222111108888780007800079,0xfd557911222208888780007800078,0xa22211110888880007800078000780042,0xc44411110888880007800078002000079,0xc44422221111088888000100007800079,0xc44422221111088888000780007800079]
def a7p5 : Keys := .leaf [
0xc44422221111088888000787807800079,0xc444222211110888880007f800780007c,0xc44422221111088888008780007800079,0xc4442222111108888807878000780007a,0xc44422221111088888078800078000784,0xc4442222111108888808078000780007c,0xc4442222111108888878078000780007f,0xc44422221111088888780800078000079,0xc444222211110f8008888800007800079,0xc444222211110f8888000780007800079,0xc444222211110f8888888800007800079,0xc4442222180011110888878000780007b,0xc44422221911088888000780007800079,0xc4442222191111110888878000780007b,0xc44422221999911108000780007800079,0xc4442227911108888800078000780007c,0xc4442227a222111108888800078000784,0xc44427a2111108888800078000780007c,0xc44427a22222111108888800007800079,0xc4442800222211110888878000780007b,0xc4442a22111108888800078000780007c,0xc4442a222222111108888780007800079,0xc4442aaa911108888800078000780007c,0xc4442aaaa80011110888878000780007b,0xc4443333111108888800078000780007c,0xc47c22221111088888000780007800079,0xc47c44442222111108888800078000079,0xc7c422221111088888000780007800079,0xc7c44444222211110888880000780007c,0xc8004444222211110888878000780007e,0xcc4422221111088888000780007800079,0xcc444444222211110888878000780007c]
def a7p6 : Keys := .leaf [
0xcccca2221111088888000780007800079,0xccccc800222211110888878000780007e,0xd55522221111088888000780007800079,0xf80011110888878000780020000780040,0xf80022221111088881000078000780040,0xf80022221111088887800078000780040,0xf80022221111088887800078000780048,0xf80022221111088887800078000780052,0xf8002222111108888780007800440007d,0xf8002222111108888780007c000780040,0xf8002222111108888780007c00780007d,0xf8002222111108888780007f807800040,0xf8002222111108888780040400780007d,0xf80022221111088887840078000780042,0xf80022221111088887840780007800078,0xf80022221111088887878078000780042,0xf8002222111108888787840400780007d,0xf80022221111088887f80078000780042,0xf80022221111088c87800078000780042,0xf80022221111088c8888878000780007c,0xf800222211110f8887800078000780042,0xf800222211110f8888888078000780042,0xf80022221115088887800078000780040,0xf8002222111511110888878000780007e,0xf80022261111088887800078000780040,0xf80022279111088887800078000780040,0xf8002227a222111108888780007800040,0xf80027a21111088887800078000780040,0xf80027a22222111108888078000780042,0xf8002aaa9111088887800078000780040,0xf80033331111088887800078000780042,0xf8004004222211110888878000780007f]
def a7p7 : Keys := .leaf [
0xf8004444111108888100007800200007b,0xf8004444111108888780007800200007d,0xf80044441111088887800078002200078,0xf80044441111088887800078002780078,0xf80044441111088887800078002780205,0xf8004444111108888780007800280007d,0xf8004444111108888780007800300007f,0xf8004444111108888780007f80200007d,0xf80044441111088887800220007800078,0xf8004444111108888787807800200007f,0xf80044441111088887a0007800200007f,0xf80044441111088887a0078000780007d,0xf80044441111088887f8007800200007f,0xf80044441111088887f80220007800078,0xf8004444111108a88780007800200007f,0xf8004444111108a888888780007800079,0xf800444411110f888780007800200007f,0xf800444411110f888888807800200007f,0xf8004444113108888780007800200007d,0xf8004444113111110888878000780007b,0xf8004444202011110888878000780007a,0xf8004444222211110888810000780007b,0xf8004444222211110888810100780007b,0xf80044442222111108888107807800078,0xf80044442222111108888107810000786,0xf8004444222211110888811000780007e,0xf8004444222211110888817800780007d,0xf8004444222211110888817801000007b,0xf80044442222111108888180007800079,0xf80044442222111108888300007800079,0xf8004444222211110888850000780007c,0xf800444422221111088887800078000fc]
def a7p8 : Keys := .leaf [
0xf8004444222211110888878000780017e,0xf8004444222211110888878000780027c,0xf80044442222111108888780007880079,0xf8004444222211110888878000790007b,0xf80044442222111108888780007c00079,0xf80044442222111108888780010780786,0xf8004444222211110888878001780007b,0xf80044442222111108888780020780784,0xf80044442222111108888780047800079,0xf8004444222211110888878080780007a,0xf8004444222211110888878100780007a,0xf8004444222211110888878200780007a,0xf8004444222211110888878400780007a,0xf80044442222111108888787807f80786,0xf8004444222211110888878800780007f,0xf8004444222211110888879000780007f,0xf800444422221111088887a000780007f,0xf800444422221111088887c000780007f,0xf800444422221111088887f8007f8007b,0xf800444422221111088887ff80780007a,0xf80044442222111108888807878000784,0xf80044442222111108888878078000079,0xf8004444222211110889878000780007a,0xf800444422221111088c878000780007a,0xf800444422221111088f8780007800008,0xf8004444222211110898878000780007f,0xf80044442222111108a8878000780007f,0xf80044442222111108f8878000080007c,0xf8004444222211110988810000780007b,0xf8004444222211110988878000780007a,0xf80044442222111109888888807800079,0xf8004444222211110a88878000780007a]
def a7p9 : Keys := .leaf [
0xf8004444222211110c88878000780007f,0xf8004444222211110f80088880780007a,0xf8004444222211110f888078000780008,0xf8004444222211110f888078000780012,0xf8004444222211110f888078000780022,0xf8004444222211110f888078000780042,0xf8004444222211110f88807800080007d,0xf8004444222211110f88807800100007f,0xf8004444222211110f88807800200007f,0xf8004444222211110f88807800400007f,0xf8004444222211110f88807f80780007a,0xf8004444222211110f888080007800079,0xf8004444222211110f88810000780007b,0xf8004444222211110f888200007800078,0xf8004444222211110f88840000780007d,0xf8004444222211110f88878780780007a,0xf8004444222211110f8887f800780007f,0xf8004444222211110f888800007800079,0xf8004444222211110f88888f80780007a,0xf8004444222211110f8888f880780007f,0xf8004444222211110f8f888880780007a,0xf8004444222211110f8f8f8880780007a,0xf8004444222211110ff8888880780007f,0xf8004444222211110ff88f8880780007f,0xf80044442222111110000f8880780007b,0xf80044442222111188888780007800078,0xf80044442222111508888780007800078,0xf80044442222111788888780007800012,0xf80044442222111791110888878780786,0xf80044442222111791110f8880780007a,0xf8004444222211190888878000780007d,0xf8004444222211310888878000780007d]
def a7p10 : Keys := .leaf [
0xf8004444222211790888878000100007e,0xf8004444222211791111088887f80007b,0xf80044442222117911110f8880780007f,0xf8004444222217910888810000780007b,0xf80044442222179111110f8880780007a,0xf80044442222191108888780007800078,0xf8004444222219998888810000780007b,0xf80044442222199991110f8880780007a,0xf800444422221f9991110f8880780007a,0xf80044442222200011110f8880780007a,0xf80044442222200791110888878000786,0xf8004444222291110888878000780007c,0xf8004444222311110888878000780007e,0xf8004444222611110888878000780007c,0xf8004444222791110888810000780007e,0xf80044442227911108888780007800009,0xf80044442227911108888780007800013,0xf80044442227911108888780007800020,0xf80044442227911108888780007800040,0xf80044442227911108888780007800084,0xf80044442227911108888780007800106,0xf80044442227911108888780007800205,0xf80044442227911108888780007800405,0xf80044442227911108888780007f80784,0xf80044442227911108888780008000784,0xf80044442227911108888780010000786,0xf80044442227911108888780020000781,0xf80044442227911108888780040000784,0xf8004444222791110888878780780007f,0xf80044442227911108888787878000784,0xf800444422279111088887f800780007f,0xf800444422279111088887f8078000784]
def a7p11 : Keys := .leaf [
0xf80044442227911108888800078000784,0xf800444422279111088f8888878000784,0xf80044442227911108f88888878000784,0xf8004444222791110f88878000780007f,0xf8004444222791110f88888880780007e,0xf8004444222791110f888888878000784,0xf80044442227911110000888878000786,0xf80044442227911791110888878000786,0xf80044442227917911110888878000786,0xf80044442227979111110888878000784,0xf80044442227999991110888878000784,0xf80044442227a00011110888878000783,0xf80044442227a22211110888810000786,0xf80044442227a22211110888878780786,0xf80044442227a2221111088887f800786,0xf80044442227a22211110f8880780007a,0xf80044442227a22211110f88888880786,0xf8004444222a11110888878000780007c,0xf8004444223211110888878000780007e,0xf8004444227a11110888878000200007d,0xf8004444227a222211110f8880780007a,0xf8004444227a222791110888878000784,0xf8004444227fa22791110888878000784,0xf800444422a211110888878000780007c,0xf8004444232211110888810000780007e,0xf8004444232211110888878000780007e,0xf8004444232222221111088880780007b,0xf8004444262211110888878000780007c,0xf8004444278022221111088880780007a,0xf800444427a2111108888078000780008,0xf800444427a2111108888078000780012,0xf800444427a2111108888078000780022]
def a7p12 : Keys := .leaf [
0xf800444427a2111108888078000780042,0xf800444427a211110888807800080007c,0xf800444427a211110888807800100007e,0xf800444427a211110888807800200007f,0xf800444427a211110888807800400007f,0xf800444427a211110888807f80780007f,0xf800444427a211110888808000780007c,0xf800444427a211110888810000780007e,0xf800444427a2111108888200007800078,0xf800444427a211110888840000780007c,0xf800444427a211110888878780780007e,0xf800444427a21111088887f800780007e,0xf800444427a211110888880000780007c,0xf800444427a21111088f888880780007a,0xf800444427a2111108f8888880780007c,0xf800444427a211110f88878000780007f,0xf800444427a211110f88888880780007e,0xf800444427a211111000088880780007e,0xf800444427a211179111088880780007a,0xf800444427a211791111088880780007e,0xf800444427a217911111088880780007e,0xf800444427a219999111088880780007e,0xf800444427a220001111088880780007a,0xf800444427a2222211110f8880780007a,0xf800444427a222279111088880780007f,0xf800444427a2222791110888878000784,0xf800444427a22227a2221111088880786,0xf800444427a2227a1111088880780007f,0xf800444427a791110888878000780007c,0xf800444427a791110888878780780007e,0xf800444427a7a2221111088880780007a,0xf800444427a7a2279111088880780007f]
def a7p13 : Keys := .leaf [
0xf800444427a7a22791110888878000784,0xf800444427a7a227a2221111088880786,0xf800444427a7a7a21111088880780007f,0xf800444427fa22221111088880780007a,0xf800444427fa27a21111088880780007f,0xf80044442a2211110888878000780007c,0xf80044442aaa91110888810000780007e,0xf80044442aaa91110888878780780007e,0xf80044442aaa9111088887f800780007e,0xf80044442aaa911108f8878000780007f,0xf80044442aaa91110f88878000780007f,0xf80044442aaa91110f88888880780007e,0xf80044442aaa99999111078000780007f,0xf80044442aaaa22211110f8880780007a,0xf80044442aaaa22791110888878000784,0xf80044442aaaa7a21111088880780007f,0xf80044442aaf91110888878000780007c,0xf80044442aafa22791110888878000784,0xf80044442faa91110888878000780007c,0xf80044442faa91110f88878000780007f,0xf80044442faa91110f88888880780007e,0xf80044442faaa2221111088880780007a,0xf80044442faaa22211110f8880780007a,0xf80044442faaa7a21111088880780007e,0xf80044442faaaaaa9111088880780007f,0xf80044443111222208888780007800078,0xf8004444322211110888878000780007e,0xf8004444333311110888810000780007e,0xf80044443333111108888300007800079,0xf8004444333311110888878780780007f,0xf800444433331111088887f800780007e,0xf8004444333311110f88878000780007f]
def a7p14 : Keys := .leaf [
0xf8004444333311110f88888880780007e,0xf8004444333311790888878000780007d,0xf8004444333319998888878000780007d,0xf80044443333222211110f8880780007a,0xf80044443333222791110888878000786,0xf8004444333327a21111088880780007f,0xf8004444333791110888878000780007e,0xf80044443337a22791110888878000786,0xf800444437b311110888878000780007c,0xf800444437b327a21111088880780007e,0xf80044443bbb91110888878000780007c,0xf80044444000222211110f8880780007f,0xf80044444000222791110888878000786,0xf8004444400027a21111088880780007e,0xf8004444407822221111088887800007b,0xf8004444a222111108888780007800079,0xf8004445222211110888878000780007b,0xf8004447a222111108888780007800040,0xf8004447c444222211110f8880780007f,0xf8004447c444222791110888878000784,0xf8004447c44427a21111088880780007e,0xf800444c2222111108888780007800079,0xf8004454222211110888878000780007b,0xf8004464111108888780007800200007d,0xf80044642222111108888780007800079,0xf800447c111108888780007800200007d,0xf800447c222211110888810000780007b,0xf800447c2222111108888780000780009,0xf800447c2222111108888780000780013,0xf800447c2222111108888780000780020,0xf800447c2222111108888780000780040,0xf800447c222211110888878000080007c]
def a7p15 : Keys := .leaf [
0xf800447c222211110888878000100007e,0xf800447c222211110888878000200007d,0xf800447c222211110888878000400007d,0xf800447c2222111108888780007f80079,0xf800447c2222111108888780008000079,0xf800447c222211110888878001000007b,0xf800447c2222111108888780020000079,0xf800447c222211110888878004000007c,0xf800447c222211110888878780780007a,0xf800447c2222111108888787878000079,0xf800447c22221111088887f800780007a,0xf800447c22221111088887f8078000079,0xf800447c2222111108888800078000079,0xf800447c22221111088f8888878000079,0xf800447c2222111108f88888878000079,0xf800447c222211110f88878000780007a,0xf800447c222211110f88888880780007a,0xf800447c222211110f888888878000079,0xf800447c222211111000088887800007b,0xf800447c222211179111088887800007b,0xf800447c222211791111088887800007b,0xf800447c2222179111110888878000079,0xf800447c2222199991110888878000079,0xf800447c222220001111088887800007b,0xf800447c2227911108888780007800078,0xf800447c2227a22211110888878000079,0xf800447c2227a22211110888878000781,0xf800447c227a222211110888878000079,0xf800447c27a211110888878000780007d,0xf800447c27a222221111088880780007a,0xf800447c27a2222211110888878000079,0xf800447c2aaa91110888878000780007d]
def a7p16 : Keys := .leaf [
0xf800447c2aaaa22211110888878000079,0xf800447c333311110888878000780007f,0xf800447c333322221111088887800007b,0xf800447c400022221111088887800007e,0xf800447c444411110888878000200007d,0xf800447c444422221111088881000007b,0xf800447c444422221111088887878007b,0xf800447c444422221111088887f80007b,0xf800447c4444222211110f8880780007f,0xf800447c4444222211110f8888888007b,0xf800447c444422279111088887800007c,0xf800447c4444222791110888878000784,0xf800447c44442227a2221111088887801,0xf800447c444427a21111088880780007e,0xf800447c444427a22222111108888007b,0xf800447c44442aaa9111088887800007c,0xf800447c444433331111088887800007e,0xf800447c4447a22211110888878000079,0xf800447fc47c222211110888878000079,0xf80044c42222111108888780007800079,0xf8004544222211110888810000780007b,0xf8004544222211110888878000780007b,0xf8004544444422221111088880780007e,0xf80046442222111108888780007800079,0xf8004780444422221111088880780007f,0xf80047c4111108888780007800200007d,0xf80047c42222111108888078000780009,0xf80047c42222111108888078000780012,0xf80047c42222111108888078000780022,0xf80047c42222111108888078000780042,0xf80047c4222211110888807800080007c,0xf80047c4222211110888807800100007f]
def a7p17 : Keys := .leaf [
0xf80047c4222211110888807800200007f,0xf80047c4222211110888807800400007f,0xf80047c4222211110888807f80780007a,0xf80047c42222111108888080007800079,0xf80047c4222211110888810000780007b,0xf80047c42222111108888200007800079,0xf80047c4222211110888840000780007c,0xf80047c4222211110888878780780007b,0xf80047c422221111088887f800780007b,0xf80047c42222111108888800007800079,0xf80047c422221111088f8888807800079,0xf80047c42222111108f88888807800079,0xf80047c4222211110f88878000780007a,0xf80047c4222211110f88888880780007b,0xf80047c4222211111000088880780007b,0xf80047c4222211179111088880780007a,0xf80047c4222211791111088880780007f,0xf80047c4222217911111088880780007b,0xf80047c4222219999111088880780007b,0xf80047c4222220001111088880780007a,0xf80047c42227911108888780007800078,0xf80047c42227a2221111088880780007b,0xf80047c4227a22221111088880780007b,0xf80047c427a2111108888780007800078,0xf80047c427a222221111088880780007b,0xf80047c42aaa91110888878000780007d,0xf80047c42aaaa22211110888807800079,0xf80047c4333311110888878000780007d,0xf80047c4333322221111088880780007b,0xf80047c4400022221111088880780007f,0xf80047c4444411110888807800200007f,0xf80047c44444222211110f8880780007f]
def a7p18 : Keys := .leaf [
0xf80047c4444422279111088880780007f,0xf80047c44444222791110888878000784,0xf80047c444442227a2221111088880786,0xf80047c4444427a21111088880780007e,0xf80047c444442aaa9111088880780007e,0xf80047c4444433331111088880780007e,0xf80047c44447a2221111088880780007a,0xf80047c4447c22221111088880780007a,0xf80047c4447c222211110888878000079,0xf80047c4447c44442222111108888007b,0xf80047c7c44422221111088880780007f,0xf80047c7c7c422221111088880780007a,0xf80047fc2222111108888780007800079,0xf80047fc22221111088887f800780007b,0xf80047fc444422221111088880780007f,0xf80047fc447c22221111088880780007a,0xf80047fc447c222211110888878000079,0xf80047fc447c44442222111108888007b,0xf80047fc47c422221111088880780007a,0xf8004c442222111108888780007800079,0xf8004ccc911108888780007800200007d,0xf8004ccca22211110888810000780007b,0xf8004ccca22211110888878780780007b,0xf8004ccca2221111088887f800780007a,0xf8004ccca2221111088f878000780007a,0xf8004ccca22211110f88878000780007a,0xf8004ccca22211110f88888880780007b,0xf8004ccca22219999111078000780007a,0xf8004ccca227911108888780007800078,0xf8004ccca227a22211110888878000781,0xf8004ccca7a2111108888780007800078,0xf8004ccca7a222221111088880780007b]
def a7p19 : Keys := .leaf [
0xf8004cccaaaa911108888780007800078,0xf8004cccaaaaa2221111078000780007a,0xf8004cccb33311110888878000780007a,0xf8004cccc444222211110f8880780007f,0xf8004cccc444222791110888878000784,0xf8004cccc44427a21111088880780007c,0xf8004cccc4442aaa9111078000780007f,0xf8004cccc47c222211110888878000079,0xf8004cccc7c422221111088880780007a,0xf8004cfca222111108888780007800079,0xf8004cfcc47c222211110888878000079,0xf8004fcca222111108888780007800079,0xf8004fcca22211110f88878000780007a,0xf8004fcca22211110f88888880780007b,0xf8004fccc44422221111088880780007f,0xf8004fccc444222211110f8880780007f,0xf8004fccc7c422221111088880780007b,0xf8004fcccccca2221111088880780007a,0xf8005111444422220888878000780007d,0xf8005444222211110888878000780007b,0xf8005555111108888780007800200007f,0xf8005555222211110888810000780007b,0xf8005555222211110888850000780007c,0xf8005555222211110888878780780007a,0xf800555522221111088887f800780007a,0xf8005555222211110f88878000780007a,0xf8005555222211110f88888880780007b,0xf80055552222111788888780007800078,0xf80055552222199988888780007800078,0xf8005555222791110888878000780007a,0xf80055552227a22211110888878000783,0xf800555527a2111108888780007800078]
def a7p20 : Keys := .leaf [
0xf800555527a222221111088880780007b,0xf80055552aaa911108888780007800078,0xf8005555333311110888878000780007a,0xf80055553333222208888780007800078,0xf80055554444222211110f8880780007f,0xf80055554444222791110888878000786,0xf8005555444427a21111088880780007e,0xf8005555444433330888878000780007d,0xf8005555447c22221111088887800007b,0xf800555547c422221111088880780007a,0xf800557d222211110888878000780007b,0xf800557d447c22221111088887800007b,0xf80057d52222111108888780007800079,0xf80057d547c422221111088880780007b,0xf8005ddda222111108888780007800079,0xf8006222444411110888878000780007e,0xf8006444222211110888878000780007b,0xf80066664444222211110f8880780007a,0xf80066664444222791110888878000784,0xf8006666444427a21111088880780007f,0xf8006666447c222211110888878000079,0xf800666647c422221111088880780007a,0xf8006667c444222791110888878000784,0xf800667e447c222211110888878000079,0xf80067e6444422221111088880780007a,0xf80067e6444427a21111088880780007f,0xf80067e647c422221111088880780007a,0xf800c4442222111108888780007800078,0xf80144442222111108888780007800078,0xf80244442222111108888780007800078,0xf80422221111088887800078000780040,0xf80444442222111108888780007800078]
def a7p21 : Keys := .leaf [
0xf8047800222211110888878000780007a,0xf807a2221111088887800078000780040,0xf807c004222211110888878000780007f,0xf807c444111108888780007800200007d,0xf807c444222211110888810000780007b,0xf807c4442222111108888780007f80784,0xf807c4442222111108888787807800079,0xf807c4442222111108888787878000784,0xf807c44422221111088887f800780007b,0xf807c44422221111088f8888878000784,0xf807c444222211110f888780007800078,0xf807c444222211110f888888807800079,0xf807c444222791110888878000780007d,0xf807c4442227a22211110888878000784,0xf807c44427a211110888878000780007d,0xf807c44427a2222211110888807800079,0xf807c4442aaa91110888878000780007d,0xf807c444333311110888878000780007c,0xf807c47c2222111108888780007800078,0xf807c47c4444222211110888878000079,0xf807c7c42222111108888780007800078,0xf807c7c4444422221111088880780007c,0xf807cccca222111108888780007800078,0xf807d5552222111108888780007800079,0xf807f8004444222211110888878780786,0xf807f8004444222211110f8880780007a,0xf807f8004444222791110888878000786,0xf807f800444427a21111088880780007a,0xf807f800447c22221111088887800007b,0xf807f80047c422221111088880780007a,0xf8084444222211110888878000780007d,0xf8104444222211110888878000780007d]
def a7p22 : Keys := .leaf [
0xf8204444111108888780007800200007d,0xf8204444222211110888878000780007d,0xf8207800444411110888878000780007f,0xf8404444222211110888878000780007d,0xf87822221111088887800078000780040,0xf8784444111108888780007800200007d,0xf8784444202011110888878000780007a,0xf8784444222211110888810000780007e,0xf87844442222111108888780007f80079,0xf87844442222111108888787807800079,0xf878444422221111088887f800780007c,0xf878444422221111088887f8078000079,0xf87844442222111108f88888878000079,0xf8784444222211110f88878000780007d,0xf8784444222211110f88888880780007c,0xf8784444222791110888878000780007d,0xf87844442227a22211110888878000784,0xf878444427a211110888878000780007d,0xf878444427a2222211110888807800079,0xf87844442aaa91110888878000780007c,0xf8784444333311110888878000780007c,0xf878447c2222111108888780007800078,0xf878447c4444222211110888878000079,0xf87847c42222111108888780007800078,0xf87847c4444422221111088880780007c,0xf8784ccca222111108888780007800078,0xf87855552222111108888780007800078,0xf8787800444422221111088887f80007b,0xf87878004444222211110f8880780007f,0xf87878004444222791110888878000786,0xf8787800444427a21111088880780007f,0xf8787800447c22221111088887800007b]
def a7p23 : Keys := .leaf [
0xf878780047c422221111088880780007f,0xf87fc4442222111108888780007800078,0xf888c4442222111108000780007800079,0xf888f8004444222211110f8880780007a,0xf888f8004444222791110888878000786,0xf888f800444427a21111088880780007f,0xf888f800447c22221111088887800007b,0xf888f80047c422221111088880780007a,0xf9004444222211110888810000780007b,0xf90044442222111108888780007800078,0xf91122221111088887800078000780040,0xf9114444111108888780007800200007d,0xf91144442222088887800078000780008,0xf91144442222088887800078000780012,0xf91144442222088887800078000780020,0xf91144442222088887800078000780040,0xf9114444222208888780007800080007d,0xf9114444222208888780007800100007f,0xf9114444222208888780007800200007d,0xf9114444222208888780007800400007d,0xf9114444222208888780007f807800078,0xf91144442222088887800080007800079,0xf9114444222208888780010000780007b,0xf91144442222088887800200007800078,0xf9114444222208888780040000780007d,0xf91144442222088887878780007800078,0xf91144442222088887f8078000780007d,0xf91144442222088888000780007800079,0xf91144442222088f88888780007800078,0xf9114444222208f88888878000780007d,0xf911444422220f8888888780007800078,0xf9114444222210000888878000780007b]
def a7p24 : Keys := .leaf [
0xf9114444222211110888810000780007b,0xf9114444222211110888878780780007b,0xf911444422221111088887f800780007e,0xf9114444222211110f888780007800078,0xf9114444222211110f888888807800079,0xf91144442222111788888780007800078,0xf9114444222211790888878000780007d,0xf91144442222179108888780007800078,0xf91144442222199988888780007800078,0xf9114444222220000888878000780007a,0xf9114444222791110888878000780007c,0xf91144442227a22208888780007800078,0xf91144442227a22211110888878000784,0xf9114444227a222208888780007800078,0xf911444427a211110888878000780007c,0xf911444427a2222208888780007800078,0xf911444427a222221111088880780007b,0xf91144442aaa91110888878000780007c,0xf91144442aaaa22208888780007800078,0xf9114444333311110888878000780007c,0xf91144443333222208888780007800078,0xf9114444400022220888878000780007f,0xf9114447c44422220888878000780007d,0xf911447c2222111108888780007800078,0xf911447c444422220888878000780007d,0xf911447c4444222211110888878000079,0xf91147c42222111108888780007800079,0xf91147c4444422220888878000780007d,0xf91147c4444422221111088880780007e,0xf9114ccca222111108888780007800079,0xf9114cccc44422220888878000780007d,0xf91155552222111108888780007800079]
def a7p25 : Keys := .leaf [
0xf9115555444422220888878000780007d,0xf91166664444222208888780007800078,0xf91178002222088887800078000780040,0xf9117800444408888780007800200007d,0xf9117800444422220888810000780007b,0xf9117800444422220888878780780007a,0xf911780044442222088887f800780007f,0xf9117800444422220f888780007800078,0xf9117800444422220f88888880780007a,0xf91178004444222211110f8880780007a,0xf9117800444422278888878000780007d,0xf91178004444222791110888878000786,0xf9117800444427a20888878000780007d,0xf9117800444427a21111088880780007f,0xf911780044442aaa8888878000780007d,0xf9117800444433330888878000780007d,0xf9117800447c222208888780007800078,0xf9117800447c22221111088887800007b,0xf911780047c4222208888780007800078,0xf911780047c422221111088880780007a,0xf91178004ccca22208888780007800078,0xf91178005555222208888780007800078,0xf9117807c444222208888780007800078,0xf9117878444422220888878000780007d,0xf9117888c444222208888780007800078,0xf917c4442222111108888780007800078,0xf917f9114444222208888780007800078,0xf9794444222211110888878000780007d,0xf9797911444422220888878000780007d,0xf999f9114444222208888780007800078,0xfa0044442222111108888780007800078,0xfa2222221111088887800078000780040]
def a7p26 : Keys := .leaf [
0xfa2244441111088887800078000780008,0xfa2244441111088887800078000780012,0xfa2244441111088887800078000780020,0xfa2244441111088887800078000780040,0xfa224444111108888780007800080007c,0xfa224444111108888780007800100007e,0xfa224444111108888780007800200007d,0xfa224444111108888780007800400007d,0xfa224444111108888780007f80780007d,0xfa224444111108888780008000780007c,0xfa224444111108888780010000780007e,0xfa2244441111088887800200007800078,0xfa224444111108888780040000780007c,0xfa2244441111088887878780007800078,0xfa2244441111088887f8078000780007d,0xfa224444111108888800078000780007c,0xfa2244441111088f88888780007800078,0xfa224444111108f88888878000780007c,0xfa22444411110f888888878000780007d,0xfa224444111110000888878000780007e,0xfa2244441117911108888780007800078,0xfa224444117911110888878000780007e,0xfa224444179111110888878000780007d,0xfa224444199991110888878000780007c,0xfa224444200011110888878000780007a,0xfa224444222211110888810000780007b,0xfa224444222211110888878780780007b,0xfa22444422221111088887f800780007b,0xfa224444222211110f888888807800079,0xfa224444222791110888878000780007d,0xfa2244442227a22211110888878000784,0xfa224444227a11110888878000780007d]
def a7p27 : Keys := .leaf [
0xfa22444427a211110888878000780007d,0xfa22444427a2222211110888807800079,0xfa2244442aaa91110888878000780007d,0xfa224444333311110888878000780007d,0xfa224444400011110888878000780007e,0xfa224447c44411110888878000780007c,0xfa22447c2222111108888780007800078,0xfa22447c444411110888878000780007c,0xfa22447c4444222211110888878000079,0xfa2247c42222111108888780007800078,0xfa2247c4444411110888878000780007c,0xfa2247c4444422221111088880780007b,0xfa224ccca222111108888780007800079,0xfa224cccc44411110888878000780007c,0xfa2255552222111108888780007800079,0xfa225555444411110888878000780007e,0xfa226666444411110888878000780007d,0xfa2278001111088887800078000780042,0xfa227800444411110888810000780007e,0xfa227800444411110888878780780007f,0xfa22780044441111088887f800780007f,0xfa227800444411110f88878000780007f,0xfa227800444411110f88888880780007e,0xfa2278004444222211110f8880780007a,0xfa2278004444222791110888878000786,0xfa227800444427a21111088880780007f,0xfa227800447c11110888878000780007f,0xfa227800447c22221111088887800007b,0xfa22780047c411110888878000780007a,0xfa22780047c422221111088880780007a,0xfa22780047c444441111088880780007e,0xfa2278004ccc91110888878000780007a]
def a7p28 : Keys := .leaf [
0xfa227800555511110888878000780007a,0xfa227807c44411110888878000780007c,0xfa227878444411110888878000780007c,0xfa227888c44411110888878000780007c,0xfa227911444411110888878000780007c,0xfa2279114444222208888780007800078,0xfa227911780044440888878000780007d,0xfa27c4442222111108888780007800078,0xfa27c444222791110888878000780007d,0xfa27c4442227a22211110888878000784,0xfa27f800444411110888878000780007e,0xfa27f8004444222791110888878000786,0xfa27f807c44411110888878000780007c,0xfa27fa22444411110888878000780007d,0xfa7a44442222111108888780007800078,0xfa7a7a22444411110888878000780007d,0xfaaaf800444411110888878000780007e,0xfaaafa22444411110888878000780007c,0xfb3344442222111108888780007800078,0xfb334444333311110888878000780007d,0xfb337800444411110888878000780007e,0xfb337911444411110888878000780007c,0xfb3379114444222208888780007800078,0xfb337911780044440888878000780007d,0xfb337a22444411110888878000780007c,0xfc004444222211110888878000780007d,0xfc4422221111088887800078000780008,0xfc4422221111088887800078000780013,0xfc4422221111088887800078000780020,0xfc4422221111088887800078000780040,0xfc442222111108888780007800080007d,0xfc442222111108888780007800100007e]
def a7p29 : Keys := .leaf [
0xfc442222111108888780007800200007d,0xfc442222111108888780007800400007d,0xfc442222111108888780007f807800078,0xfc4422221111088887800080007800079,0xfc442222111108888780010000780007b,0xfc4422221111088887800200007800078,0xfc442222111108888780040000780007d,0xfc4422221111088887878780007800078,0xfc4422221111088887f8078000780007d,0xfc4422221111088888000780007800079,0xfc4422221111088f88888780007800078,0xfc442222111108f88888878000780007d,0xfc44222211110f8888888780007800078,0xfc442222111110000888878000780007b,0xfc442222111791110888878000780007b,0xfc442222117911110888878000780007b,0xfc4422221791111108888780007800078,0xfc4422221999911108888780007800079,0xfc442222200011110888878000780007b,0xfc442227a222111108888780007800079,0xfc44227a2222111108888780007800079,0xfc4427a22222111108888780007800078,0xfc442aaaa222111108888780007800079,0xfc443333222211110888878000780007b,0xfc444000222211110888878000780007e,0xfc444444111108888780007800200007d,0xfc444444222211110888810000780007e,0xfc444444222211110888878780780007e,0xfc44444422221111088887f800780007e,0xfc444444222211110f88888880780007c,0xfc444444222791110888878000780007d,0xfc4444442227a22211110888878000784]
def a7p30 : Keys := .leaf [
0xfc44444427a211110888878000780007c,0xfc44444427a2222211110888807800079,0xfc4444442aaa91110888878000780007c,0xfc444444333311110888878000780007c,0xfc444447a222111108888780007800078,0xfc44447c2222111108888780007800078,0xfc44447c4444222211110888878000079,0xfc4447c42222111108888780007800078,0xfc4447c4444422221111088880780007c,0xfc444ccca222111108888780007800078,0xfc4455552222111108888780007800078,0xfc4466662222111108888780007800078,0xfc447800111108888780007800200007f,0xfc447800222211110888810000780007b,0xfc447800222211110888878780780007a,0xfc44780022221111088887f800780007a,0xfc447800222211110f88878000780007a,0xfc447800222211110f88888880780007b,0xfc447800222791110888878000780007a,0xfc44780027a2111108888780007800078,0xfc44780027a222221111088880780007a,0xfc4478002aaa91110888878000780007f,0xfc447800333311110888878000780007f,0xfc4478004444222211110f8880780007f,0xfc4478004444222791110888878000786,0xfc447800444427a21111088880780007e,0xfc447800447c22221111088887800007b,0xfc44780047c422221111088880780007a,0xfc447807a222111108888780007800079,0xfc4478782222111108888780007800079,0xfc447888a222111108888780007800079,0xfc4479112222111108888780007800079]
def a7p31 : Keys := .leaf [
0xfc447911444422220888878000780007d,0xfc4479117800222208888780007800078,0xfc447a222222111108888780007800079,0xfc447a22444411110888878000780007c,0xfc447a22780011110888878000780007a,0xfc47c444222211110888878000780007d,0xfc47fc442222111108888780007800078,0xfc7c4444222211110888878000780007d,0xfc7c447c2222111108888780007800078,0xfc7c447c4444222211110888878000079,0xfc7c7800222211110888878000780007b,0xfc7c7800447c22221111088887800007b,0xfc7c78782222111108888780007800079,0xfc7c7c442222111108888780007800078,0xfcccf800222211110888878000780007b,0xfcccfc442222111108888780007800079,0xfd554444222211110888878000780007d,0xfd5555552222111108888780007800078,0xfd557800222211110888878000780007b,0xfd5579112222111108888780007800079,0xfd557911444422220888878000780007d,0xfd5579117800222208888780007800078,0xfd557c442222111108888780007800079,0xfe6644442222111108888780007800078,0xfe667a22444411110888878000780007d,0xfe667c442222111108888780007800078,0xff8078004444222211110f8880780007a,0xff8078004444222791110888878000784,0xff807800444427a21111088880780007e,0xff807800447c222211110888878000079,0xff80780047c422221111088880780007b,0xff8079114444222208888780007800078]
def a7p32 : Keys := .leaf [
0xff807a22444411110888878000780007c,0xff807c442222111108888780007800079,0xff88f8004444222211110f8880780007a,0xff9179114444222208888780007800078,0xffa27800444411110888878000780007c,0xffa27800444427a21111088880780007e,0xffa27a22444411110888878000780007c,0xffc478002222111108888780007800079,0xffc4780047c422221111088880780007b,0xffc47c442222111108888780007800079]
def a7 : Keys := .branch 0x1f00088f855554444222211110f00000f (.branch 0x1f00088884444222211110f0000f0002f (.branch 0x1f444f0008f882222111100f0000f (.branch 0x1f0008f888888444f2222111100f0 (.branch 0x1f0008888444f22221f1100f0000f (a7p0) (a7p1)) (.branch 0x1f2228888444411110ff000f0000f (a7p2) (a7p3))) (.branch 0x1999944442222111110000f0000f0000f (.branch 0x1888844442222111110000f0f00f0000f (a7p4) (a7p5)) (.branch 0x1f000888822221111020000f00040000f (a7p6) (a7p7)))) (.branch 0x1f00088884f442222111100f0000f0008 (.branch 0x1f0008888444422f211110f000020000f (.branch 0x1f00088884444222219110f0000f0000f (a7p8) (a7p9)) (.branch 0x1f0008888444f2222111110000f0000f0 (a7p10) (a7p11))) (.branch 0x1f0008888666622221f11111100f0000f (.branch 0x1f00088884f4f444f222211110f0000f0 (a7p12) (a7p13)) (.branch 0x1f00088f84444222211110f000020000f (a7p14) (a7p15))))) (.branch 0x1f2228888444422221111020000f0000f (.branch 0x1f000aaaa4f4444442222111100f0000f (.branch 0x1f0008f888888444f2222111100f0000f (.branch 0x1f0008f8844442222111100f00040000f (a7p16) (a7p17)) (.branch 0x1f00099995555222211110f0000f0000f (a7p18) (a7p19))) (.branch 0x1f0408888222211110f0000f00040000f (.branch 0x1f008f0004444222211110f0000f0000f (a7p20) (a7p21)) (.branch 0x1f0f0f0008f8844442222111100f0000f (a7p22) (a7p23)))) (.branch 0x1f444f000aaaa222211110f0000f0000f (.branch 0x1f4448888222211110f0000f0000f0001 (.branch 0x1f222aaaa8888444411110f0000f0000f (a7p24) (a7p25)) (.branch 0x1f44488884f44222211110f0000f0000f (a7p26) (a7p27))) (.branch 0x1f88888884f44222211110f0000f0000f (.branch 0x1f8884444222211110f0000f00040000f (a7p28) (a7p29)) (.branch 0x1f888f2228888444411110f0000f0000f (a7p30) (.branch 0x1ff00f4448888222211110f0000f0000f (a7p31) (a7p32))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p0 : r7p0.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p1 : r7p1.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p2 : r7p2.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p3 : r7p3.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p4 : r7p4.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p5 : r7p5.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p6 : r7p6.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p7 : r7p7.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p8 : r7p8.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p9 : r7p9.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p10 : r7p10.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p11 : r7p11.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p12 : r7p12.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p13 : r7p13.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p14 : r7p14.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p15 : r7p15.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p16 : r7p16.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p17 : r7p17.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p18 : r7p18.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p19 : r7p19.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p20 : r7p20.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p21 : r7p21.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p22 : r7p22.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p23 : r7p23.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p24 : r7p24.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p25 : r7p25.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p26 : r7p26.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p27 : r7p27.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p28 : r7p28.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p29 : r7p29.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p30 : r7p30.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p31 : r7p31.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p32 : r7p32.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p33 : r7p33.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p34 : r7p34.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p35 : r7p35.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p36 : r7p36.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p37 : r7p37.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p38 : r7p38.all (checkFast 6 a6) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr7p39 : r7p39.all (checkFast 6 a6) = true := by
  decide +kernel

lemma badR7 : Rejects 7 r7 :=
  verifyFast 6 a6 r7 badA6 (by
    unfold r7
    simp only [allBranch, Bool.and_true, goodr7p0, goodr7p1, goodr7p2, goodr7p3, goodr7p4, goodr7p5, goodr7p6, goodr7p7, goodr7p8, goodr7p9, goodr7p10, goodr7p11, goodr7p12, goodr7p13, goodr7p14, goodr7p15, goodr7p16, goodr7p17, goodr7p18, goodr7p19, goodr7p20, goodr7p21, goodr7p22, goodr7p23, goodr7p24, goodr7p25, goodr7p26, goodr7p27, goodr7p28, goodr7p29, goodr7p30, goodr7p31, goodr7p32, goodr7p33, goodr7p34, goodr7p35, goodr7p36, goodr7p37, goodr7p38, goodr7p39])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p0 : a7p0.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p1 : a7p1.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p2 : a7p2.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p3 : a7p3.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p4 : a7p4.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p5 : a7p5.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p6 : a7p6.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p7 : a7p7.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p8 : a7p8.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p9 : a7p9.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p10 : a7p10.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p11 : a7p11.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p12 : a7p12.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p13 : a7p13.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p14 : a7p14.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p15 : a7p15.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p16 : a7p16.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p17 : a7p17.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p18 : a7p18.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p19 : a7p19.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p20 : a7p20.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p21 : a7p21.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p22 : a7p22.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p23 : a7p23.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p24 : a7p24.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p25 : a7p25.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p26 : a7p26.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p27 : a7p27.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p28 : a7p28.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p29 : a7p29.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p30 : a7p30.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p31 : a7p31.all (checkAlias r7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda7p32 : a7p32.all (checkAlias r7) = true := by
  decide +kernel

lemma badA7 : RejectsAlias 7 a7 :=
  verifyAliases 7 r7 a7 badR7 (by
    unfold a7
    simp only [allBranch, Bool.and_true, gooda7p0, gooda7p1, gooda7p2, gooda7p3, gooda7p4, gooda7p5, gooda7p6, gooda7p7, gooda7p8, gooda7p9, gooda7p10, gooda7p11, gooda7p12, gooda7p13, gooda7p14, gooda7p15, gooda7p16, gooda7p17, gooda7p18, gooda7p19, gooda7p20, gooda7p21, gooda7p22, gooda7p23, gooda7p24, gooda7p25, gooda7p26, gooda7p27, gooda7p28, gooda7p29, gooda7p30, gooda7p31, gooda7p32])
def r8p0 : Keys := .leaf [
0x1f2228888444411110f0000f0000f,0x1f8884444222211110f0000f0000f,0x1f0004444222211110f0000f0000f0008,0x1f00f88884444222211110f0000f0000f]
def r8p1 : Keys := .leaf [
0x1f22288884444222211110f0000f0000f,0x1f222f0008888444411110f0000f0000f,0x1f44488884444222211110f0000f0000f,0x1f00088884444222211110f0000f0000f0001]
def r8p2 : Keys := .leaf [
0x1f00088884444222211110f0000f0000f0004,0x1f00088884444222211110f0000f0000f0008,0x1f00088884444222211110f0000ff00f0000f,0x1f00088884444222211110f00040000f0000f]
def r8p3 : Keys := .leaf [
0x1f00088884444222211110f0f0f0000f0000f,0x1f000888844442222111f11110f0000f0000f,0x1f0008888444422221f1111110f0000f0000f,0x1f000888844442f22222211110f0000f0000f]
def r8p4 : Keys := .leaf [
0x1f00088884f444444222211110f0000f0000f,0x1f000cccc88884444222211110f0000f0000f]
def r8 : Keys := .branch 0x1f00088884444222211110f0000f0000f0004 (.branch 0x1f22288884444222211110f0000f0000f (r8p0) (r8p1)) (.branch 0x1f00088884444222211110f0f0f0000f0000f (r8p2) (.branch 0x1f00088884f444444222211110f0000f0000f (r8p3) (r8p4)))

def a8p0 : Keys := .leaf [
0xf8004444222211110f8880780007a,0xf8004444222791110888878000784,0xf800444427a21111088880780007e,0xf800447c222211110888878000079,0xf80047c422221111088880780007a,0xf9114444222208888780007800078,0xfa22444411110888878000780007c,0xfc442222111108888780007800078,0xc44422221111088888000780007800079,0xf80022221111088887800078000780040,0xf8004444111108888780007800200007d,0xf8004444222211110888810000780007b,0xf8004444222211110888878780780007a,0xf800444422221111088887f800780007f,0xf8004444222211110f88878000780007a,0xf8004444222211110f88888880780007a,0xf8004444222791110888878000780007c,0xf80044442227a22211110888878000784,0xf800444427a211110888878000780007c,0xf800444427a222221111088880780007a,0xf80044442aaa91110888878000780007c,0xf8004444333311110888878000780007e,0xf800447c2222111108888780007800079,0xf800447c4444222211110888878000079,0xf80047c42222111108888780007800079,0xf80047c4444422221111088880780007f,0xf8004ccca222111108888780007800079,0xf8005555222211110888878000780007b,0xf807c4442222111108888780007800078,0xf8784444222211110888878000780007d,0xf91144442222111108888780007800078,0xf91178004444222208888780007800078]
def a8p1 : Keys := .leaf [
0xfa2244442222111108888780007800078,0xfa227800444411110888878000780007e,0xfc444444222211110888878000780007d,0xfc447800222211110888878000780007b,0xf800444422221111088887800078000780008,0xf800444422221111088887800078000780012,0xf800444422221111088887800078000780020,0xf800444422221111088887800078000780040,0xf80044442222111108888780007800080007c,0xf80044442222111108888780007800100007e,0xf80044442222111108888780007800200007d,0xf80044442222111108888780007800400007d,0xf80044442222111108888780007f807800078,0xf800444422221111088887800080007800079,0xf80044442222111108888780010000780007b,0xf800444422221111088887800200007800078,0xf80044442222111108888780040000780007c,0xf800444422221111088887878780007800078,0xf800444422221111088887f8078000780007d,0xf800444422221111088888000780007800079,0xf800444422221111088f88888780007800078,0xf80044442222111108f88888878000780007c,0xf8004444222211110f8888888780007800078,0xf80044442222111110000888878000780007b,0xf80044442222111791110888878000780007a,0xf80044442222117911110888878000780007e,0xf800444422221791111108888780007800078,0xf800444422221999911108888780007800079,0xf80044442222200011110888878000780007a,0xf80044442227a222111108888780007800079,0xf8004444227a2222111108888780007800079,0xf800444427a22222111108888780007800078]
def a8p2 : Keys := .leaf [
0xf80044442aaaa222111108888780007800079,0xf80044443333222211110888878000780007b,0xf80044444000222211110888878000780007e,0xf8004447c444222211110888878000780007c,0xf800447c4444222211110888878000780007c,0xf80047c44444222211110888878000780007c,0xf8004cccc444222211110888878000780007c,0xf80055554444222211110888878000780007e,0xf800666644442222111108888780007800078,0xf807f8004444222211110888878000780007a,0xf87878004444222211110888878000780007f,0xf888f8004444222211110888878000780007a,0xf91178004444222211110888878000780007a,0xfa2278004444222211110888878000780007a,0xfc4478004444222211110888878000780007e,0xff80780044442222111108888780007800079]
def a8 : Keys := .branch 0x1f44488884444222211110f0000f0000f (a8p0) (.branch 0x1f000888855554444222211110f0000f0000f (a8p1) (a8p2))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr8p0 : r8p0.all (checkFast 7 a7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr8p1 : r8p1.all (checkFast 7 a7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr8p2 : r8p2.all (checkFast 7 a7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr8p3 : r8p3.all (checkFast 7 a7) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr8p4 : r8p4.all (checkFast 7 a7) = true := by
  decide +kernel

lemma badR8 : Rejects 8 r8 :=
  verifyFast 7 a7 r8 badA7 (by
    unfold r8
    simp only [allBranch, Bool.and_true, goodr8p0, goodr8p1, goodr8p2, goodr8p3, goodr8p4])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda8p0 : a8p0.all (checkAlias r8) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda8p1 : a8p1.all (checkAlias r8) = true := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda8p2 : a8p2.all (checkAlias r8) = true := by
  decide +kernel

lemma badA8 : RejectsAlias 8 a8 :=
  verifyAliases 8 r8 a8 badR8 (by
    unfold a8
    simp only [allBranch, Bool.and_true, gooda8p0, gooda8p1, gooda8p2])
def r9p0 : Keys := .leaf [
0x1f00088884444222211110f0000f0000f]
def r9 : Keys := r9p0

def a9p0 : Keys := .leaf [
0xf80044442222111108888780007800078]
def a9 : Keys := a9p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma goodr9p0 : r9p0.all (checkFast 8 a8) = true := by
  decide +kernel

lemma badR9 : Rejects 9 r9 :=
  verifyFast 8 a8 r9 badA8 (by
    unfold r9
    simp only [allBranch, Bool.and_true, goodr9p0])
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma gooda9p0 : a9p0.all (checkAlias r9) = true := by
  decide +kernel

lemma badA9 : RejectsAlias 9 a9 :=
  verifyAliases 9 r9 a9 badR9 (by
    unfold a9
    simp only [allBranch, Bool.and_true, gooda9p0])

lemma lower :
    ¬ RepSizeAtMost (fun u v : Fin 4 => (4731 : ℕ).testBit (4*u.val+v.val)) 9 := by
  rintro ⟨C, mono, size, computes⟩
  obtain ⟨k,hk,build⟩ := representsBuild C mono computes
  obtain ⟨W,sub,j,jk,reach⟩ := buildReach build
  rw [allSources W sub (reachSeparates reach)] at reach
  have same : (decodeKey 659299855113181820339880627644369207311).toFinset = sources.toFinset := by decide +kernel
  rw [← same] at reach
  exact badA9 659299855113181820339880627644369207311 (by decide +kernel) j (jk.trans (hk.trans size)) reach

end PEqualNP.Outside.L_meta_21108.Core

theorem PEqualNP.Outside.L_meta_21108 :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) =>
      (35067 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  intro h
  exact PEqualNP.Outside.L_meta_21108.Core.lower
    (PEqualNP.Outside.L_meta_21108.Connection.transfer h)
