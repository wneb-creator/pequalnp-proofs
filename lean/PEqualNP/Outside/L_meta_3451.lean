import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3451.ForestSupport

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

end PEqualNP.Outside.L_meta_3451.ForestSupport

namespace PEqualNP.Outside.L_meta_3451.ForestSupport

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

end PEqualNP.Outside.L_meta_3451.ForestSupport

namespace PEqualNP.Outside.L_meta_3451.ForestSupport

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


def Stat.val (w : List Bool) : (Bool ⊕ ℕ) → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : (Bool ⊕ ℕ) → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
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
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, Stat.Valid w.length s) :
    Stat.Valid (w.length + (simplify op w.length ins).1.toList.length) ((simplify op w.length ins).2) ∧
    Stat.val (wiresFrom (simplify op w.length ins).1.toList w) ((simplify op w.length ins).2)
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

def elimStep (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : (Bool ⊕ ℕ)) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
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

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
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

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : (Bool ⊕ ℕ), Stat.Valid m s → Stat.Valid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : (Bool ⊕ ℕ), Stat.Valid w.length s →
    Stat.val (w ++ t) s = Stat.val w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    Stat.Valid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    Stat.val (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
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
    show Stat.Valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ)) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length = n := by simp
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
      Stat.val (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : Stat.Valid (n + acc.2.length) (acc.1.getD C.output (Sum.inl false)) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
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

end PEqualNP.Outside.L_meta_3451.ForestSupport

namespace PEqualNP.Outside.L_meta_3451.ForestSupport

open PEqualNP.CircuitLowerBounds

lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

lemma simplify_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
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

lemma elimStep_none (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

lemma elimStep_const (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
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
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
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
      Stat.val (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
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

end PEqualNP.Outside.L_meta_3451.ForestSupport

namespace PEqualNP.Outside.L_meta_3451.ForestSupport.PermInputs

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

end PEqualNP.Outside.L_meta_3451.ForestSupport.PermInputs

namespace PEqualNP.Outside.L_meta_3451.ForestSupport.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3451.ForestSupport.PermInputs

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
  have h' := PEqualNP.Outside.L_meta_3451.ForestSupport.gate_elim n _ b s hdep' hnc' hg
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

end PEqualNP.Outside.L_meta_3451.ForestSupport.Forest

namespace PEqualNP.Outside.L_meta_3451.ForestSupport.Forest

open SimpleGraph

lemma exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push Not at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

lemma forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩

    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

end PEqualNP.Outside.L_meta_3451.ForestSupport.Forest

namespace PEqualNP.Outside.L_meta_3451.ForestSupport.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3451.ForestSupport.PermInputs
open SimpleGraph

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

lemma F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

lemma F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

lemma F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

lemma F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp

lemma F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

lemma F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

lemma restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

lemma restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _

  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

lemma cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

lemma cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega

lemma ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)

lemma ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

lemma noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

lemma del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

lemma claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push Not at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push Not at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push Not at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

lemma forest_bound : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsAcyclic → (∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s →
    G.edgeFinset.card + k ≤ s + 1 := by
  intro n k s G _ hac hE hk hC
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  rw [hf] at hC
  have := claimQ _ n G ∅ k s rfl hac (by simp) (fun T hT => hk T hT) (Or.inr hE) hC
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [Finset.card_empty] at this
  omega

end PEqualNP.Outside.L_meta_3451.ForestSupport.Forest


namespace PEqualNP.Outside.L_meta_3451.CleanUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3451.ForestSupport

def Reads (m : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ a ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, a < m + j

def Safe (n m : ℕ) (gs : List Gate) (A : (Fin n → Bool) → Bool) : Prop :=
  ∀ w : List Bool, w.length = m → ∀ j < gs.length,
    (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    (wiresFrom gs w).getD (m + j) false = true → A (fun i => w.getD i false) = true

lemma reads_append (m : ℕ) (gs hs : List Gate) (hg : Reads m gs)
    (hh : Reads (m + gs.length) hs) : Reads m (gs ++ hs) := by
  intro j hj a ha
  by_cases h : j < gs.length
  · rw [List.getD_append _ _ _ _ h] at ha
    exact hg j h a ha
  · rw [List.getD_append_right _ _ _ _ (by omega)] at ha
    have hb := hh (j - gs.length) (by simp at hj; omega) a ha
    omega

lemma safe_append (n m : ℕ) (hm : n ≤ m) (gs hs : List Gate)
    (A : (Fin n → Bool) → Bool) (hg : Safe n m gs A)
    (hh : Safe n (m + gs.length) hs A) : Safe n m (gs ++ hs) A := by
  intro w hw j hj hop hv
  rw [wiresFrom_append] at hv
  by_cases h : j < gs.length
  · rw [List.getD_append _ _ _ _ h] at hop
    rw [getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; omega)] at hv
    exact hg w hw j h hop hv
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hop
    have heq : m + j = m + gs.length + (j - gs.length) := by omega
    rw [heq] at hv
    have ha := hh (wiresFrom gs w) (by rw [length_wiresFrom, hw])
      (j - gs.length) (by simp at hj; omega) hop hv
    have hi : (fun i : Fin n => (wiresFrom gs w).getD i false) =
        (fun i : Fin n => w.getD i false) := by
      funext i
      exact getD_wiresFrom _ _ _ (by rw [hw]; have := i.isLt; omega)
    simpa only [hi] using ha

lemma safe_snoc (n m : ℕ) (gs : List Gate) (g : Gate) (A : (Fin n → Bool) → Bool)
    (hs : Safe n m gs A)
    (hlast : ∀ w : List Bool, w.length = m → g.op = GateOp.and →
      (wiresFrom (gs ++ [g]) w).getD (m + gs.length) false = true →
      A (fun i => w.getD i false) = true) : Safe n m (gs ++ [g]) A := by
  intro w hw j hj hop hv
  by_cases h : j < gs.length
  · rw [List.getD_append _ _ _ _ h] at hop
    rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hw]; omega)] at hv
    exact hs w hw j h hop hv
  · have heq : j = gs.length := by simp at hj; omega
    subst j
    have hg : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp
    rw [hg] at hop
    exact hlast w hw hop hv

def Bld (n : ℕ) (A F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ),
    (∀ g ∈ gs, Ok g) ∧ (∀ g ∈ gs, g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ Reads m gs ∧ Safe n m gs A ∧
    ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {A F : (Fin n → Bool) → Bool} {s s' : ℕ}
    (h : Bld n A F s) (hs : s ≤ s') : Bld n A F s' := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, rb, safe, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, len.trans hs, ho, rb, safe, ev⟩

lemma bld_congr {n : ℕ} {A F H : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld n A F s) (e : ∀ x, F x = H x) : Bld n A H s := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, rb, safe, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, len, ho, rb, safe, fun w hw => by rw [ev w hw, e]⟩

lemma bld_var {n : ℕ} (A : (Fin n → Bool) → Bool) (i : Fin n) :
    Bld n A (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by simp, le_rfl, by simp; omega, ?_, ?_, ?_⟩
  · simp [Reads]
  · simp [Safe]
  · intro w _; simp [wiresFrom]

lemma bld_bin {n : ℕ} (A : (Fin n → Bool) → Bool)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (ha : op = GateOp.and → ∀ x, c (F x) (H x) = true → A x = true)
    (h1 : Bld n A F s1) (h2 : Bld n A H s2) :
    Bld n A (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, nn1, len1, ho1, rb1, sf1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, nn2, len2, ho2, rb2, sf2, ev2⟩ := h2 (m + gs1.length) (by omega)
  have hev (w : List Bool) (hw : w.length = m) :
      (wiresFrom (gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩]) w).getD
        (m + gs1.length + gs2.length) false = c (F (fun i => w.getD i false)) (H (fun i => w.getD i false)) := by
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u =
        u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
    rw [e1, e2]
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length,
    ?_, ?_, ?_, ?_, ?_, ?_, hev⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact nn1 g hg
    · exact nn2 g hg
    · subst hg; rcases hop with h | h <;> simp [h]
  · simp; omega
  · simp; omega
  · apply reads_append
    · exact reads_append m gs1 gs2 rb1 rb2
    · intro j hj a ha'
      have hj0 : j = 0 := by simpa using hj
      subst j
      simp only [List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl <;> simp only [List.length_append, Nat.add_zero] <;> omega
  · apply safe_snoc
    · exact safe_append n m hm gs1 gs2 A sf1 sf2
    · intro w hw hand hv
      have hval := hev w hw
      simp only [List.length_append, ← Nat.add_assoc] at hv
      rw [hval] at hv
      exact ha hand _ hv

lemma bld_or {n : ℕ} {A F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (h1 : Bld n A F s1) (h2 : Bld n A H s2) :
    Bld n A (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin A GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval])
    (by intro h; cases h) h1 h2

lemma bld_and {n : ℕ} {A F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (ha : ∀ x, F x = true → H x = true → A x = true)
    (h1 : Bld n A F s1) (h2 : Bld n A H s2) :
    Bld n A (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin A GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval])
    (by intro _ x hx; simp only [Bool.and_eq_true] at hx; exact ha x hx.1 hx.2) h1 h2

lemma bld_anyList {n : ℕ} (A : (Fin n → Bool) → Bool) (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n A (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var A v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var A v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp


lemma bld_anyFinset {n : ℕ} (A : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n A (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList A vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

lemma bld_edges (n : ℕ) (A : (Fin n → Bool) → Bool) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    (∀ e ∈ E, ∀ x : Fin n → Bool, (∀ v ∈ e, x v = true) → A x = true) →
    Bld n A (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc ha
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc ha
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
    have star : E1.Nonempty → Bld n A (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (by
        intro x hxt hxS
        simp only [decide_eq_true_eq] at hxS
        obtain ⟨v, hv, hxv⟩ := hxS
        have he : s(t, v) ∈ E := (Finset.mem_filter.mp ((Finset.mem_filter.mp hv).2)).1
        exact ha s(t, v) he x (by
          intro u hu
          rcases Sym2.mem_iff.mp hu with rfl | rfl <;> assumption))
        (bld_var A t) (bld_anyFinset A S hSne)
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
      · have := bld_or (star h1) (ih E2 h2 c2 (fun e he => ha e (Finset.mem_filter.mp he).1))
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
      refine bld_congr (bld_mono (ih E2 h2 c2 (fun e he => ha e (Finset.mem_filter.mp he).1)) (by omega)) ?_
      intro x
      rw [key, h1]
      simp



lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

lemma bld_circuit {n : ℕ} {A F : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld n A F s) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ circuitFun n D = F ∧
      D.size ≤ s ∧ (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true → A x = true) := by
  obtain ⟨gs, out, ok, nn, len, _, rb, safe, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ?_, rb, ?_, len, ?_⟩
  · intro g hg
    refine ⟨?_, (ok g hg).2⟩
    rcases (ok g hg).1 with hand | hor | hnot
    · exact Or.inl hand
    · exact Or.inr hor
    · exact (nn g hg hnot).elim
  · funext x
    have e := ev (List.ofFn x) (by simp)
    simp only [circuitFun, Circuit.eval, wires_eq, e]
    congr 1
    funext i
    exact getD_ofFn x i
  · intro j hj hop x hv
    have hs := safe (List.ofFn x) (by simp) j hj hop hv
    simpa only [getD_ofFn] using hs

lemma clean_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hE : ∃ i j : Fin n, G.Adj i j)
    (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧
      circuitFun n D = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ i k : Fin n, G.Adj i k ∧ x i = true ∧ x k = true) := by
  classical
  let A : (Fin n → Bool) → Bool := fun x =>
    decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
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
  have heq (x : Fin n → Bool) :
      decide (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) = A x := by
    change decide _ = decide _
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
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
  have ha : ∀ e ∈ G.edgeFinset, ∀ x : Fin n → Bool,
      (∀ v ∈ e, x v = true) → A x = true := by
    intro e he x hx
    rw [← heq x]
    exact decide_eq_true ⟨e, he, hx⟩
  obtain ⟨D, hm, hr, hv, hs, hsafe⟩ := bld_circuit (bld_edges n A T G.edgeFinset hne cov ha)
  refine ⟨D, hm, hr, ?_, ?_, ?_⟩
  · funext x
    rw [congrFun hv x, heq]
  · have hp := hne.card_pos
    omega
  · intro j hj hop x hx
    have hs := hsafe j hj hop x hx
    exact of_decide_eq_true hs

end PEqualNP.Outside.L_meta_3451.CleanUpper



namespace PEqualNP.Outside.L_meta_3451

lemma edgeless (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  refine ⟨⟨[], N + N⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro z
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.getD_eq_getElem?_getD, hI]
  · simp
  · simp

lemma positive_size (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∃ p l, I p l)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    0 < C.size := by
  by_contra! hsize
  have hnil : C.gates = [] := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using Nat.eq_zero_of_le_zero hsize
  obtain ⟨p, l, hpl⟩ := hI
  have hall : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => true) = true :=
    (hfun _).mpr ⟨p, l, hpl, rfl, rfl⟩
  have hout : C.output < N + N := by
    by_contra! hbound
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil, List.foldl_nil] at hall
    rw [List.getD_eq_default _ _ (by simpa using hbound)] at hall
    cases hall
  let i : Fin (N + N) := ⟨C.output, hout⟩
  let z : Fin (N + N) → Bool := fun k => decide (k = i)
  have hz : PEqualNP.MetaComplexity.circuitFun (N + N) C z = true := by
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil, List.getD_eq_getElem?_getD, hout, z, i]
  obtain ⟨p', l', _, hp', hl'⟩ := (hfun z).mp hz
  simp only [z, decide_eq_true_eq] at hp' hl'
  have heq := congrArg Fin.val (hp'.trans hl'.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
  have hpbound := p'.isLt
  omega

lemma one_point (I : Fin 1 → Fin 1 → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (1 + 1) → Bool,
      PEqualNP.MetaComplexity.circuitFun (1 + 1) C z = true ↔
      ∃ p l : Fin 1, I p l ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (1 + 1) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (1 + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (1 + 1) D z = true ↔ ∃ p l : Fin 1, I p l ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin 1, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (1 + 1) => decide (ke = Fin.castAdd 1 p0 ∨ ke = Fin.natAdd 1 l0)))).getD (1 + 1 + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin 1, (D.wires (List.ofFn (fun kc : Fin (1 + 1) => decide (kc = Fin.castAdd 1 p)))).getD (1 + 1 + j) false = false) ∧ ∀ l : Fin 1, (D.wires (List.ofFn (fun kd : Fin (1 + 1) => decide (kd = Fin.natAdd 1 l)))).getD (1 + 1 + j) false = false) := by
  by_cases hI : I 0 0
  · let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩
    have hIall (p l : Fin 1) : I p l := by
      have hp : p = 0 := Subsingleton.elim _ _
      have hl : l = 0 := Subsingleton.elim _ _
      simpa [hp, hl] using hI
    refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2, D]
    · decide
    · have hsize := positive_size 1 I C ⟨0, 0, hI⟩ hfun
      change 1 ≤ C.size
      omega
    · intro z
      simp [D, PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.ofFn_succ, Fin.exists_fin_one, hIall]
    · intro j hj hop p l hn
      exact (hn (hIall p l)).elim
    · intro j hj _
      have hj0 : j = 0 := by simpa [D] using hj
      subst j
      constructor <;> intro p <;> fin_cases p <;> decide
  · apply edgeless 1 I C
    intro p l
    have hp : p = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    simpa [hp, hl] using hI

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

lemma acyclic_of_one_nonleaf_side {V : Type*} (G : SimpleGraph V)
    (P : V → Prop) (u : V)
    (bip : ∀ a b, G.Adj a b → (P a ↔ ¬ P b))
    (leaf : ∀ a, P a → a ≠ u → ∀ b c, G.Adj a b → G.Adj a c → b = c) :
    G.IsAcyclic := by
  classical
  have center {a : V} (c : G.Walk a a) (hc : c.IsCycle) (ha : P a) : a = u := by
    by_contra hne
    exact hc.snd_ne_penultimate
      (leaf a ha hne c.snd c.penultimate (c.adj_snd hc.not_nil)
        (c.adj_penultimate hc.not_nil).symm)
  have no_right {a : V} (c : G.Walk a a) (hc : c.IsCycle) (ha : ¬ P a) : False := by
    have hs : P c.snd := (bip c.snd a (c.adj_snd hc.not_nil).symm).2 ha
    have ht : P c.penultimate := (bip c.penultimate a (c.adj_penultimate hc.not_nil)).2 ha
    have es : c.snd = u := center (c.rotate c.snd (c.getVert_mem_support 1)) (hc.rotate _) hs
    have et : c.penultimate = u := center
      (c.rotate c.penultimate (c.getVert_mem_support (c.length - 1))) (hc.rotate _) ht
    exact hc.snd_ne_penultimate (es.trans et.symm)
  intro a c hc
  by_cases ha : P a
  · have hs : ¬ P c.snd := (bip a c.snd (c.adj_snd hc.not_nil)).1 ha
    exact no_right (c.rotate c.snd (c.getVert_mem_support 1)) (hc.rotate _) hs
  · exact no_right c hc ha

def incGraph (N : ℕ) (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj a b := ∃ p l : Fin N, I p l ∧
    ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
      (a = Fin.natAdd N l ∧ b = Fin.castAdd N p))
  symm := ⟨by
    rintro a b ⟨p, l, hI, h⟩
    exact ⟨p, l, hI, by tauto⟩⟩
  loopless := ⟨by
    rintro a ⟨p, l, hI, h⟩
    rcases h with ⟨hp, hl⟩ | ⟨hl, hp⟩
    all_goals
      have h := congrArg Fin.val (hp.symm.trans hl)
      have := p.isLt
      change p.val = N + l.val at h
      omega⟩

lemma incGraph_bipartite (N : ℕ) (I : Fin N → Fin N → Prop) :
    ∀ a b, (incGraph N I).Adj a b → (a.val < N ↔ ¬ b.val < N) := by
  rintro a b ⟨p, l, hI, h⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have := p.isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega

lemma incGraph_left_neighbors (N : ℕ) (I : Fin N → Fin N → Prop)
    (p : Fin N) (b : Fin (N + N)) :
    (incGraph N I).Adj (Fin.castAdd N p) b ↔
      ∃ l : Fin N, I p l ∧ b = Fin.natAdd N l := by
  constructor
  · rintro ⟨q, l, hI, h⟩
    rcases h with ⟨h, hb⟩ | ⟨h, hb⟩
    · have hq : p = q := Fin.ext (congrArg (fun x : Fin (N + N) => x.val) h)
      subst q
      exact ⟨l, hI, hb⟩
    · have he := congrArg Fin.val h
      have := p.isLt
      change p.val = N + l.val at he
      omega
  · rintro ⟨l, hI, hb⟩
    exact ⟨p, l, hI, Or.inl ⟨rfl, hb⟩⟩

lemma incGraph_right_neighbors (N : ℕ) (I : Fin N → Fin N → Prop)
    (l : Fin N) (b : Fin (N + N)) :
    (incGraph N I).Adj (Fin.natAdd N l) b ↔
      ∃ p : Fin N, I p l ∧ b = Fin.castAdd N p := by
  constructor
  · rintro ⟨p, q, hI, h⟩
    rcases h with ⟨h, hb⟩ | ⟨h, hb⟩
    · have he := congrArg Fin.val h
      have := p.isLt
      change N + l.val = p.val at he
      omega
    · have he := congrArg Fin.val h
      have hq : l = q := Fin.ext (by simpa using he)
      subst q
      exact ⟨p, hI, hb⟩
  · rintro ⟨p, hI, hb⟩
    exact ⟨p, l, hI, Or.inr ⟨rfl, hb⟩⟩

lemma incGraph_acyclic_of_universal_row (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p0 : Fin N) (hall : ∀ l, I p0 l) : (incGraph N I).IsAcyclic := by
  apply acyclic_of_one_nonleaf_side (incGraph N I) (fun a => a.val < N)
    (Fin.castAdd N p0) (incGraph_bipartite N I)
  intro a ha hne b c hab hac
  let p : Fin N := ⟨a.val, ha⟩
  have he : a = Fin.castAdd N p := Fin.ext rfl
  have hp : p ≠ p0 := by
    intro h
    exact hne (he.trans (congrArg (Fin.castAdd N) h))
  rw [he, incGraph_left_neighbors] at hab hac
  obtain ⟨l, hpl, rfl⟩ := hab
  obtain ⟨l', hpl', rfl⟩ := hac
  have hll : l = l' := by
    by_contra h
    exact hfour p p0 l l' hp h ⟨hpl, hpl', hall l, hall l'⟩
  exact congrArg (Fin.natAdd N) hll

lemma incGraph_acyclic_of_universal_column (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l0 : Fin N) (hall : ∀ p, I p l0) : (incGraph N I).IsAcyclic := by
  have hbip : ∀ a b, (incGraph N I).Adj a b → (N ≤ a.val ↔ ¬ N ≤ b.val) := by
    intro a b hab
    have h := incGraph_bipartite N I a b hab
    omega
  apply acyclic_of_one_nonleaf_side (incGraph N I) (fun a => N ≤ a.val)
    (Fin.natAdd N l0) hbip
  intro a ha hne b c hab hac
  let l : Fin N := ⟨a.val - N, by have := a.isLt; omega⟩
  have he : a = Fin.natAdd N l := Fin.ext (by dsimp [l]; omega)
  have hl : l ≠ l0 := by
    intro h
    exact hne (he.trans (congrArg (Fin.natAdd N) h))
  rw [he, incGraph_right_neighbors] at hab hac
  obtain ⟨p, hpl, rfl⟩ := hab
  obtain ⟨p', hpl', rfl⟩ := hac
  have hpp : p = p' := by
    by_contra h
    exact hfour p p' l l0 h hl ⟨hpl, hall p, hpl', hall p'⟩
  exact congrArg (Fin.castAdd N) hpp

def incGraphDecidable (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    DecidableRel (incGraph N I).Adj := by
  intro a b
  change Decidable (∃ p l : Fin N, I p l ∧
    ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
      (a = Fin.natAdd N l ∧ b = Fin.castAdd N p)))
  infer_instance

lemma incGraph_edge_iff (N : ℕ) (I : Fin N → Fin N → Prop) (z : Fin (N + N) → Bool) :
    (∃ a b : Fin (N + N), (incGraph N I).Adj a b ∧ z a = true ∧ z b = true) ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  constructor
  · rintro ⟨a, b, ⟨p, l, hI, h⟩, ha, hb⟩
    refine ⟨p, l, hI, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨Fin.castAdd N p, Fin.natAdd N l,
      ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩

lemma incGraph_graphFun_iff (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel (incGraph N I).Adj] (z : Fin (N + N) → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (incGraph N I) ∅ z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
  exact incGraph_edge_iff N I z

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

lemma decMinCover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n),
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      ∀ T' : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ T : Finset (Fin n),
    (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ T.card = k
  have hex : ∃ k, P k := ⟨n, Finset.univ, by simp, by simp⟩
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  rw [hcard]
  exact Nat.find_min' hex ⟨T', hT', rfl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma decForestBridge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C)
    (hfun : circuitFun n C =
      (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)))
    (hupper : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
        circuitFun n D =
          (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        D.size + 1 ≤ G.edgeFinset.card + T.card ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
          (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true))
    (hlower : ∀ k s : ℕ,
      (∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      HasCircuitSize n
        (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) s →
      G.edgeFinset.card + k ≤ s + 1) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
      circuitFun n D =
        (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true) := by
  obtain ⟨T, hT, hmin⟩ := decMinCover n G
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨hop, hs⟩ := hC g hg
    refine ⟨?_, hs⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hsmall : HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
      C.size := ⟨C, hfan, le_rfl, fun x => congrFun hfun x⟩
  have hlo := hlower T.card C.size hmin hsmall
  obtain ⟨D, hm, hr, hf, hs, ha⟩ := hupper T hT
  exact ⟨D, hm, hr, by omega, hf, ha⟩

lemma decIncidenceFinish (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hgraph : ∀ z : Fin (N + N) → Bool,
      (∃ i j, G.Adj i j ∧ z i = true ∧ z j = true) ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (C : Circuit)
    (hclean : ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      circuitFun (N + N) D =
        (fun x : Fin (N + N) → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x : Fin (N + N) → Bool,
        (D.wires (List.ofFn x)).getD (N + N + j) false = true →
        ∃ i k, G.Adj i k ∧ x i = true ∧ x k = true)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  obtain ⟨D, hm, hr, hs, hf, ha⟩ := hclean
  refine ⟨D, hm, hr, hs, ?_, ?_, ?_⟩
  · intro z
    rw [hf, decide_eq_true_iff]
    exact hgraph z
  · intro j hj hand p0 l0 hnon
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨p, l, hil, hp, hl⟩ := (hgraph _).mp (ha j hj hand _ ht)
    have hpp : p = p0 := by
      rcases of_decide_eq_true hp with h | h
      · apply Fin.ext
        exact congrArg (fun k : Fin (N + N) => k.val) h
      · have hh := congrArg (fun k : Fin (N + N) => k.val) h
        change p.val = N + l0.val at hh
        omega
    have hll : l = l0 := by
      rcases of_decide_eq_true hl with h | h
      · have hh := congrArg (fun k : Fin (N + N) => k.val) h
        change N + l.val = p0.val at hh
        omega
      · apply Fin.ext
        have hh := congrArg (fun k : Fin (N + N) => k.val) h
        change N + l.val = N + l0.val at hh
        omega
    exact hnon (hpp ▸ hll ▸ hil)
  · intro j hj hand
    constructor
    · intro p0
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨p, l, _, _, hl⟩ := (hgraph _).mp (ha j hj hand _ ht)
      have hh := congrArg (fun k : Fin (N + N) => k.val) (of_decide_eq_true hl)
      change N + l.val = p0.val at hh
      omega
    · intro l0
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨p, l, _, hp, _⟩ := (hgraph _).mp (ha j hj hand _ ht)
      have hh := congrArg (fun k : Fin (N + N) => k.val) (of_decide_eq_true hp)
      change p.val = N + l0.val at hh
      omega

end PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

lemma acyclic_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hac : (incGraph N I).IsAcyclic)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  by_cases hedge : ∃ p l : Fin N, I p l
  · letI : DecidableRel (incGraph N I).Adj := incGraphDecidable N I
    have hE : ∃ i j : Fin (N + N), (incGraph N I).Adj i j := by
      obtain ⟨p, l, hpl⟩ := hedge
      exact ⟨Fin.castAdd N p, Fin.natAdd N l, p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
    have hf : PEqualNP.MetaComplexity.circuitFun (N + N) C =
        (fun z : Fin (N + N) → Bool =>
          decide (∃ i j, (incGraph N I).Adj i j ∧ z i = true ∧ z j = true)) := by
      funext z
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact (hfun z).trans (incGraph_edge_iff N I z).symm
    apply decIncidenceFinish N I (incGraph N I) (incGraph_edge_iff N I) C
    exact decForestBridge (N + N) (incGraph N I) C hmono hf
      (fun T hT => CleanUpper.clean_upper (N + N) (incGraph N I) T hE hT)
      (fun k s hk hc => ForestSupport.Forest.forest_bound (N + N) k s (incGraph N I)
        hac hE hk hc)
  · apply edgeless N I C
    intro p l hp
    exact hedge ⟨p, l, hp⟩

lemma universal_row (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p0 : Fin N) (hall : ∀ l, I p0 l)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) :=
  acyclic_incidence N I C (incGraph_acyclic_of_universal_row N I hfour p0 hall) hmono hfun

lemma universal_column (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l0 : Fin N) (hall : ∀ p, I p l0)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) :=
  acyclic_incidence N I C (incGraph_acyclic_of_universal_column N I hfour l0 hall) hmono hfun



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def decStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma decEvalMono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma decFoldMono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl decStep a).getD i false = true →
        (gs.foldl decStep b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [decStep, hl]
    · intro i hi
      unfold decStep at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact decEvalMono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma decWireMono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  refine decFoldMono C.gates (fun g hg => (hC g hg).1) _ _ (by simp) ?_ w
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma decSingletonPoint (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : Monotone2 C) (j : ℕ) (p : Fin N)
    (hp : ∃ l, ¬ I p l)
    (hpair : ∀ l, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false := by
  obtain ⟨l, hl⟩ := hp
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := decWireMono (N + N) C hC
    (fun k => decide (k = Fin.castAdd N p))
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
    (by intro k hk; exact decide_eq_true_iff.mpr (Or.inl (of_decide_eq_true hk)))
    (N + N + j) ht
  rw [hpair l hl] at hm
  cases hm

lemma decSingletonLine (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : Monotone2 C) (j : ℕ) (l : Fin N)
    (hl : ∃ p, ¬ I p l)
    (hpair : ∀ p, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  obtain ⟨p, hp⟩ := hl
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := decWireMono (N + N) C hC
    (fun k => decide (k = Fin.natAdd N l))
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
    (by intro k hk; exact decide_eq_true_iff.mpr (Or.inr (of_decide_eq_true hk)))
    (N + N + j) ht
  rw [hpair p hp] at hm
  cases hm

lemma decAndSingletons (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : Circuit) (hD : Monotone2 D)
    (hp : ∀ p, ∃ l, ¬ I p l) (hl : ∀ l, ∃ p, ¬ I p l)
    (hpair : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ p l : Fin N, ¬ I p l →
      (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  intro j hj ha
  constructor
  · intro p
    exact decSingletonPoint N I D hD j p (hp p) (hpair j hj ha p)
  · intro l
    exact decSingletonLine N I D hD j l (hl l) (fun p h => hpair j hj ha p l h)

lemma decFinish (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hp : ∀ p, ∃ l, ¬ I p l) (hl : ∀ l, ∃ p, ¬ I p l)
    (hclean : ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  obtain ⟨D, hm, hr, hs, hf, hpair⟩ := hclean
  exact ⟨D, hm, hr, hs, hf, hpair, decAndSingletons N I D hm hp hl hpair⟩

lemma decUniversalPointDegree (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p : Fin N) (hp : ∀ l, I p l) (q : Fin N) (hq : q ≠ p)
    (l l' : Fin N) (hl : I q l) (hl' : I q l') : l = l' := by
  by_contra hne
  exact hfour p q l l' (Ne.symm hq) hne ⟨hp l, hp l', hl, hl'⟩

lemma decUniversalLineDegree (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l : Fin N) (hl : ∀ p, I p l) (k : Fin N) (hk : k ≠ l)
    (p p' : Fin N) (hp : I p k) (hp' : I p' k) : p = p' := by
  by_contra hne
  exact hfour p p' l k hne (Ne.symm hk) ⟨hl p, hp, hl p', hp'⟩



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def zResWire {m n : ℕ} (r : Fin m → Option (Fin n)) (i : ℕ) : Option ℕ :=
  if hi : i < m then (r ⟨i, hi⟩).map Fin.val else some (n + (i - m))

def zResGate (ρ : ℕ → Option ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.any (fun i => (ρ i).isNone) then ⟨.or, []⟩
      else ⟨.and, g.inputs.filterMap ρ⟩
  | op => ⟨op, g.inputs.filterMap ρ⟩

def zResCircuit {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (zResGate (zResWire r)), (zResWire r C.output).getD (n + C.size)⟩

def zResInput {m n : ℕ} (r : Fin m → Option (Fin n)) (z : Fin n → Bool) : Fin m → Bool :=
  fun i => (r i).elim false z

lemma zRes_size {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) :
    (zResCircuit r C).size = C.size := by
  simp [zResCircuit, Circuit.size]

lemma zRes_gate_mono (ρ : ℕ → Option ℕ) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    ((zResGate ρ g).op = .and ∨ (zResGate ρ g).op = .or) ∧
      (zResGate ρ g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  · simp only [zResGate]
    split
    · simp
    · exact ⟨Or.inl rfl, (List.length_filterMap_le ρ ins).trans hlen⟩
  · exact ⟨Or.inr rfl, (List.length_filterMap_le ρ ins).trans hlen⟩

lemma zRes_monotone {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) : Monotone2 (zResCircuit r C) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact zRes_gate_mono _ _ (hC g₀ hg₀).1 (hC g₀ hg₀).2

lemma zRes_gate_eval (ρ : ℕ → Option ℕ) (g : Gate) (a b : ℕ → Bool)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (hval : ∀ i, (ρ i).elim false b = a i) :
    (zResGate ρ g).op.eval ((zResGate ρ g).inputs.map b) =
      g.op.eval (g.inputs.map a) := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ins⟩⟩⟩
    · simp [zResGate, GateOp.eval]
    · specialize hval i
      cases hρ : ρ i <;> simp_all [zResGate, GateOp.eval]
    · have hi := hval i
      have hj := hval j
      cases hρi : ρ i <;> cases hρj : ρ j <;> simp_all [zResGate, GateOp.eval]
    · simp at hlen

lemma zRes_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = w.length
    · subst i; simp
    · rw [if_neg he, List.getD_eq_default w false (by omega),
        List.getD_eq_default [v] false (by simp; omega)]

lemma zRes_wire_gate {m n : ℕ} (r : Fin m → Option (Fin n)) (j : ℕ) :
    zResWire r (m + j) = some (n + j) := by
  simp [zResWire]

lemma zRes_step_rel {m n : ℕ} (r : Fin m → Option (Fin n))
    (a b : List Bool) (k : ℕ) (ha : a.length = m + k) (hb : b.length = n + k)
    (hv : ∀ i, (zResWire r i).elim false (fun j => b.getD j false) = a.getD i false)
    (v : Bool) :
    ∀ i, (zResWire r i).elim false (fun j => (b ++ [v]).getD j false) =
      (a ++ [v]).getD i false := by
  intro i
  have hv_i := hv i
  rw [zRes_snoc, ha]
  by_cases hi : i < m
  · have he : i ≠ m + k := by omega
    rw [if_neg he]
    rw [zResWire, dif_pos hi] at hv_i ⊢
    cases hri : r ⟨i, hi⟩ with
    | none => simpa [hri] using hv_i
    | some j =>
      have hj : j.val < b.length := by rw [hb]; omega
      simp only [hri, Option.map_some, Option.elim_some] at hv_i ⊢
      rw [List.getD_append _ _ _ _ hj]
      exact hv_i
  · rw [zResWire, dif_neg hi] at hv_i ⊢
    simp only [Option.elim_some]
    rw [zRes_snoc, hb]
    by_cases he : i = m + k
    · subst i; simp
    · have he' : n + (i - m) ≠ n + k := by omega
      rw [if_neg he, if_neg he']
      simpa [zResWire, hi] using hv_i

lemma zRes_fold_rel {m n : ℕ} (r : Fin m → Option (Fin n)) (gs : List Gate) :
    ∀ (a b : List Bool) (k : ℕ), a.length = m + k → b.length = n + k →
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
      (∀ i, (zResWire r i).elim false (fun j => b.getD j false) = a.getD i false) →
      ∀ i, (zResWire r i).elim false (fun j =>
        ((gs.map (zResGate (zResWire r))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) b).getD j false) =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) a).getD i false := by
  induction gs with
  | nil => intro a b k ha hb hgs hv i; exact hv i
  | cons g gs ih =>
    intro a b k ha hb hgs hv
    have hg := hgs g (by simp)
    have he := zRes_gate_eval (zResWire r) g (fun i => a.getD i false)
      (fun i => b.getD i false) hg.1 hg.2 hv
    simp only [List.map_cons, List.foldl_cons, he]
    apply ih _ _ (k + 1)
    · simp [ha]; omega
    · simp [hb]; omega
    · intro g' hg'; exact hgs g' (by simp [hg'])
    · exact zRes_step_rel r a b k ha hb hv _

lemma zRes_input_rel {m n : ℕ} (r : Fin m → Option (Fin n)) (z : Fin n → Bool) (i : ℕ) :
    (zResWire r i).elim false (fun j => (List.ofFn z).getD j false) =
      (List.ofFn (zResInput r z)).getD i false := by
  by_cases hi : i < m
  · simp only [zResWire, dif_pos hi]
    rw [List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn, zResInput]
    cases hr : r ⟨i, hi⟩ with
    | none => rfl
    | some j => simp [j.isLt]
  · simp [zResWire, hi, List.getD_eq_default, zResInput]

lemma zRes_wires {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) (i : ℕ) :
    (zResWire r i).elim false (fun j => ((zResCircuit r C).wires (List.ofFn z)).getD j false) =
      (C.wires (List.ofFn (zResInput r z))).getD i false := by
  exact zRes_fold_rel r C.gates _ _ 0 (by simp) (by simp) hC
    (zRes_input_rel r z) i

lemma zRes_wires_gate {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) (j : ℕ) :
    ((zResCircuit r C).wires (List.ofFn z)).getD (n + j) false =
      (C.wires (List.ofFn (zResInput r z))).getD (m + j) false := by
  simpa [zRes_wire_gate] using zRes_wires r C hC z (m + j)

lemma zRes_gateAt {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ) :
    gateAt (zResCircuit r C) j = zResGate (zResWire r) (gateAt C j) := by
  have he : zResGate (zResWire r) ⟨.or, []⟩ = ⟨.or, []⟩ := rfl
  unfold gateAt zResCircuit
  change (C.gates.map (zResGate (zResWire r))).getD j _ = _
  simpa only [he] using List.getD_map (n := j) C.gates ⟨GateOp.or, []⟩
    (zResGate (zResWire r))

lemma zRes_inputs (ρ : ℕ → Option ℕ) (g : Gate) (i : ℕ)
    (hi : i ∈ (zResGate ρ g).inputs) : ∃ j ∈ g.inputs, ρ j = some i := by
  cases g with
  | mk op ins =>
    cases op <;> simp only [zResGate] at hi
    · split at hi
      · simp at hi
      · exact List.mem_filterMap.mp hi
    all_goals exact List.mem_filterMap.mp hi

lemma zRes_wire_lt {m n : ℕ} (r : Fin m → Option (Fin n)) (i j k : ℕ)
    (hi : i < m + k) (hr : zResWire r i = some j) : j < n + k := by
  by_cases him : i < m
  · simp only [zResWire, dif_pos him] at hr
    cases he : r ⟨i, him⟩ with
    | none => simp [he] at hr
    | some t => simp [he] at hr; subst j; omega
  · simp only [zResWire, dif_neg him, Option.some.injEq] at hr
    omega

lemma zRes_readsBack {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : ReadsBack m C) : ReadsBack n (zResCircuit r C) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [zResCircuit] using hj
  rw [zRes_gateAt] at hi
  obtain ⟨k, hk, hki⟩ := zRes_inputs _ _ _ hi
  exact zRes_wire_lt r k i j (hC j hj' k hk) hki

lemma zRes_and_source (ρ : ℕ → Option ℕ) (g : Gate)
    (h : (zResGate ρ g).op = .and) : g.op = .and := by
  cases g with
  | mk op ins =>
    cases op <;> simp_all [zResGate]

lemma zRes_and_wire {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (j : ℕ) (hj : (gateAt (zResCircuit r C) j).op = .and)
    (z : Fin n → Bool) :
    (gateAt C j).op = .and ∧
      ((zResCircuit r C).wires (List.ofFn z)).getD (n + j) false =
        (C.wires (List.ofFn (zResInput r z))).getD (m + j) false := by
  rw [zRes_gateAt] at hj
  exact ⟨zRes_and_source _ _ hj, zRes_wires_gate r C hC z j⟩

lemma zRes_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  have hf : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp; omega
  exact hf C.gates x

lemma zRes_eval {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) :
    circuitFun n (zResCircuit r C) z = circuitFun m C (zResInput r z) := by
  have hv := zRes_wires r C hC z C.output
  change ((zResCircuit r C).wires (List.ofFn z)).getD
      ((zResWire r C.output).getD (n + C.size)) false = _
  cases hr : zResWire r C.output with
  | none =>
    simp only [hr, Option.elim_none] at hv
    rw [Option.getD_none, List.getD_eq_default _ false (by
      rw [zRes_wires_length]
      simp [zResCircuit, Circuit.size])]
    exact hv
  | some j => simpa [hr, circuitFun, Circuit.eval] using hv


def padI {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin (N + 1)) : Prop :=
  ∃ a b : Fin N, p = a.castSucc ∧ l = b.castSucc ∧ I a b

def padLift {N : ℕ} : Fin (N + N) → Option (Fin ((N + 1) + (N + 1))) :=
  Fin.addCases (fun p => some (Fin.castAdd (N + 1) p.castSucc))
    (fun l => some (Fin.natAdd (N + 1) l.castSucc))

def padDrop {N : ℕ} : Fin ((N + 1) + (N + 1)) → Option (Fin (N + N)) :=
  Fin.addCases (Fin.lastCases none (fun p => some (Fin.castAdd N p)))
    (Fin.lastCases none (fun l => some (Fin.natAdd N l)))

lemma padI_cast {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    padI I p.castSucc l.castSucc ↔ I p l := by
  simp [padI]

lemma padI_point_last {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin (N + 1)) :
    ¬ padI I (Fin.last N) l := by
  rintro ⟨a, b, h, _, _⟩
  have := congrArg Fin.val h
  simp at this
  omega

lemma padI_line_last {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin (N + 1)) :
    ¬ padI I p (Fin.last N) := by
  rintro ⟨a, b, _, h, _⟩
  have := congrArg Fin.val h
  simp at this
  omega

lemma padI_noRect {N : ℕ} (I : Fin N → Fin N → Prop)
    (h : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∀ p p' l l' : Fin (N + 1), p ≠ p' → l ≠ l' →
      ¬ (padI I p l ∧ padI I p l' ∧ padI I p' l ∧ padI I p' l') := by
  rintro p p' l l' hpp hll ⟨⟨a, b, rfl, rfl, hab⟩, h1, h2, h3⟩
  obtain ⟨a', d, ha', rfl, had⟩ := h1
  have haa : a = a' := Fin.castSucc_injective N ha'
  subst a'
  obtain ⟨c, b', rfl, hb', hcb⟩ := h2
  have hbb : b = b' := Fin.castSucc_injective N hb'
  subst b'
  have hcd := (padI_cast I c d).mp h3
  exact h a c b d (fun e => hpp (congrArg Fin.castSucc e))
    (fun e => hll (congrArg Fin.castSucc e)) ⟨hab, had, hcb, hcd⟩

lemma padLift_input_point {N : ℕ} (z : Fin ((N + 1) + (N + 1)) → Bool) (p : Fin N) :
    zResInput padLift z (Fin.castAdd N p) = z (Fin.castAdd (N + 1) p.castSucc) := by
  simp only [zResInput, padLift, Fin.addCases_left, Fin.addCases_right, Option.elim_some]

lemma padLift_input_line {N : ℕ} (z : Fin ((N + 1) + (N + 1)) → Bool) (l : Fin N) :
    zResInput padLift z (Fin.natAdd N l) = z (Fin.natAdd (N + 1) l.castSucc) := by
  simp only [zResInput, padLift, Fin.addCases_left, Fin.addCases_right, Option.elim_some]

lemma padDrop_input_point {N : ℕ} (z : Fin (N + N) → Bool) (p : Fin N) :
    zResInput padDrop z (Fin.castAdd (N + 1) p.castSucc) = z (Fin.castAdd N p) := by
  simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc, Option.elim_some]

lemma padDrop_input_line {N : ℕ} (z : Fin (N + N) → Bool) (l : Fin N) :
    zResInput padDrop z (Fin.natAdd (N + 1) l.castSucc) = z (Fin.natAdd N l) := by
  simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc, Option.elim_some]

lemma padLift_computes {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (hf : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) (zResCircuit (padLift (N := N)) C) z = true ↔
      ∃ p l : Fin (N + 1), padI I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true := by
  intro z
  rw [zRes_eval _ _ hC, hf]
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    exact ⟨p.castSucc, l.castSucc, (padI_cast I p l).mpr hpl,
      by simpa only [padLift_input_point] using hp, by simpa only [padLift_input_line] using hl⟩
  · rintro ⟨p, l, ⟨a, b, rfl, rfl, hab⟩, hp, hl⟩
    exact ⟨a, b, hab, by simpa only [padLift_input_point] using hp,
      by simpa only [padLift_input_line] using hl⟩

lemma padDrop_computes {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (hf : ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) C z = true ↔
      ∃ p l : Fin (N + 1), padI I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) (zResCircuit (padDrop (N := N)) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [zRes_eval _ _ hC, hf]
  constructor
  · rintro ⟨p, l, ⟨a, b, rfl, rfl, hab⟩, hp, hl⟩
    exact ⟨a, b, hab, by simpa only [padDrop_input_point] using hp,
      by simpa only [padDrop_input_line] using hl⟩
  · rintro ⟨a, b, hab, hp, hl⟩
    exact ⟨a.castSucc, b.castSucc, (padI_cast I a b).mpr hab,
      by simpa only [padDrop_input_point] using hp, by simpa only [padDrop_input_line] using hl⟩

lemma padDrop_pair {N : ℕ} (p l : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) =
      (fun k : Fin ((N + 1) + (N + 1)) =>
        decide (k = Fin.castAdd (N + 1) p.castSucc ∨ k = Fin.natAdd (N + 1) l.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padDrop_point {N : ℕ} (p : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)) =
      (fun k : Fin ((N + 1) + (N + 1)) => decide (k = Fin.castAdd (N + 1) p.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padDrop_line {N : ℕ} (l : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)) =
      (fun k : Fin ((N + 1) + (N + 1)) => decide (k = Fin.natAdd (N + 1) l.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padSuffices (hclean : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C hfour hC hrC hfC
  classical
  let C' := zResCircuit (padLift (N := N)) C
  have hC' : Monotone2 C' := zRes_monotone _ _ hC
  have hrC' : ReadsBack ((N + 1) + (N + 1)) C' := zRes_readsBack _ _ hrC
  have hfC' := padLift_computes I C hC hfC
  obtain ⟨D, hD, hrD, hsD, hfD, hpD⟩ :=
    hclean (N + 1) (padI I) C' (padI_noRect I hfour) hC' hrC' hfC'
  have hsingle := decAndSingletons (N + 1) (padI I) D hD
    (fun p => ⟨Fin.last N, padI_line_last I p⟩)
    (fun l => ⟨Fin.last N, padI_point_last I l⟩) hpD
  let E := zResCircuit (padDrop (N := N)) D
  refine ⟨E, zRes_monotone _ _ hD, zRes_readsBack _ _ hrD, ?_,
    padDrop_computes I D hD hfD, ?_, ?_⟩
  · simpa only [E, C', zRes_size] using hsD
  · intro j hj hand p l hpl
    have hj' : j < D.gates.length := by simpa [E, zResCircuit] using hj
    have hand' : (gateAt D j).op = .and :=
      zRes_and_source _ _ (by simpa only [E, zRes_gateAt] using hand)
    change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
    rw [zRes_wires_gate _ _ hD, padDrop_pair]
    exact hpD j hj' hand' p.castSucc l.castSucc (fun h => hpl ((padI_cast I p l).mp h))
  · intro j hj hand
    have hj' : j < D.gates.length := by simpa [E, zResCircuit] using hj
    have hand' : (gateAt D j).op = .and :=
      zRes_and_source _ _ (by simpa only [E, zRes_gateAt] using hand)
    constructor
    · intro p
      change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
      rw [zRes_wires_gate _ _ hD, padDrop_point]
      exact (hsingle j hj' hand').1 p.castSucc
    · intro l
      change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
      rw [zRes_wires_gate _ _ hD, padDrop_line]
      exact (hsingle j hj' hand').2 l.castSucc


lemma lcFoldPrefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl decStep w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (decStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [decStep]

lemma lcLength (gs : List Gate) (w : List Bool) :
    (gs.foldl decStep w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := lcFoldPrefix gs w
  rw [ht]; simp [hl]

lemma lcRead (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl decStep w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := lcFoldPrefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma lcGateValue (pre post : List Gate) (g : Gate) (w : List Bool) :
    ((pre ++ g :: post).foldl decStep w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep w).getD i false) := by
  rw [List.foldl_append, List.foldl_cons]
  rw [lcRead _ _ _ (by simp [decStep, lcLength])]
  change ((pre.foldl decStep w) ++
    [g.op.eval (g.inputs.map fun i => (pre.foldl decStep w).getD i false)]).getD
      (w.length + pre.length) false = _
  rw [← lcLength pre w]
  simp

lemma lcSnocMono (w : List Bool) (a b : Bool) (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (w ++ [b]).getD i false = true := by
  intro i hi
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h] at hi ⊢
    exact hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    cases he : i - w.length with
    | zero => simpa [he] using hab (by simpa [he] using hi)
    | succ k => simp [he] at hi

lemma lcGetDReplace (pre post : List Gate) (g r d : Gate) (k : ℕ)
    (hk : k ≠ pre.length) : (pre ++ r :: post).getD k d = (pre ++ g :: post).getD k d := by
  by_cases h : k < pre.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨a, ha⟩ : ∃ a, k - pre.length = a + 1 := ⟨k - pre.length - 1, by omega⟩
    simp [ha]

def lcPair (N : ℕ) (p l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)

lemma lcPairLe (N : ℕ) (p l : Fin N) (z : Fin (N + N) → Bool)
    (hp : z (Fin.castAdd N p) = true) (hl : z (Fin.natAdd N l) = true) :
    ∀ k, lcPair N p l k = true → z k = true := by
  intro k hk
  rcases of_decide_eq_true hk with rfl | rfl <;> assumption

lemma lcPairTrue (N : ℕ) (p l : Fin N) :
    lcPair N p l (Fin.castAdd N p) = true ∧ lcPair N p l (Fin.natAdd N l) = true := by
  simp [lcPair]

lemma lcPairCompleteness (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hD : Monotone2 D)
    (hle : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) D z = true → circuitFun (N + N) C z = true)
    (heq : ∀ p l : Fin N, I p l →
      circuitFun (N + N) D (lcPair N p l) = circuitFun (N + N) C (lcPair N p l)) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  constructor
  · intro hz
    exact (hC z).mp (hle z hz)
  · rintro ⟨p, l, hpl, hp, hl⟩
    have hpair : circuitFun (N + N) D (lcPair N p l) = true := by
      rw [heq p l hpl]
      exact (hC _).mpr ⟨p, l, hpl, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩
    exact decWireMono (N + N) D hD _ z (lcPairLe N p l z hp hl) D.output hpair

lemma lcReplacement (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g r : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrsize : r.inputs.length ≤ 2)
    (hrread : ∀ a ∈ r.inputs, a < N + N + pre.length)
    (hrle : ∀ z : Fin (N + N) → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true)
    (hreq : ∀ p l : Fin N, I p l →
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn (lcPair N p l))).getD i false) =
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn (lcPair N p l))).getD i false)) :
    let D : Circuit := ⟨pre ++ r :: post, C.output⟩
    Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
      (∀ z : Fin (N + N) → Bool, ∀ i,
        (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true) ∧
      (∀ p l : Fin N, I p l → D.wires (List.ofFn (lcPair N p l)) = C.wires (List.ofFn (lcPair N p l))) ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  intro D
  have hm : Monotone2 D := by
    intro a ha
    change a ∈ pre ++ r :: post at ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hmono a (by rw [hsplit]; simp [ha])
    · exact ⟨hrop, hrsize⟩
    · exact hmono a (by rw [hsplit]; simp [ha])
  have hr : ReadsBack (N + N) D := by
    intro k hk a ha
    by_cases he : k = pre.length
    · subst k
      have har : a ∈ r.inputs := by simpa [gateAt, D] using ha
      exact hrread a har
    · have hg := lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k he
      have hak : a ∈ (gateAt C k).inputs := by
        change a ∈ ((pre ++ r :: post).getD k ⟨GateOp.or, []⟩).inputs at ha
        rw [hg] at ha
        simpa only [gateAt, hsplit] using ha
      exact hreads k (by simpa [hsplit, D] using hk) a hak
  have hle : ∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true := by
    intro z
    change ∀ i, ((pre ++ r :: post).foldl decStep (List.ofFn z)).getD i false = true →
      (C.gates.foldl decStep (List.ofFn z)).getD i false = true
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply decFoldMono post (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1)
    · simp [decStep]
    · exact lcSnocMono _ _ _ (hrle z)
  have heq : ∀ p l : Fin N, I p l →
      D.wires (List.ofFn (lcPair N p l)) = C.wires (List.ofFn (lcPair N p l)) := by
    intro p l hpl
    change (pre ++ r :: post).foldl decStep _ = C.gates.foldl decStep _
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    simp only [decStep, hreq p l hpl]
  refine ⟨hm, hr, by simp [Circuit.size, hsplit, D], hle, heq, ?_⟩
  apply lcPairCompleteness N I C D hfun hm (fun z => hle z C.output)
  intro p l hpl
  exact congrArg (fun ws : List Bool => ws.getD C.output false) (heq p l hpl)


def lcImproves (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit) : Prop :=
  Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
    (∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true) ∧
    (∀ p l : Fin N, I p l → D.wires (List.ofFn (lcPair N p l)) = C.wires (List.ofFn (lcPair N p l))) ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

lemma lcCircuitGate (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post) (z : Fin n → Bool) :
    (C.wires (List.ofFn z)).getD (n + pre.length) false =
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) := by
  change (C.gates.foldl decStep (List.ofFn z)).getD (n + pre.length) false = _
  rw [hsplit]
  simpa only [List.length_ofFn] using lcGateValue pre post g (List.ofFn z)

lemma lcZeroSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hnone : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = false) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (gateAt D pre.length).op = GateOp.or ∧
      (∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + pre.length) false = false) := by
  let r : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · exact lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
      (by simp [r]) (by simp [r]) (by simp [r, GateOp.eval]) (by
        intro p l hpl
        rw [← lcCircuitGate (N + N) C pre post g hsplit, hnone p l hpl]
        rfl)
  · simp [gateAt, D, r]
  · intro z
    rw [lcCircuitGate (N + N) D pre post r rfl]
    rfl

lemma lcPairPoint (N : ℕ) (p l p' : Fin N) :
    lcPair N p l (Fin.castAdd N p') = true ↔ p' = p := by
  have hcross : Fin.castAdd N p' ≠ Fin.natAdd N l := by
    intro h
    have hh := congrArg Fin.val h
    change p'.val = N + l.val at hh
    omega
  constructor
  · intro hx
    rcases of_decide_eq_true hx with h | h
    · exact Fin.ext (congrArg (fun k : Fin (N + N) => k.val) h)
    · exact (hcross h).elim
  · intro h; subst p'; exact decide_eq_true (Or.inl rfl)

lemma lcPairLine (N : ℕ) (p l l' : Fin N) :
    lcPair N p l (Fin.natAdd N l') = true ↔ l' = l := by
  have hcross : Fin.natAdd N l' ≠ Fin.castAdd N p := by
    intro h
    have hh := congrArg Fin.val h
    change N + l'.val = p.val at hh
    omega
  constructor
  · intro hx
    rcases of_decide_eq_true hx with h | h
    · exact (hcross h).elim
    · apply Fin.ext
      have hh := congrArg (fun k : Fin (N + N) => k.val) h
      change N + l'.val = N + l.val at hh
      omega
  · intro h; subst l'; exact decide_eq_true (Or.inr rfl)

lemma lcGetDOfFn {n : ℕ} (z : Fin n → Bool) (i : Fin n) :
    (List.ofFn z).getD i.val false = z i := by simp

lemma lcRawPairEval (N : ℕ) (pre : List Gate) (p l : Fin N) (z : Fin (N + N) → Bool) :
    GateOp.and.eval ([p.val, N + l.val].map fun i =>
      (pre.foldl decStep (List.ofFn z)).getD i false) =
      (z (Fin.castAdd N p) && z (Fin.natAdd N l)) := by
  have hp : (pre.foldl decStep (List.ofFn z)).getD p.val false = z (Fin.castAdd N p) := by
    rw [lcRead _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact lcGetDOfFn z (Fin.castAdd N p)
  have hl : (pre.foldl decStep (List.ofFn z)).getD (N + l.val) false = z (Fin.natAdd N l) := by
    rw [lcRead _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact lcGetDOfFn z (Fin.natAdd N l)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [hp, hl]

lemma lcOneSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 l0 : Fin N) (hI : I p0 l0)
    (haccept : (C.wires (List.ofFn (lcPair N p0 l0))).getD (N + N + pre.length) false = true)
    (honly : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true →
        p = p0 ∧ l = l0) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  let r : Gate := ⟨GateOp.and, [p0.val, N + l0.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · apply lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · intro z hz
      change GateOp.and.eval _ = true at hz
      rw [lcRawPairEval] at hz
      simp only [Bool.and_eq_true] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l0 z hz.1 hz.2)
        (N + N + pre.length) haccept
    · intro p l hpl
      change GateOp.and.eval _ = _
      rw [lcRawPairEval, ← lcCircuitGate (N + N) C pre post g hsplit,
        Bool.eq_iff_iff, Bool.and_eq_true, lcPairPoint, lcPairLine]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact haccept
      · intro ht
        obtain ⟨hp, hl⟩ := honly p l hpl ht
        exact ⟨hp.symm, hl.symm⟩
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcRawPairEval] at hz
    simp only [Bool.and_eq_true] at hz
    exact ⟨p0, l0, hI, hz.1, hz.2⟩



lemma mdReplacementShape (C : Circuit) (pre post : List Gate) (g r : Gate)
    (hsplit : C.gates = pre ++ g :: post) :
    ∀ k, k ≠ pre.length →
      gateAt (⟨pre ++ r :: post, C.output⟩ : Circuit) k = gateAt C k := by
  intro k hk
  change (pre ++ r :: post).getD k ⟨GateOp.or, []⟩ = C.gates.getD k ⟨GateOp.or, []⟩
  rw [hsplit]
  exact lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k hk

lemma mdZeroSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hnone : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = false) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.or ∧
      (∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + pre.length) false = false) := by
  let r : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
      (by simp [r]) (by simp [r]) (by simp [r, GateOp.eval]) (by
        intro p l hpl
        rw [← lcCircuitGate (N + N) C pre post g hsplit, hnone p l hpl]
        rfl)
  · exact mdReplacementShape C pre post g r hsplit
  · simp [gateAt, D, r]
  · intro z
    rw [lcCircuitGate (N + N) D pre post r rfl]
    rfl


lemma mdOneSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 l0 : Fin N) (hI : I p0 l0)
    (haccept : (C.wires (List.ofFn (lcPair N p0 l0))).getD (N + N + pre.length) false = true)
    (honly : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true →
        p = p0 ∧ l = l0) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  let r : Gate := ⟨GateOp.and, [p0.val, N + l0.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · apply lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · intro z hz
      change GateOp.and.eval _ = true at hz
      rw [lcRawPairEval] at hz
      simp only [Bool.and_eq_true] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l0 z hz.1 hz.2)
        (N + N + pre.length) haccept
    · intro p l hpl
      change GateOp.and.eval _ = _
      rw [lcRawPairEval, ← lcCircuitGate (N + N) C pre post g hsplit,
        Bool.eq_iff_iff, Bool.and_eq_true, lcPairPoint, lcPairLine]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact haccept
      · intro ht
        obtain ⟨hp, hl⟩ := honly p l hpl ht
        exact ⟨hp.symm, hl.symm⟩
  · exact mdReplacementShape C pre post g r hsplit
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcRawPairEval] at hz
    simp only [Bool.and_eq_true] at hz
    exact ⟨p0, l0, hI, hz.1, hz.2⟩

def mdDirty (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ∃ p l : Fin N, ¬ I p l ∧
    (C.wires (List.ofFn (lcPair N p l))).getD (N + N + j) false = true

noncomputable def mdCount (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : ℕ := by
  classical
  exact ((Finset.range C.gates.length).filter (mdDirty N I C)).card

lemma mdCleanFromBelow (N : ℕ) (I : Fin N → Fin N → Prop) (D : Circuit) (j : ℕ)
    (hbelow : ∀ z : Fin (N + N) → Bool,
      (D.wires (List.ofFn z)).getD (N + N + j) false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ¬ mdDirty N I D j := by
  rintro ⟨_, p0, l0, hn, ht⟩
  obtain ⟨p, l, hI, hp, hl⟩ := hbelow _ ht
  have hpp := (lcPairPoint N p0 l0 p).mp hp
  have hll := (lcPairLine N p0 l0 l).mp hl
  exact hn (hpp ▸ hll ▸ hI)

lemma mdCountDecrease (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (hsize : D.size = C.size)
    (hle : ∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true)
    (hshape : ∀ k, k ≠ j → gateAt D k = gateAt C k)
    (hdirty : mdDirty N I C j) (hclean : ¬ mdDirty N I D j) :
    mdCount N I D < mdCount N I C := by
  classical
  let S := (Finset.range C.gates.length).filter (mdDirty N I C)
  let T := (Finset.range D.gates.length).filter (mdDirty N I D)
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hdirty⟩
  have hsub : T ⊆ S.erase j := by
    intro k hk
    obtain ⟨hklen, hkd⟩ := Finset.mem_filter.mp hk
    have hkne : k ≠ j := by
      intro h
      subst k
      exact hclean hkd
    apply Finset.mem_erase.mpr
    refine ⟨hkne, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · have hlen : D.gates.length = C.gates.length := hsize
      simpa only [hlen] using hklen
    · obtain ⟨hop, p, l, hn, ht⟩ := hkd
      exact ⟨(congrArg Gate.op (hshape k hkne)).symm.trans hop, p, l, hn, hle _ _ ht⟩
  have hlecard := Finset.card_le_card hsub
  have hcard := Finset.card_erase_of_mem hjS
  have hpos := Finset.card_pos.mpr ⟨j, hjS⟩
  change T.card < S.card
  omega

lemma minimum_dirty (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, mdDirty N I D j →
        ∃ p l : Fin N, I p l ∧
          (D.wires (List.ofFn (lcPair N p l))).getD (N + N + j) false = true ∧
          ∃ p' l' : Fin N, I p' l' ∧
            (D.wires (List.ofFn (lcPair N p' l'))).getD (N + N + j) false = true ∧
            (p ≠ p' ∨ l ≠ l')) := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    mdCount N I D = k
  have hex : ∃ k, P k := ⟨mdCount N I C, C, hmono, hreads, le_rfl, hfun, rfl⟩
  obtain ⟨D, hm, hr, hs, hf, hcount⟩ := Nat.find_spec hex
  have hmin (E : Circuit) (he : lcImproves N I D E) : mdCount N I D ≤ mdCount N I E := by
    rw [hcount]
    obtain ⟨hem, her, hes, _, _, hef⟩ := he
    exact Nat.find_min' hex ⟨E, hem, her, hes ▸ hs, hef, rfl⟩
  refine ⟨D, hm, hr, hs, hf, ?_⟩
  intro j hj hdirty
  by_contra htwo
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  let g := gateAt D j
  have hpre : pre.length = j := List.length_take_of_le hj.le
  have hsplit : D.gates = pre ++ g :: post := by
    dsimp [pre, post, g, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  by_cases hsupport : ∃ p l : Fin N, I p l ∧
      (D.wires (List.ofFn (lcPair N p l))).getD (N + N + j) false = true
  · obtain ⟨p0, l0, hI, haccept⟩ := hsupport
    have honly : ∀ p l : Fin N, I p l →
        (D.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true →
        p = p0 ∧ l = l0 := by
      intro p l hpl ht
      rw [hpre] at ht
      by_contra hne
      have hd : p0 ≠ p ∨ l0 ≠ l := by
        by_cases hp : p = p0
        · right
          intro hl
          exact hne ⟨hp, hl.symm⟩
        · exact Or.inl (Ne.symm hp)
      exact htwo ⟨p0, l0, hI, haccept, p, l, hpl, ht, hd⟩
    obtain ⟨E, he, hshape, _, hbelow⟩ := mdOneSupport N I D pre post g hsplit hm hr hf p0 l0 hI
      (by simpa only [hpre] using haccept) honly
    have hclean := mdCleanFromBelow N I E pre.length hbelow
    have hdec := mdCountDecrease N I D E j hj he.2.2.1 he.2.2.2.1
      (by simpa only [hpre] using hshape) hdirty (by simpa only [hpre] using hclean)
    exact (Nat.not_lt_of_ge (hmin E he)) hdec
  · have hnone : ∀ p l : Fin N, I p l →
        (D.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = false := by
      intro p l hpl
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hsupport ⟨p, l, hpl, by simpa only [hpre] using ht⟩
    obtain ⟨E, he, hshape, hor, _⟩ := mdZeroSupport N I D pre post g hsplit hm hr hf hnone
    have hclean : ¬ mdDirty N I E pre.length := by
      rintro ⟨hand, _⟩
      rw [hor] at hand
      cases hand
    have hdec := mdCountDecrease N I D E j hj he.2.2.1 he.2.2.2.1
      (by simpa only [hpre] using hshape) hdirty (by simpa only [hpre] using hclean)
    exact (Nat.not_lt_of_ge (hmin E he)) hdec


lemma lcStarEval (N : ℕ) (pre : List Gate) (p : Fin N) (w : ℕ)
    (z : Fin (N + N) → Bool) :
    GateOp.and.eval ([p.val, w].map fun i =>
      (pre.foldl decStep (List.ofFn z)).getD i false) =
      (z (Fin.castAdd N p) && (pre.foldl decStep (List.ofFn z)).getD w false) := by
  have hp : (pre.foldl decStep (List.ofFn z)).getD p.val false = z (Fin.castAdd N p) := by
    rw [lcRead _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact lcGetDOfFn z (Fin.castAdd N p)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, hp]

lemma lcStarSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 : Fin N) (w : ℕ) (hw : w < N + N + pre.length)
    (hstar : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true → p = p0)
    (hwire : ∀ z : Fin (N + N) → Bool,
      (pre.foldl decStep (List.ofFn z)).getD w false = true ↔
      ∃ l : Fin N, I p0 l ∧
        (C.wires (List.ofFn (lcPair N p0 l))).getD (N + N + pre.length) false = true ∧
        z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  let r : Gate := ⟨GateOp.and, [p0.val, w]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  have hle : ∀ z : Fin (N + N) → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true := by
    intro z hz
    change GateOp.and.eval _ = true at hz
    rw [lcStarEval, Bool.and_eq_true] at hz
    obtain ⟨l, _, haccept, hl⟩ := (hwire z).mp hz.2
    rw [← lcCircuitGate (N + N) C pre post g hsplit]
    exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l z hz.1 hl)
      (N + N + pre.length) haccept
  refine ⟨D, ?_, ?_, ?_⟩
  · apply lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · exact hle
    · intro p l hpl
      rw [Bool.eq_iff_iff]
      constructor
      · exact hle _
      · intro ht
        have haccept : (C.wires (List.ofFn (lcPair N p l))).getD
            (N + N + pre.length) false = true := by
          rw [lcCircuitGate (N + N) C pre post g hsplit]
          exact ht
        have hp := hstar p l hpl haccept
        subst p
        change GateOp.and.eval _ = true
        rw [lcStarEval, Bool.and_eq_true]
        exact ⟨(lcPairTrue N p0 l).1,
          (hwire _).mpr ⟨l, hpl, haccept, (lcPairTrue N p0 l).2⟩⟩
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcStarEval, Bool.and_eq_true] at hz
    obtain ⟨l, hpl, _, hl⟩ := (hwire z).mp hz.2
    exact ⟨p0, l, hpl, hz.1, hl⟩




open PEqualNP.MetaComplexity

def fsSingle {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def fsPositive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => fsPositive a ∧ fsPositive b
  | .or a b => fsPositive a ∧ fsPositive b

def fsCleanAt {n : ℕ} (i : Fin n) : DMFormula n → Prop
  | .lit _ _ => True
  | .and a b => fsCleanAt i a ∧ fsCleanAt i b ∧
      (a.eval (fsSingle i) && b.eval (fsSingle i)) = false
  | .or a b => fsCleanAt i a ∧ fsCleanAt i b

def fsEval {n : ℕ} (a : Option (DMFormula n)) (z : Fin n → Bool) : Bool :=
  a.elim false (fun f => f.eval z)

def fsLeaves {n : ℕ} (a : Option (DMFormula n)) : ℕ :=
  a.elim 0 DMFormula.leaves

def fsPos {n : ℕ} (a : Option (DMFormula n)) : Prop :=
  ∀ f ∈ a, fsPositive f

def fsClean {n : ℕ} (i : Fin n) (a : Option (DMFormula n)) : Prop :=
  ∀ f ∈ a, fsCleanAt i f

def fsOr {n : ℕ} : Option (DMFormula n) → Option (DMFormula n) → Option (DMFormula n)
  | none, b => b
  | a, none => a
  | some a, some b => some (.or a b)

def fsAnd {n : ℕ} : Option (DMFormula n) → Option (DMFormula n) → Option (DMFormula n)
  | some a, some b => some (.and a b)
  | _, _ => none

def fsJoin {n : ℕ} (i : Fin n) : Option (DMFormula n) → DMFormula n
  | none => .lit i true
  | some a => .or (.lit i true) a

lemma fsOr_eval {n : ℕ} (a b : Option (DMFormula n)) (z : Fin n → Bool) :
    fsEval (fsOr a b) z = (fsEval a z || fsEval b z) := by
  cases a <;> cases b <;> simp [fsOr, fsEval, DMFormula.eval]

lemma fsAnd_eval {n : ℕ} (a b : Option (DMFormula n)) (z : Fin n → Bool) :
    fsEval (fsAnd a b) z = (fsEval a z && fsEval b z) := by
  cases a <;> cases b <;> simp [fsAnd, fsEval, DMFormula.eval]

lemma fsJoin_eval {n : ℕ} (i : Fin n) (a : Option (DMFormula n)) (z : Fin n → Bool) :
    (fsJoin i a).eval z = (z i || fsEval a z) := by
  cases a <;> simp [fsJoin, fsEval, DMFormula.eval]

lemma fsOr_leaves {n : ℕ} (a b : Option (DMFormula n)) :
    fsLeaves (fsOr a b) = fsLeaves a + fsLeaves b := by
  cases a <;> cases b <;> simp [fsOr, fsLeaves, DMFormula.leaves]

lemma fsAnd_leaves {n : ℕ} (a b : Option (DMFormula n)) :
    fsLeaves (fsAnd a b) ≤ fsLeaves a + fsLeaves b := by
  cases a <;> cases b <;> simp [fsAnd, fsLeaves, DMFormula.leaves]

lemma fsJoin_leaves {n : ℕ} (i : Fin n) (a : Option (DMFormula n)) :
    (fsJoin i a).leaves = fsLeaves a + 1 := by
  cases a <;> simp [fsJoin, fsLeaves, DMFormula.leaves, Nat.add_comm]

lemma fsOr_pos {n : ℕ} (a b : Option (DMFormula n))
    (ha : fsPos a) (hb : fsPos b) : fsPos (fsOr a b) := by
  cases a <;> cases b <;> simp_all [fsOr, fsPos, fsPositive]

lemma fsAnd_pos {n : ℕ} (a b : Option (DMFormula n))
    (ha : fsPos a) (hb : fsPos b) : fsPos (fsAnd a b) := by
  cases a <;> cases b <;> simp_all [fsAnd, fsPos, fsPositive]

lemma fsJoin_pos {n : ℕ} (i : Fin n) (a : Option (DMFormula n))
    (ha : fsPos a) : fsPositive (fsJoin i a) := by
  cases a <;> simp_all [fsJoin, fsPos, fsPositive]

lemma fsOr_clean {n : ℕ} (i : Fin n) (a b : Option (DMFormula n))
    (ha : fsClean i a) (hb : fsClean i b) : fsClean i (fsOr a b) := by
  cases a <;> cases b <;> simp_all [fsOr, fsClean, fsCleanAt]

lemma fsAnd_clean {n : ℕ} (i : Fin n) (a b : Option (DMFormula n))
    (ha : fsClean i a) (hb : fsClean i b)
    (hz : (fsEval a (fsSingle i) && fsEval b (fsSingle i)) = false) :
    fsClean i (fsAnd a b) := by
  cases a <;> cases b <;> simp_all [fsAnd, fsClean, fsCleanAt, fsEval]

lemma fsJoin_clean {n : ℕ} (i j : Fin n) (a : Option (DMFormula n))
    (ha : fsClean j a) : fsCleanAt j (fsJoin i a) := by
  cases a <;> simp_all [fsJoin, fsClean, fsCleanAt]

lemma fsFactor {n : ℕ} (i : Fin n) (f : DMFormula n) (hf : fsPositive f)
    (hi : f.eval (fsSingle i) = true) :
    ∃ a : Option (DMFormula n), fsPos a ∧ fsLeaves a + 1 ≤ f.leaves ∧
      (∀ z, f.eval z = (z i || fsEval a z)) ∧ fsEval a (fsSingle i) = false ∧
      ∀ j, fsCleanAt j f → fsClean j a := by
  induction f with
  | lit j b =>
    have hb : b = true := hf
    subst b
    have hj : j = i := by simpa [DMFormula.eval, fsSingle] using hi
    subst j
    exact ⟨none, by simp [fsPos], by simp [fsLeaves, DMFormula.leaves],
      by simp [DMFormula.eval, fsEval], rfl, by simp [fsClean]⟩
  | or f g ihf ihg =>
    obtain ⟨hf, hg⟩ := hf
    have he : f.eval (fsSingle i) = true ∨ g.eval (fsSingle i) = true :=
      by simpa only [DMFormula.eval, Bool.or_eq_true] using hi
    by_cases hfi : f.eval (fsSingle i) = true
    · obtain ⟨a, hpa, hla, hea, hza, hca⟩ := ihf hf hfi
      by_cases hgi : g.eval (fsSingle i) = true
      · obtain ⟨b, hpb, hlb, heb, hzb, hcb⟩ := ihg hg hgi
        refine ⟨fsOr a b, fsOr_pos a b hpa hpb, ?_, ?_, ?_, ?_⟩
        · rw [fsOr_leaves]; change _ ≤ f.leaves + g.leaves; omega
        · intro z; simp only [DMFormula.eval, hea, heb, fsOr_eval]
          cases z i <;> simp
        · simp [fsOr_eval, hza, hzb]
        · intro j hj; exact fsOr_clean j a b (hca j hj.1) (hcb j hj.2)
      · refine ⟨fsOr a (some g), fsOr_pos _ _ hpa (by simpa [fsPos] using hg),
          ?_, ?_, ?_, ?_⟩
        · rw [fsOr_leaves]; change fsLeaves a + g.leaves + 1 ≤ f.leaves + g.leaves; omega
        · intro z; rw [DMFormula.eval, hea, fsOr_eval]
          change ((z i || fsEval a z) || g.eval z) = (z i || (fsEval a z || g.eval z))
          exact Bool.or_assoc _ _ _
        · have hg0 : g.eval (fsSingle i) = false := Bool.eq_false_iff.mpr hgi
          rw [fsOr_eval, hza]
          simpa only [fsEval, Option.elim_some, Bool.false_or] using hg0
        · intro j hj; exact fsOr_clean j _ _ (hca j hj.1) (by simpa [fsClean] using hj.2)
    · have hgi : g.eval (fsSingle i) = true := he.resolve_left hfi
      obtain ⟨b, hpb, hlb, heb, hzb, hcb⟩ := ihg hg hgi
      refine ⟨fsOr (some f) b, fsOr_pos _ _ (by simpa [fsPos] using hf) hpb,
        ?_, ?_, ?_, ?_⟩
      · rw [fsOr_leaves]; change f.leaves + fsLeaves b + 1 ≤ f.leaves + g.leaves; omega
      · intro z; rw [DMFormula.eval, heb, fsOr_eval]
        change (f.eval z || (z i || fsEval b z)) = (z i || (f.eval z || fsEval b z))
        cases z i <;> simp
      · have hf0 : f.eval (fsSingle i) = false := Bool.eq_false_iff.mpr hfi
        rw [fsOr_eval, hzb]
        simpa only [fsEval, Option.elim_some, Bool.or_false] using hf0
      · intro j hj; exact fsOr_clean j _ _ (by simpa [fsClean] using hj.1) (hcb j hj.2)
  | and f g ihf ihg =>
    obtain ⟨hf, hg⟩ := hf
    have hp : f.eval (fsSingle i) = true ∧ g.eval (fsSingle i) = true :=
      by simpa only [DMFormula.eval, Bool.and_eq_true] using hi
    obtain ⟨hfi, hgi⟩ := hp
    obtain ⟨a, hpa, hla, hea, hza, hca⟩ := ihf hf hfi
    obtain ⟨b, hpb, hlb, heb, hzb, hcb⟩ := ihg hg hgi
    refine ⟨fsAnd a b, fsAnd_pos a b hpa hpb, ?_, ?_, ?_, ?_⟩
    · have hh := fsAnd_leaves a b
      change _ ≤ f.leaves + g.leaves; omega
    · intro z; simp only [DMFormula.eval, hea, heb, fsAnd_eval]
      cases z i <;> simp
    · simp [fsAnd_eval, hza, hzb]
    · intro j hj
      apply fsAnd_clean j a b (hca j hj.1) (hcb j hj.2.1)
      have hz := hj.2.2
      rw [hea, heb] at hz
      cases fsSingle j i <;> simp_all

lemma fsNormalizeAt {n : ℕ} (i : Fin n) (f : DMFormula n) (hf : fsPositive f) :
    ∃ g : DMFormula n, fsPositive g ∧ g.leaves ≤ f.leaves ∧
      (∀ z, g.eval z = f.eval z) ∧ fsCleanAt i g ∧
      ∀ j, fsCleanAt j f → fsCleanAt j g := by
  induction f with
  | lit j b => exact ⟨.lit j b, hf, le_rfl, fun _ => rfl, trivial, fun _ h => h⟩
  | or f g ihf ihg =>
    obtain ⟨a, hpa, hla, hea, hca, hsa⟩ := ihf hf.1
    obtain ⟨b, hpb, hlb, heb, hcb, hsb⟩ := ihg hf.2
    refine ⟨.or a b, ⟨hpa, hpb⟩, Nat.add_le_add hla hlb,
      ?_, ⟨hca, hcb⟩, ?_⟩
    · intro z; simp [DMFormula.eval, hea, heb]
    · intro j hj; exact ⟨hsa j hj.1, hsb j hj.2⟩
  | and f g ihf ihg =>
    obtain ⟨a, hpa, hla, hea, hca, hsa⟩ := ihf hf.1
    obtain ⟨b, hpb, hlb, heb, hcb, hsb⟩ := ihg hf.2
    by_cases hfi : (a.eval (fsSingle i) && b.eval (fsSingle i)) = true
    · have hp : a.eval (fsSingle i) = true ∧ b.eval (fsSingle i) = true :=
        by simpa only [Bool.and_eq_true] using hfi
      obtain ⟨hai, hbi⟩ := hp
      obtain ⟨a', hpa', hla', hea', hza', hca'⟩ := fsFactor i a hpa hai
      obtain ⟨b', hpb', hlb', heb', hzb', hcb'⟩ := fsFactor i b hpb hbi
      refine ⟨fsJoin i (fsAnd a' b'), fsJoin_pos _ _ (fsAnd_pos _ _ hpa' hpb'),
        ?_, ?_, ?_, ?_⟩
      · rw [fsJoin_leaves]
        have hh := fsAnd_leaves a' b'
        change _ ≤ f.leaves + g.leaves; omega
      · intro z
        rw [fsJoin_eval, fsAnd_eval, DMFormula.eval]
        rw [← hea, ← heb, hea', heb']
        cases z i <;> simp
      · apply fsJoin_clean
        exact fsAnd_clean _ _ _ (hca' i hca) (hcb' i hcb) (by simp [hza', hzb'])
      · intro j hj
        apply fsJoin_clean
        apply fsAnd_clean _ _ _ (hca' j (hsa j hj.1)) (hcb' j (hsb j hj.2.1))
        have hz := hj.2.2
        rw [← hea, ← heb, hea', heb'] at hz
        cases hji : fsSingle j i
        · simpa [hji] using hz
        · simp [hji] at hz
    · refine ⟨.and a b, ⟨hpa, hpb⟩, Nat.add_le_add hla hlb, ?_,
        ⟨hca, hcb, Bool.eq_false_iff.mpr hfi⟩, ?_⟩
      · intro z; simp [DMFormula.eval, hea, heb]
      · intro j hj
        exact ⟨hsa j hj.1, hsb j hj.2.1, by simpa [hea, heb] using hj.2.2⟩

lemma fsNormalizeList {n : ℕ} (is : List (Fin n)) (f : DMFormula n) (hf : fsPositive f) :
    ∃ g : DMFormula n, fsPositive g ∧ g.leaves ≤ f.leaves ∧
      (∀ z, g.eval z = f.eval z) ∧ (∀ i ∈ is, fsCleanAt i g) ∧
      ∀ j, fsCleanAt j f → fsCleanAt j g := by
  induction is generalizing f with
  | nil => exact ⟨f, hf, le_rfl, fun _ => rfl, by simp, fun _ h => h⟩
  | cons i is ih =>
    obtain ⟨a, hpa, hla, hea, hca, hsa⟩ := fsNormalizeAt i f hf
    obtain ⟨b, hpb, hlb, heb, hcb, hsb⟩ := ih a hpa
    refine ⟨b, hpb, hlb.trans hla, fun z => (heb z).trans (hea z), ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hsb _ hca
      · exact hcb j hj
    · intro j hj; exact hsb j (hsa j hj)

lemma fsNormalize {n : ℕ} (f : DMFormula n) (hf : fsPositive f) :
    ∃ g : DMFormula n, fsPositive g ∧ g.leaves ≤ f.leaves ∧
      (∀ z, g.eval z = f.eval z) ∧ ∀ i, fsCleanAt i g := by
  obtain ⟨g, hpg, hlg, heg, hcg, _⟩ := fsNormalizeList (List.finRange n) f hf
  exact ⟨g, hpg, hlg, heg, fun i => hcg i (by simp)⟩


end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

-- Essential edges are those lost when the selected gate is replaced by false.
def lcKill (C : Circuit) (pre post : List Gate) : Circuit :=
  ⟨pre ++ ⟨GateOp.or, []⟩ :: post, C.output⟩

def lcOutputImproves (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit) : Prop :=
  Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
    (∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true →
      (C.wires (List.ofFn z)).getD i false = true) ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

lemma lcReplaceEq (n : ℕ) (C : Circuit) (pre post : List Gate) (g r : Gate)
    (hsplit : C.gates = pre ++ g :: post) (z : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
        (pre.foldl decStep (List.ofFn z)).getD i false) =
      g.op.eval (g.inputs.map fun i =>
        (pre.foldl decStep (List.ofFn z)).getD i false)) :
    (⟨pre ++ r :: post, C.output⟩ : Circuit).wires (List.ofFn z) = C.wires (List.ofFn z) := by
  change (pre ++ r :: post).foldl decStep _ = C.gates.foldl decStep _
  rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  simp only [decStep, heq]

lemma lcKillBelow (n : ℕ) (C : Circuit) (pre post : List Gate) (r : Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (z : Fin n → Bool) :
    ∀ i, ((lcKill C pre post).wires (List.ofFn z)).getD i false = true →
      ((⟨pre ++ r :: post, C.output⟩ : Circuit).wires (List.ofFn z)).getD i false = true := by
  change ∀ i, ((pre ++ ⟨GateOp.or, []⟩ :: post).foldl decStep _).getD i false = true →
    ((pre ++ r :: post).foldl decStep _).getD i false = true
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  apply decFoldMono post hpost
  · simp [decStep]
  · apply lcSnocMono
    simp [GateOp.eval]

lemma lcReplacementOutput (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g r : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrsize : r.inputs.length ≤ 2)
    (hrread : ∀ a ∈ r.inputs, a < N + N + pre.length)
    (hrle : ∀ z : Fin (N + N) → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true)
    (hreq : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (⟨pre ++ r :: post, C.output⟩ : Circuit) (lcPair N p l) = true) :
    lcOutputImproves N I C ⟨pre ++ r :: post, C.output⟩ := by
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  have hm : Monotone2 D := by
    intro a ha
    change a ∈ pre ++ r :: post at ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hmono a (by rw [hsplit]; simp [ha])
    · exact ⟨hrop, hrsize⟩
    · exact hmono a (by rw [hsplit]; simp [ha])
  have hr : ReadsBack (N + N) D := by
    intro k hk a ha
    by_cases he : k = pre.length
    · subst k
      have har : a ∈ r.inputs := by simpa [gateAt, D] using ha
      exact hrread a har
    · have hg := lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k he
      have hak : a ∈ (gateAt C k).inputs := by
        change a ∈ ((pre ++ r :: post).getD k ⟨GateOp.or, []⟩).inputs at ha
        rw [hg] at ha
        simpa only [gateAt, hsplit] using ha
      exact hreads k (by simpa [hsplit, D] using hk) a hak
  have hle : ∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true := by
    intro z
    change ∀ i, ((pre ++ r :: post).foldl decStep (List.ofFn z)).getD i false = true →
      (C.gates.foldl decStep (List.ofFn z)).getD i false = true
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply decFoldMono post (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1)
    · simp [decStep]
    · exact lcSnocMono _ _ _ (hrle z)
  refine ⟨hm, hr, by simp [Circuit.size, hsplit], hle, ?_⟩
  apply lcPairCompleteness N I C D hfun hm (fun z => hle z C.output)
  intro p l hpl
  exact (hreq p l hpl).trans
    ((hfun _).mpr ⟨p, l, hpl, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩).symm

lemma lcEssentialAccepted (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (hI : I p l)
    (he : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false) :
    (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true := by
  by_contra hn
  have hz := Bool.eq_false_iff.mpr hn
  rw [lcCircuitGate (N + N) C pre post g hsplit] at hz
  have heq := lcReplaceEq (N + N) C pre post g ⟨GateOp.or, []⟩ hsplit (lcPair N p l) hz.symm
  have hc := (hfun _).mpr ⟨p, l, hI, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩
  have hout := congrArg (fun w : List Bool => w.getD C.output false) heq
  change circuitFun (N + N) (lcKill C pre post) (lcPair N p l) =
    circuitFun (N + N) C (lcPair N p l) at hout
  rw [he, hc] at hout
  cases hout

lemma lcZeroEssential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hnone : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = true) :
    ∃ D : Circuit, lcOutputImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.or ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = false) := by
  let r : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := lcKill C pre post
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact lcReplacementOutput N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
      (by simp [r]) (by simp [r]) (by simp [r, GateOp.eval]) hnone
  · exact mdReplacementShape C pre post g r hsplit
  · simp [gateAt, D, lcKill]
  · intro z
    rw [lcCircuitGate (N + N) D pre post r rfl]
    rfl

lemma lcOneEssential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 l0 : Fin N) (hI : I p0 l0)
    (hessential : circuitFun (N + N) (lcKill C pre post) (lcPair N p0 l0) = false)
    (honly : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false → p = p0 ∧ l = l0) :
    ∃ D : Circuit, lcOutputImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  have haccept := lcEssentialAccepted N I C pre post g hsplit hfun p0 l0 hI hessential
  let r : Gate := ⟨GateOp.and, [p0.val, N + l0.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · apply lcReplacementOutput N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · intro z hz
      change GateOp.and.eval _ = true at hz
      rw [lcRawPairEval] at hz
      simp only [Bool.and_eq_true] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l0 z hz.1 hz.2)
        (N + N + pre.length) haccept
    · intro p l hpl
      by_cases he : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false
      · obtain ⟨hp, hl⟩ := honly p l hpl he
        subst p
        subst l
        have heq : r.op.eval (r.inputs.map fun i =>
            (pre.foldl decStep (List.ofFn (lcPair N p0 l0))).getD i false) =
            g.op.eval (g.inputs.map fun i =>
              (pre.foldl decStep (List.ofFn (lcPair N p0 l0))).getD i false) := by
          change GateOp.and.eval _ = _
          rw [lcRawPairEval, ← lcCircuitGate (N + N) C pre post g hsplit, haccept]
          simp only [(lcPairTrue N p0 l0).1, (lcPairTrue N p0 l0).2, Bool.true_and]
        have hw := lcReplaceEq (N + N) C pre post g r hsplit (lcPair N p0 l0) heq
        have hout := congrArg (fun w : List Bool => w.getD C.output false) hw
        exact hout.trans ((hfun _).mpr
          ⟨p0, l0, hI, (lcPairTrue N p0 l0).1, (lcPairTrue N p0 l0).2⟩)
      · have hz : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = true :=
          Bool.eq_true_of_ne_false he
        exact lcKillBelow (N + N) C pre post r
          (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1) _ C.output hz
  · exact mdReplacementShape C pre post g r hsplit
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcRawPairEval] at hz
    simp only [Bool.and_eq_true] at hz
    exact ⟨p0, l0, hI, hz.1, hz.2⟩

def lcEssential (N : ℕ) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  circuitFun (N + N) (lcKill C (C.gates.take j) (C.gates.drop (j + 1))) (lcPair N p l) = false

lemma minimum_dirty_essential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, mdDirty N I D j →
        ∃ p l : Fin N, I p l ∧ lcEssential N D j p l ∧
          ∃ p' l' : Fin N, I p' l' ∧ lcEssential N D j p' l' ∧ (p ≠ p' ∨ l ≠ l')) := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    mdCount N I D = k
  have hex : ∃ k, P k := ⟨mdCount N I C, C, hmono, hreads, le_rfl, hfun, rfl⟩
  obtain ⟨D, hm, hr, hs, hf, hcount⟩ := Nat.find_spec hex
  have hmin (E : Circuit) (he : lcOutputImproves N I D E) : mdCount N I D ≤ mdCount N I E := by
    rw [hcount]
    obtain ⟨hem, her, hes, _, hef⟩ := he
    exact Nat.find_min' hex ⟨E, hem, her, hes ▸ hs, hef, rfl⟩
  refine ⟨D, hm, hr, hs, hf, ?_⟩
  intro j hj hdirty
  by_contra htwo
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  let g := gateAt D j
  have hpre : pre.length = j := List.length_take_of_le hj.le
  have hsplit : D.gates = pre ++ g :: post := by
    dsimp [pre, post, g, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  by_cases hsupport : ∃ p l : Fin N, I p l ∧ lcEssential N D j p l
  · obtain ⟨p0, l0, hI, haccept⟩ := hsupport
    have honly : ∀ p l : Fin N, I p l →
        circuitFun (N + N) (lcKill D pre post) (lcPair N p l) = false →
        p = p0 ∧ l = l0 := by
      intro p l hpl ht
      by_contra hne
      have hd : p0 ≠ p ∨ l0 ≠ l := by
        by_cases hp : p = p0
        · right
          intro hl
          exact hne ⟨hp, hl.symm⟩
        · exact Or.inl (Ne.symm hp)
      exact htwo ⟨p0, l0, hI, haccept, p, l, hpl, ht, hd⟩
    obtain ⟨E, he, hshape, _, hbelow⟩ := lcOneEssential N I D pre post g hsplit hm hr hf
      p0 l0 hI haccept honly
    have hclean := mdCleanFromBelow N I E pre.length hbelow
    have hdec := mdCountDecrease N I D E j hj he.2.2.1 he.2.2.2.1
      (by simpa only [hpre] using hshape) hdirty (by simpa only [hpre] using hclean)
    exact (Nat.not_lt_of_ge (hmin E he)) hdec
  · have hnone : ∀ p l : Fin N, I p l →
        circuitFun (N + N) (lcKill D pre post) (lcPair N p l) = true := by
      intro p l hpl
      apply Bool.eq_true_of_ne_false
      intro ht
      exact hsupport ⟨p, l, hpl, ht⟩
    obtain ⟨E, he, hshape, hor, _⟩ := lcZeroEssential N I D pre post g hsplit hm hr hf hnone
    have hclean : ¬ mdDirty N I E pre.length := by
      rintro ⟨hand, _⟩
      rw [hor] at hand
      cases hand
    have hdec := mdCountDecrease N I D E j hj he.2.2.1 he.2.2.2.1
      (by simpa only [hpre] using hshape) hdirty (by simpa only [hpre] using hclean)
    exact (Nat.not_lt_of_ge (hmin E he)) hdec

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

def lcSingleton {n : ℕ} (i : Fin n) (k : Fin n) : Bool := decide (k = i)

lemma lcLiteralEval {n : ℕ} (pre : List Gate) (i : Fin n) (z : Fin n → Bool) :
    GateOp.or.eval ([i.val].map fun k => (pre.foldl decStep (List.ofFn z)).getD k false) = z i := by
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [lcRead _ _ _ (by simpa using i.isLt)]
  exact lcGetDOfFn z i

lemma lcLiteralEssential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (i : Fin (N + N))
    (hsingle : (C.wires (List.ofFn (lcSingleton i))).getD (N + N + pre.length) false = true)
    (hcritical : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false → lcPair N p l i = true) :
    ∃ D : Circuit, lcOutputImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.or := by
  let r : Gate := ⟨GateOp.or, [i.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, mdReplacementShape C pre post g r hsplit, ?_⟩
  · apply lcReplacementOutput N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
    · simp [r]
    · intro k hk
      simp only [r, List.mem_singleton] at hk
      subst k
      have hi := i.isLt
      omega
    · intro z hz
      change GateOp.or.eval _ = true at hz
      rw [lcLiteralEval] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      apply decWireMono (N + N) C hmono (lcSingleton i) z ?_ (N + N + pre.length) hsingle
      intro k hk
      have hki : k = i := of_decide_eq_true hk
      simpa only [hki] using hz
    · intro p l hpl
      by_cases he : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false
      · have hnew := hcritical p l hpl he
        have hold := lcEssentialAccepted N I C pre post g hsplit hfun p l hpl he
        have heq : r.op.eval (r.inputs.map fun k =>
            (pre.foldl decStep (List.ofFn (lcPair N p l))).getD k false) =
            g.op.eval (g.inputs.map fun k =>
              (pre.foldl decStep (List.ofFn (lcPair N p l))).getD k false) := by
          change GateOp.or.eval _ = _
          rw [lcLiteralEval, hnew, ← lcCircuitGate (N + N) C pre post g hsplit, hold]
        have hw := lcReplaceEq (N + N) C pre post g r hsplit (lcPair N p l) heq
        have hout := congrArg (fun w : List Bool => w.getD C.output false) hw
        exact hout.trans ((hfun _).mpr
          ⟨p, l, hpl, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩)
      · have hz := Bool.eq_true_of_ne_false he
        exact lcKillBelow (N + N) C pre post r
          (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1) _ C.output hz
  · simp [gateAt, D, r]

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity

def mfWire {n : ℕ} (C : Circuit) (w : ℕ) (z : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn z)).getD w false

def mfSafeProduct (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (u v : ℕ) : Prop :=
  ∀ z : Fin (N + N) → Bool, mfWire C u z = true → mfWire C v z = true →
    ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

lemma mfCrossPoint (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v : ℕ) (hsafe : mfSafeProduct N I C u v)
    (p q r : Fin N) (hu : mfWire C u (lcSingleton (Fin.castAdd N p)) = true)
    (hv : mfWire C v (lcPair N q r) = true) (hbad : ¬ I q r) : I p r := by
  let z : Fin (N + N) → Bool := fun k => lcPair N p r k || lcPair N q r k
  have huz : mfWire C u z = true := by
    apply decWireMono (N + N) C hmono (lcSingleton (Fin.castAdd N p)) z ?_ u hu
    intro k hk
    have he : k = Fin.castAdd N p := of_decide_eq_true hk
    subst k
    simp [z, lcPair]
  have hvz : mfWire C v z = true := by
    apply decWireMono (N + N) C hmono (lcPair N q r) z ?_ v hv
    intro k hk
    simp [z, hk]
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z huz hvz
  simp only [z, Bool.or_eq_true] at ha hb
  have hb' : b = r := by
    rcases hb with hb | hb
    · exact (lcPairLine N p r b).mp hb
    · exact (lcPairLine N q r b).mp hb
  subst b
  have ha' : a = p ∨ a = q := by
    rcases ha with ha | ha
    · exact Or.inl ((lcPairPoint N p r a).mp ha)
    · exact Or.inr ((lcPairPoint N q r a).mp ha)
  rcases ha' with rfl | rfl
  · exact hab
  · exact (hbad hab).elim

lemma mfCrossLine (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v : ℕ) (hsafe : mfSafeProduct N I C u v)
    (l q r : Fin N) (hu : mfWire C u (lcSingleton (Fin.natAdd N l)) = true)
    (hv : mfWire C v (lcPair N q r) = true) (hbad : ¬ I q r) : I q l := by
  let z : Fin (N + N) → Bool := fun k => lcPair N q l k || lcPair N q r k
  have huz : mfWire C u z = true := by
    apply decWireMono (N + N) C hmono (lcSingleton (Fin.natAdd N l)) z ?_ u hu
    intro k hk
    have he : k = Fin.natAdd N l := of_decide_eq_true hk
    subst k
    simp [z, lcPair]
  have hvz : mfWire C v z = true := by
    apply decWireMono (N + N) C hmono (lcPair N q r) z ?_ v hv
    intro k hk
    simp [z, hk]
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z huz hvz
  simp only [z, Bool.or_eq_true] at ha hb
  have ha' : a = q := by
    rcases ha with ha | ha
    · exact (lcPairPoint N q l a).mp ha
    · exact (lcPairPoint N q r a).mp ha
  subst a
  have hb' : b = l ∨ b = r := by
    rcases hb with hb | hb
    · exact Or.inl ((lcPairLine N q l b).mp hb)
    · exact Or.inr ((lcPairLine N q r b).mp hb)
  rcases hb' with rfl | rfl
  · exact hab
  · exact (hbad hab).elim

lemma mfJunkRectangle (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v : ℕ) (hsafe : mfSafeProduct N I C u v)
    (q r : Fin N) (hbad : ¬ I q r) (hv : mfWire C v (lcPair N q r) = true) :
    (∀ p : Fin N, mfWire C u (lcSingleton (Fin.castAdd N p)) = true → I p r) ∧
    (∀ l : Fin N, mfWire C u (lcSingleton (Fin.natAdd N l)) = true → I q l) := by
  exact ⟨fun p hp => mfCrossPoint N I C hmono u v hsafe p q r hp hv hbad,
    fun l hl => mfCrossLine N I C hmono u v hsafe l q r hl hv hbad⟩

lemma mfTwoPointsForceLine (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v v' : ℕ) (hsafe : mfSafeProduct N I C u v)
    (hsafe' : mfSafeProduct N I C u v')
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' : Fin N) (hpp : p ≠ p')
    (hp : mfWire C u (lcSingleton (Fin.castAdd N p)) = true)
    (hp' : mfWire C u (lcSingleton (Fin.castAdd N p')) = true)
    (q r q' r' : Fin N) (hbad : ¬ I q r) (hbad' : ¬ I q' r')
    (hv : mfWire C v (lcPair N q r) = true)
    (hv' : mfWire C v' (lcPair N q' r') = true) : r = r' := by
  by_contra hrr
  exact hfour p p' r r' hpp hrr
    ⟨mfCrossPoint N I C hmono u v hsafe p q r hp hv hbad,
      mfCrossPoint N I C hmono u v' hsafe' p q' r' hp hv' hbad',
      mfCrossPoint N I C hmono u v hsafe p' q r hp' hv hbad,
      mfCrossPoint N I C hmono u v' hsafe' p' q' r' hp' hv' hbad'⟩

lemma mfTwoLinesForcePoint (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v v' : ℕ) (hsafe : mfSafeProduct N I C u v)
    (hsafe' : mfSafeProduct N I C u v')
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l l' : Fin N) (hll : l ≠ l')
    (hl : mfWire C u (lcSingleton (Fin.natAdd N l)) = true)
    (hl' : mfWire C u (lcSingleton (Fin.natAdd N l')) = true)
    (q r q' r' : Fin N) (hbad : ¬ I q r) (hbad' : ¬ I q' r')
    (hv : mfWire C v (lcPair N q r) = true)
    (hv' : mfWire C v' (lcPair N q' r') = true) : q = q' := by
  by_contra hqq
  exact hfour q q' l l' hqq hll
    ⟨mfCrossLine N I C hmono u v hsafe l q r hl hv hbad,
      mfCrossLine N I C hmono u v hsafe l' q r hl' hv hbad,
      mfCrossLine N I C hmono u v' hsafe' l q' r' hl hv' hbad',
      mfCrossLine N I C hmono u v' hsafe' l' q' r' hl' hv' hbad'⟩

lemma mfTwoEachForcePair (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v v' : ℕ) (hsafe : mfSafeProduct N I C u v)
    (hsafe' : mfSafeProduct N I C u v')
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' l l' : Fin N) (hpp : p ≠ p') (hll : l ≠ l')
    (hp : mfWire C u (lcSingleton (Fin.castAdd N p)) = true)
    (hp' : mfWire C u (lcSingleton (Fin.castAdd N p')) = true)
    (hl : mfWire C u (lcSingleton (Fin.natAdd N l)) = true)
    (hl' : mfWire C u (lcSingleton (Fin.natAdd N l')) = true)
    (q r q' r' : Fin N) (hbad : ¬ I q r) (hbad' : ¬ I q' r')
    (hv : mfWire C v (lcPair N q r) = true)
    (hv' : mfWire C v' (lcPair N q' r') = true) : q = q' ∧ r = r' := by
  exact ⟨mfTwoLinesForcePoint N I C hmono u v v' hsafe hsafe' hfour l l' hll hl hl'
      q r q' r' hbad hbad' hv hv',
    mfTwoPointsForceLine N I C hmono u v v' hsafe hsafe' hfour p p' hpp hp hp'
      q r q' r' hbad hbad' hv hv'⟩

lemma mfRectangleRows (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (P L : Finset (Fin N)) (q r l l' : Fin N)
    (hl : l ∈ L) (hl' : l' ∈ L) (hll : l ≠ l')
    (hmiss : ∀ p ∈ P, ∀ k ∈ L, ¬ I p k → p = q ∧ k = r) : P.card ≤ 2 := by
  classical
  by_cases hs : P ⊆ {q}
  · have h := Finset.card_le_card hs
    simp only [Finset.card_singleton] at h
    omega
  · obtain ⟨p, hp, hpq⟩ := Finset.not_subset.mp hs
    simp only [Finset.mem_singleton] at hpq
    have hrow (a : Fin N) (ha : a ∈ P) (haq : a ≠ q) (k : Fin N) (hk : k ∈ L) :
        I a k := by
      by_contra h
      exact haq (hmiss a ha k hk h).1
    have hsub : P ⊆ {q, p} := by
      intro a ha
      by_cases haq : a = q
      · simp [haq]
      · have hap : a = p := by
          by_contra h
          exact hfour a p l l' h hll
            ⟨hrow a ha haq l hl, hrow a ha haq l' hl',
              hrow p hp hpq l hl, hrow p hp hpq l' hl'⟩
        simp [hap]
    exact (Finset.card_le_card hsub).trans
      (by simpa using Finset.card_insert_le q ({p} : Finset (Fin N)))

lemma mfRectangleColumns (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (P L : Finset (Fin N)) (q r p p' : Fin N)
    (hp : p ∈ P) (hp' : p' ∈ P) (hpp : p ≠ p')
    (hmiss : ∀ a ∈ P, ∀ l ∈ L, ¬ I a l → a = q ∧ l = r) : L.card ≤ 2 := by
  refine mfRectangleRows N (fun l p => I p l) ?_ L P r q p p' hp hp' hpp ?_
  · intro l l' p p' hll hpp h
    exact hfour p p' l l' hpp hll ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  · intro l hl a ha hbad
    exact (hmiss a ha l hl hbad).symm

lemma mfRectangleStarOrSquare (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (P L : Finset (Fin N)) (q r : Fin N)
    (hmiss : ∀ a ∈ P, ∀ l ∈ L, ¬ I a l → a = q ∧ l = r) :
    P.card ≤ 1 ∨ L.card ≤ 1 ∨ P.card ≤ 2 ∧ L.card ≤ 2 := by
  by_cases hp : P.card ≤ 1
  · exact Or.inl hp
  by_cases hl : L.card ≤ 1
  · exact Or.inr (Or.inl hl)
  obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
  exact Or.inr (Or.inr
    ⟨mfRectangleRows N I hfour P L q r l l' hl hl' hll hmiss,
      mfRectangleColumns N I hfour P L q r p p' hp hp' hpp hmiss⟩)

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

def frDirty (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit) (j : ℕ) : Prop :=
  ∃ z : Fin n → Bool, bad z ∧ (C.wires (List.ofFn z)).getD (n + j) false = true

lemma frGateEval (n : ℕ) (C : Circuit) (hr : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) (z : Fin n → Bool) :
    (C.wires (List.ofFn z)).getD (n + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn z)).getD i false) := by
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hpre : pre.length = j := List.length_take_of_le hj.le
  have hs : C.gates = pre ++ gateAt C j :: post := by
    dsimp [pre, post, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  have hg := lcCircuitGate n C pre post (gateAt C j) hs z
  rw [hpre] at hg
  rw [hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  symm
  change (C.gates.foldl decStep (List.ofFn z)).getD i false = _
  rw [hs, List.foldl_append]
  apply lcRead
  rw [lcLength, List.length_ofFn, hpre]
  exact hr j hj i hi

lemma frOrReader (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit)
    (hr : ReadsBack n C) (j k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hread : n + j ∈ (gateAt C k).inputs)
    (hd : frDirty n bad C j) : frDirty n bad C k := by
  obtain ⟨z, hz, hw⟩ := hd
  refine ⟨z, hz, ?_⟩
  rw [frGateEval n C hr k hk z, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨n + j, hread, hw⟩, rfl⟩

lemma frLatestReaders (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C) (j : ℕ)
    (hd : frDirty n bad C j)
    (hlast : ∀ k < C.gates.length, frDirty n bad C k → k ≤ j) :
    ∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.and ∧ ¬ frDirty n bad C k := by
  intro k hk hread
  have hjk : j < k := by have h := hr k hk (n + j) hread; omega
  have hclean : ¬ frDirty n bad C k := by
    intro hd'
    have h := hlast k hk hd'
    omega
  refine ⟨?_, hclean⟩
  have hmem : gateAt C k ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hop := (hm (gateAt C k) hmem).1
  change (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or at hop
  rcases hop with hop | hop
  · exact hop
  · exact (hclean (frOrReader n bad C hr j k hk hop hread hd)).elim

lemma frLatestExists (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hex : ∃ j < C.gates.length, frDirty n bad C j) :
    ∃ j < C.gates.length, frDirty n bad C j ∧
      (∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
        (gateAt C k).op = GateOp.and ∧ ¬ frDirty n bad C k) := by
  classical
  let S := (Finset.range C.gates.length).filter (frDirty n bad C)
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hd⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hd⟩⟩
  let j := S.max' hS
  have hjS : j ∈ S := Finset.max'_mem S hS
  obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hjS
  have hj' := Finset.mem_range.mp hj
  refine ⟨j, hj', hd, frLatestReaders n bad C hm hr j hd ?_⟩
  intro k hk hdk
  exact Finset.le_max' S k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hdk⟩)

lemma frGloballySafeReaders (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hex : ∃ j < C.gates.length, ∃ z : Fin n → Bool,
      circuitFun n C z = false ∧ (C.wires (List.ofFn z)).getD (n + j) false = true) :
    ∃ j < C.gates.length,
      (∃ z : Fin n → Bool, circuitFun n C z = false ∧
        (C.wires (List.ofFn z)).getD (n + j) false = true) ∧
      C.output ≠ n + j ∧
      (∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
        (gateAt C k).op = GateOp.and ∧
        ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD (n + k) false = true →
          circuitFun n C z = true) := by
  obtain ⟨j, hj, hd, hreaders⟩ :=
    frLatestExists n (fun z => circuitFun n C z = false) C hm hr hex
  refine ⟨j, hj, hd, ?_, ?_⟩
  · intro hout
    obtain ⟨z, hz, hwire⟩ := hd
    change (C.wires (List.ofFn z)).getD C.output false = false at hz
    rw [hout, hwire] at hz
    contradiction
  · intro k hk hread
    obtain ⟨hop, hsafe⟩ := hreaders k hk hread
    refine ⟨hop, ?_⟩
    intro z hz
    cases hout : circuitFun n C z with
    | true => rfl
    | false => exact (hsafe ⟨z, hout, hz⟩).elim

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma saReplacement (n : ℕ) (C : Circuit) (pre post : List Gate) (g r : Gate)
    (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack n C)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrsize : r.inputs.length ≤ 2)
    (hrread : ∀ a ∈ r.inputs, a < n + pre.length)
    (hrle : ∀ z : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true)
    (hrsafe : ∀ z : Fin n → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      circuitFun n C z = true) :
    let D : Circuit := ⟨pre ++ r :: post, C.output⟩
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      (∀ z : Fin n → Bool, ∀ i,
        (C.wires (List.ofFn z)).getD i false = true →
        (D.wires (List.ofFn z)).getD i false = true) ∧
      (∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z) := by
  intro D
  have hm : Monotone2 D := by
    intro a ha
    change a ∈ pre ++ r :: post at ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hmono a (by rw [hsplit]; simp [ha])
    · exact ⟨hrop, hrsize⟩
    · exact hmono a (by rw [hsplit]; simp [ha])
  have hr : ReadsBack n D := by
    intro k hk a ha
    by_cases he : k = pre.length
    · subst k
      have har : a ∈ r.inputs := by simpa [gateAt, D] using ha
      exact hrread a har
    · have hg := lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k he
      have hak : a ∈ (gateAt C k).inputs := by
        change a ∈ ((pre ++ r :: post).getD k ⟨GateOp.or, []⟩).inputs at ha
        rw [hg] at ha
        simpa only [gateAt, hsplit] using ha
      exact hreads k (by simpa [hsplit, D] using hk) a hak
  have hle : ∀ z : Fin n → Bool, ∀ i,
      (C.wires (List.ofFn z)).getD i false = true →
      (D.wires (List.ofFn z)).getD i false = true := by
    intro z
    change ∀ i, (C.gates.foldl decStep (List.ofFn z)).getD i false = true →
      ((pre ++ r :: post).foldl decStep (List.ofFn z)).getD i false = true
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply decFoldMono post (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1)
    · simp [decStep]
    · exact lcSnocMono _ _ _ (hrle z)
  refine ⟨hm, hr, by simp [Circuit.size, hsplit, D], hle, ?_⟩
  intro z
  cases hout : circuitFun n C z with
  | true => exact hle z C.output hout
  | false =>
    have hrf : r.op.eval
        (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have ho := hrsafe z ht
      rw [hout] at ho
      contradiction
    have hgf : g.op.eval
        (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hr' := hrle z ht
      rw [hrf] at hr'
      contradiction
    have heq := lcReplaceEq n C pre post g r hsplit z (hrf.trans hgf.symm)
    change D.wires (List.ofFn z) = C.wires (List.ofFn z) at heq
    change (D.wires (List.ofFn z)).getD C.output false = false
    rw [heq]
    exact hout

lemma saSafeOperand (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack n C)
    (hop : g.op = GateOp.and) (w : ℕ) (hmem : w ∈ g.inputs)
    (hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true) :
    let D : Circuit := ⟨pre ++ ⟨GateOp.or, [w]⟩ :: post, C.output⟩
    Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      (∀ z : Fin n → Bool, ∀ i,
        (C.wires (List.ofFn z)).getD i false = true →
        (D.wires (List.ofFn z)).getD i false = true) ∧
      (∀ z : Fin n → Bool, circuitFun n D z = circuitFun n C z) := by
  have hw : w < n + pre.length := by
    apply hreads pre.length (by simp [hsplit])
    simpa [gateAt, hsplit] using hmem
  have hprefix (z : Fin n → Bool) :
      (C.wires (List.ofFn z)).getD w false =
        (pre.foldl decStep (List.ofFn z)).getD w false := by
    change (C.gates.foldl decStep (List.ofFn z)).getD w false = _
    rw [hsplit, List.foldl_append]
    apply lcRead
    simpa [lcLength] using hw
  apply saReplacement n C pre post g ⟨GateOp.or, [w]⟩ hsplit hmono hreads
    (Or.inr rfl) (by simp) (by simpa using hw)
  · intro z hz
    rw [hop] at hz
    simp only [GateOp.eval, List.all_map, List.all_eq_true] at hz
    simpa [GateOp.eval] using hz w hmem
  · intro z hz
    apply hsafe z
    rw [hprefix]
    simpa [GateOp.eval] using hz

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def edStepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def edRunWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl edStepWire init

lemma edGetD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

lemma edGetD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma edRunWires_len (gs : List Gate) (init : List Bool) :
    (edRunWires gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [edRunWires]
  | cons g gs ih =>
    change (edRunWires gs (edStepWire init g)).length = init.length + (gs.length + 1)
    rw [ih, edStepWire, List.length_append, List.length_singleton]
    omega

lemma edRunWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (edRunWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (edRunWires gs (edStepWire init g)).getD i false = init.getD i false
    have hlt : i < (edStepWire init g).length := by
      simp only [edStepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (edStepWire init g) hlt, edStepWire, edGetD_append_singleton, ite_eq_left hi]

lemma edRunWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (edRunWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (edRunWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (edRunWires gs (edStepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (edRunWires gs (edStepWire init g)).getD i false else false)
      have hlen : init.length < (edStepWire init g).length := by
        simp only [edStepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, edRunWires_getD_prefix gs (edStepWire init g) init.length hlen]
      have hhead : (edStepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [edStepWire, edGetD_append_singleton, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [ite_eq_left hi]
        have hi' : i < (edStepWire init g).length := by
          simp only [edStepWire, List.length_append, List.length_singleton]
          omega
        rw [edRunWires_getD_prefix gs (edStepWire init g) i hi', edStepWire,
          edGetD_append_singleton, ite_eq_left hi]
      · rw [ite_eq_right hi, edGetD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (edStepWire init g).length + k := by
        simp only [edStepWire, List.length_append, List.length_singleton]
        omega
      change (edRunWires gs (edStepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (edRunWires gs (edStepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (edStepWire init g) k hk

def edWireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma edWireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    edWireVal C x i = x ⟨i, hi⟩ := by
  unfold edWireVal
  change (edRunWires C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [edRunWires_getD_prefix C.gates (List.ofFn x) i (by simp [hi])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

lemma edWireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    edWireVal C x (n + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + j then edWireVal C x i else false) := by
  unfold edWireVal
  have h := edRunWires_getD_gate C.gates (List.ofFn x) j hj
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [hlen] at h
  exact h

lemma edWireVal_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : edWireVal C x w = false := by
  unfold edWireVal
  apply edGetD_of_ge
  change (edRunWires C.gates (List.ofFn x)).length ≤ w
  rw [edRunWires_len, List.length_ofFn]
  exact hw

def edShiftIdx (cut rep i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then rep else i - 1

lemma edShiftIdx_lt (cut rep i : ℕ) (h : i < cut) : edShiftIdx cut rep i = i := by
  unfold edShiftIdx; exact ite_eq_left h

lemma edShiftIdx_eq (cut rep : ℕ) : edShiftIdx cut rep cut = rep := by
  unfold edShiftIdx; rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]

lemma edShiftIdx_gt (cut rep i : ℕ) (h : ¬i < cut) (hne : i ≠ cut) :
    edShiftIdx cut rep i = i - 1 := by
  unfold edShiftIdx; rw [ite_eq_right h, ite_eq_right hne]

def edDelete (n : ℕ) (C : Circuit) (j rep : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map
      (fun g => ⟨g.op, g.inputs.map (edShiftIdx (n + j) rep)⟩),
    edShiftIdx (n + j) rep C.output⟩

lemma edDelete_wires {n : ℕ} (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (rep : ℕ)
    (hrep : rep < n + j ∨ rep = n + C.gates.length)
    (heq : ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep) :
    ∀ (x : Fin n → Bool) (w : ℕ),
      edWireVal (edDelete n C j rep) x (edShiftIdx (n + j) rep w) = edWireVal C x w := by
  let gs' : List Gate :=
    C.gates.take j ++ (C.gates.drop (j + 1)).map fun g =>
      ⟨g.op, g.inputs.map (edShiftIdx (n + j) rep)⟩
  let C' : Circuit := ⟨gs', edShiftIdx (n + j) rep C.output⟩
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs', hlen_take]
    omega
  have hagree : ∀ (x : Fin n → Bool) (w : ℕ),
      (w < n + j → edWireVal C' x w = edWireVal C x w) ∧
      (∀ k < C.gates.length - (j + 1), w = n + j + k → edWireVal C' x w = edWireVal C x (n + j + 1 + k)) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      constructor
      · intro hlt
        by_cases hlt_n : w < n
        · rw [edWireVal_input C' x w hlt_n, edWireVal_input C x w hlt_n]
        · have hj1 : w - n < j := by omega
          have hj1' : w - n < C'.gates.length := by omega
          have hj1c : w - n < C.gates.length := by omega
          have hw_eq : n + (w - n) = w := by omega
          rw [← hw_eq, edWireVal_gate C' x (w - n) hj1', edWireVal_gate C x (w - n) hj1c]
          have hg_eq : C'.gates[w - n] = C.gates[w - n] := by
            simp only [C', gs']
            rw [List.getElem_append_left (by rw [hlen_take]; exact hj1)]
            simp
          rw [hg_eq]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil, ite_eq_left hil]
            exact (ih i (by omega)).1 (by omega)
          · rw [ite_eq_right hil, ite_eq_right hil]
      · intro k hk hw
        subst hw
        have hk' : j + k < C'.gates.length := by omega
        have hkc : j + 1 + k < C.gates.length := by omega
        have hidx1 : n + (j + k) = n + j + k := by omega
        have hidx2 : n + (j + 1 + k) = n + j + 1 + k := by omega
        rw [← hidx1, ← hidx2, edWireVal_gate C' x (j + k) hk', edWireVal_gate C x (j + 1 + k) hkc]
        have hg_eq : C'.gates[j + k] =
            ⟨(C.gates[j + 1 + k]).op, (C.gates[j + 1 + k]).inputs.map (edShiftIdx (n + j) rep)⟩ := by
          simp only [C', gs']
          rw [List.getElem_append_right (by rw [hlen_take]; omega)]
          simp only [hlen_take, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_drop]
        rw [hg_eq, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        by_cases h1 : i < n + j
        · simp only [edShiftIdx_lt _ _ _ h1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          exact (ih i (by omega)).1 h1
        · by_cases h2 : i = n + j
          · subst h2
            simp only [edShiftIdx_eq]
            rw [ite_eq_left (show n + j < n + (j + 1 + k) by omega), heq x]
            rcases hrep with hrl | hre
            · rw [ite_eq_left (by omega)]
              exact (ih rep (by omega)).1 hrl
            · rw [hre, ite_eq_right (by omega), edWireVal_ge C x (n + C.gates.length) (le_refl _)]
          · simp only [edShiftIdx_gt _ _ _ h1 h2]
            by_cases h3 : i < n + (j + 1 + k)
            · rw [ite_eq_left (by omega), ite_eq_left h3]
              have h4 := (ih (i - 1) (by omega)).2 (i - 1 - (n + j)) (by omega) (by omega)
              have h5 : n + j + 1 + (i - 1 - (n + j)) = i := by omega
              rw [h5] at h4
              exact h4
            · rw [ite_eq_right (by omega), ite_eq_right h3]
  intro x w
  change edWireVal C' x (edShiftIdx (n + j) rep w) = edWireVal C x w
  simp only [edShiftIdx]
  by_cases h1 : w < n + j
  · rw [ite_eq_left h1]
    exact (hagree x w).1 h1
  · rw [ite_eq_right h1]
    by_cases h2 : w = n + j
    · rw [ite_eq_left h2, h2, heq x]
      rcases hrep with hrl | hre
      · exact (hagree x rep).1 hrl
      · rw [hre, edWireVal_ge C' x (n + C.gates.length) (by omega),
            edWireVal_ge C x (n + C.gates.length) (le_refl _)]
    · rw [ite_eq_right h2]
      by_cases h3 : w < n + C.gates.length
      · have h4 := (hagree x (w - 1)).2 (w - 1 - (n + j)) (by omega) (by omega)
        have h5 : n + j + 1 + (w - 1 - (n + j)) = w := by omega
        rw [h5] at h4
        exact h4
      · rw [edWireVal_ge C' x (w - 1) (by omega), edWireVal_ge C x w (by omega)]

lemma edDelete_size (n : ℕ) (C : Circuit) (j rep : ℕ) (hj : j < C.gates.length) :
    (edDelete n C j rep).size + 1 = C.size := by
  simp only [edDelete, Circuit.size, List.length_append, List.length_take,
    List.length_map, List.length_drop]
  omega

lemma edDelete_monotone (n : ℕ) (C : Circuit) (j rep : ℕ) (hm : Monotone2 C) :
    Monotone2 (edDelete n C j rep) := by
  intro g hg
  simp only [edDelete, List.mem_append, List.mem_map] at hg
  rcases hg with h | ⟨g₀, h, rfl⟩
  · exact hm g (List.mem_of_mem_take h)
  · obtain ⟨hop, hlen⟩ := hm g₀ (List.mem_of_mem_drop h)
    exact ⟨hop, by simpa using hlen⟩

lemma edDelete_before (n : ℕ) (C : Circuit) (j rep k : ℕ)
    (hj : j < C.gates.length) (hk : k < j) :
    gateAt (edDelete n C j rep) k = gateAt C k := by
  have hlen := edDelete_size n C j rep hj
  have hd : k < (edDelete n C j rep).gates.length := by
    change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
    omega
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hd, List.getD_eq_getElem _ _ (by omega)]
  simp only [edDelete]
  rw [List.getElem_append_left (by simp; omega)]
  simp

lemma edDelete_after (n : ℕ) (C : Circuit) (j rep k : ℕ)
    (hj : j < C.gates.length) (hk : k < (edDelete n C j rep).gates.length)
    (hjk : j ≤ k) :
    gateAt (edDelete n C j rep) k =
      ⟨(gateAt C (k + 1)).op, (gateAt C (k + 1)).inputs.map (edShiftIdx (n + j) rep)⟩ := by
  have hlen := edDelete_size n C j rep hj
  change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
  have hold : k + 1 < C.gates.length := by omega
  have ht : (C.gates.take j).length = j := List.length_take_of_le (by omega)
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hold]
  simp only [edDelete]
  rw [List.getElem_append_right (by omega)]
  simp only [ht, List.getElem_map, List.getElem_drop]
  have hi : j + 1 + (k - j) = k + 1 := by omega
  simp only [hi]

lemma edDelete_readsBack (n : ℕ) (C : Circuit) (j rep : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j) (hr : ReadsBack n C) :
    ReadsBack n (edDelete n C j rep) := by
  intro k hk i hi
  by_cases hkj : k < j
  · rw [edDelete_before n C j rep k hj hkj] at hi
    exact hr k (by omega) i hi
  · rw [edDelete_after n C j rep k hj hk (by omega)] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    have hlen := edDelete_size n C j rep hj
    change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
    have ha' := hr (k + 1) (by omega) a ha
    unfold edShiftIdx
    split_ifs <;> omega

lemma edDelete_eval {n : ℕ} (C : Circuit) (j rep : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j)
    (heq : ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep) :
    circuitFun n (edDelete n C j rep) = circuitFun n C := by
  funext x
  exact edDelete_wires C j hj rep (Or.inl hrep) heq x C.output

lemma edUnary_equal {n : ℕ} (C : Circuit) (j rep : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j)
    (hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or)
    (hins : (gateAt C j).inputs = [rep]) :
    ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep := by
  intro x
  rw [edWireVal_gate C x j hj]
  have hgate : C.gates[j] = gateAt C j := by
    exact (List.getD_eq_getElem _ _ hj).symm
  rw [hgate, hins]
  rcases hop with hop | hop <;> simp [hop, GateOp.eval, hrep]

lemma edDelete_and_source {n : ℕ} (C : Circuit) (j rep k : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j)
    (heq : ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep)
    (hk : k < (edDelete n C j rep).gates.length)
    (hand : (gateAt (edDelete n C j rep) k).op = .and) :
    ∃ l < C.gates.length, l ≠ j ∧ (gateAt C l).op = .and ∧
      ∀ x : Fin n → Bool,
        edWireVal (edDelete n C j rep) x (n + k) = edWireVal C x (n + l) := by
  by_cases hkj : k < j
  · refine ⟨k, by omega, by omega, ?_, ?_⟩
    · simpa [edDelete_before n C j rep k hj hkj] using hand
    · intro x
      simpa [edShiftIdx, show n + k < n + j by omega] using
        edDelete_wires C j hj rep (Or.inl hrep) heq x (n + k)
  · have hlen := edDelete_size n C j rep hj
    change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
    refine ⟨k + 1, by omega, by omega, ?_, ?_⟩
    · simpa [edDelete_after n C j rep k hj hk (by omega)] using hand
    · intro x
      have hidx : edShiftIdx (n + j) rep (n + (k + 1)) = n + k := by
        unfold edShiftIdx
        split_ifs <;> omega
      simpa [hidx] using edDelete_wires C j hj rep (Or.inl hrep) heq x (n + (k + 1))

lemma edUnary_delete {n : ℕ} (C : Circuit) (j rep : ℕ)
    (hm : Monotone2 C) (hr : ReadsBack n C) (hj : j < C.gates.length)
    (hins : (gateAt C j).inputs = [rep]) :
    Monotone2 (edDelete n C j rep) ∧ ReadsBack n (edDelete n C j rep) ∧
      (edDelete n C j rep).size + 1 = C.size ∧
      circuitFun n (edDelete n C j rep) = circuitFun n C := by
  have hrep : rep < n + j := hr j hj rep (by simp [hins])
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact ⟨edDelete_monotone n C j rep hm, edDelete_readsBack n C j rep hj hrep hr,
    edDelete_size n C j rep hj,
    edDelete_eval C j rep hj hrep (edUnary_equal C j rep hj hrep (hm _ hmem).1 hins)⟩

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma saStrictSafeOperand (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack n C)
    (hop : g.op = GateOp.and) (w : ℕ) (hmem : w ∈ g.inputs)
    (hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = C.size ∧
      circuitFun n D = circuitFun n C := by
  let E : Circuit := ⟨pre ++ ⟨GateOp.or, [w]⟩ :: post, C.output⟩
  obtain ⟨hm, hr, hs, _, hf⟩ :=
    saSafeOperand n C pre post g hsplit hmono hreads hop w hmem hsafe
  have hj : pre.length < E.gates.length := by simp [E]
  have hins : (gateAt E pre.length).inputs = [w] := by simp [gateAt, E]
  obtain ⟨hdm, hdr, hds, hdf⟩ := edUnary_delete E pre.length w hm hr hj hins
  exact ⟨_, hdm, hdr, hds.trans hs, hdf.trans (funext hf)⟩

lemma saMinimumAndOperandUnsafe (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : ℕ) (hmem : w ∈ (gateAt C j).inputs) :
    ∃ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true ∧
      circuitFun n C z = false := by
  by_contra hnone
  have hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true := by
    intro z hz
    cases hf : circuitFun n C z with
    | true => rfl
    | false => exact (hnone ⟨z, hz, hf⟩).elim
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hs : C.gates = pre ++ gateAt C j :: post := by
    dsimp [pre, post, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  obtain ⟨D, hdm, hdr, hds, hdf⟩ :=
    saStrictSafeOperand n C pre post (gateAt C j) hs hm hr hop w hmem hsafe
  have hle := hmin D hdm hdr hdf
  omega

lemma saMinimumSafeReaders (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (w : ℕ) (hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true) :
    ∀ j < C.gates.length, w ∈ (gateAt C j).inputs →
      (gateAt C j).op = GateOp.or := by
  intro j hj hmem
  have hjmem : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop := (hm (gateAt C j) hjmem).1
  change (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or at hop
  rcases hop with hop | hop
  · obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin j hj hop w hmem
    have ht := hsafe z hz
    rw [hf] at ht
    contradiction
  · exact hop

lemma frMinimumLatestReaders (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    ∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
      ∃ w < n + j, (gateAt C k).op = GateOp.and ∧
        ((gateAt C k).inputs = [n + j, w] ∨ (gateAt C k).inputs = [w, n + j]) := by
  intro k hk hread
  obtain ⟨hop, hclean⟩ := frLatestReaders n (fun z => circuitFun n C z = false)
    C hm hr j hd hlast k hk hread
  have hbefore (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : w ≤ n + j := by
    by_contra hn
    have hwn : n ≤ w := by omega
    have hwr := hr k hk w hw
    obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop w hw
    have hwd : frDirty n (fun z => circuitFun n C z = false) C (w - n) := by
      refine ⟨z, hf, ?_⟩
      simpa only [Nat.add_sub_of_le hwn] using hz
    have hx := hlast (w - n) (by omega) hwd
    omega
  have hother : ∃ w ∈ (gateAt C k).inputs, w ≠ n + j := by
    by_contra hn
    have hall : ∀ w ∈ (gateAt C k).inputs, w = n + j := by
      intro w hw
      by_contra hne
      exact hn ⟨w, hw, hne⟩
    obtain ⟨z, hz, hwire⟩ := hd
    apply hclean
    refine ⟨z, hz, ?_⟩
    rw [frGateEval n C hr k hk z, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true]
    intro w hw
    rw [hall w hw]
    exact hwire
  have hkmem : gateAt C k ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hlen := (hm (gateAt C k) hkmem).2
  obtain ⟨w, hw, hne⟩ := hother
  have hwlt : w < n + j := lt_of_le_of_ne (hbefore w hw) hne
  refine ⟨w, hwlt, hop, ?_⟩
  cases hin : (gateAt C k).inputs with
  | nil => simp [hin] at hread
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : n + j = a := by simpa [hin] using hread
      have hw' : w = a := by simpa [hin] using hw
      exact (hne (hw'.trans ha.symm)).elim
    | cons b tail =>
      have ht : tail = [] := by simpa [hin] using hlen
      subst tail
      simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hread hw
      rcases hread with ha | hb
      · subst a
        rcases hw with hw | hw
        · exact (hne hw).elim
        · subst b; exact Or.inl rfl
      · subst b
        rcases hw with hw | hw
        · subst a; exact Or.inr rfl
        · exact (hne hw).elim

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

def taTerm {m : ℕ} (t : Fin m ⊕ (Fin m × Fin m)) (x : Fin m → Bool) : Bool :=
  match t with
  | .inl i => x i
  | .inr (i, j) => x i && x j

def taTermCost {m : ℕ} (t : Fin m ⊕ (Fin m × Fin m)) : ℕ :=
  match t with
  | .inl _ => 0
  | .inr _ => 1

lemma taTermBld {m : ℕ} (t : Fin m ⊕ (Fin m × Fin m)) :
    CleanUpper.Bld m (fun _ => true) (taTerm t) (taTermCost t) := by
  cases t with
  | inl i => exact CleanUpper.bld_var _ i
  | inr p =>
    obtain ⟨i, j⟩ := p
    exact CleanUpper.bld_and (by intros; rfl)
      (CleanUpper.bld_var _ i) (CleanUpper.bld_var _ j)

lemma taAttach {m : ℕ} (ts : List (Fin m ⊕ (Fin m × Fin m))) :
    ∀ (F : (Fin m → Bool) → Bool) (s : ℕ),
      CleanUpper.Bld m (fun _ => true) F s →
      CleanUpper.Bld m (fun _ => true)
        (fun x => F x || ts.any (fun t => taTerm t x))
        (s + (ts.map taTermCost).sum + ts.length) := by
  induction ts with
  | nil =>
    intro F s h
    simpa using h
  | cons t ts ih =>
    intro F s h
    have h' := ih (fun x => F x || taTerm t x) (s + taTermCost t + 1)
      (CleanUpper.bld_or h (taTermBld t))
    have hc : s + taTermCost t + 1 + (ts.map taTermCost).sum + ts.length =
        s + ((t :: ts).map taTermCost).sum + (t :: ts).length := by simp; omega
    rw [hc] at h'
    apply CleanUpper.bld_congr h'
    intro x
    simp [Bool.or_assoc]

lemma taFactoredBld {m : ℕ} (u v : Fin m) (vs : List (Fin m))
    (ts : List (Fin m ⊕ (Fin m × Fin m))) :
    CleanUpper.Bld m (fun _ => true)
      (fun x => (v :: vs).any (fun w => x u && x w) || ts.any (fun t => taTerm t x))
      (vs.length + 1 + (ts.map taTermCost).sum + ts.length) := by
  have h := CleanUpper.bld_and (by intros; rfl) (CleanUpper.bld_var (fun _ => true) u)
    (CleanUpper.bld_anyList (fun _ => true) vs v)
  have h' := taAttach ts _ (vs.length + 1) (by simpa using h)
  apply CleanUpper.bld_congr h'
  intro x
  cases x u <;> simp

lemma taAppend (n : ℕ) (P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (F : (Fin (n + P.size) → Bool) → Bool) (s : ℕ)
    (hb : CleanUpper.Bld (n + P.size) (fun _ => true) F s) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ P.size + s ∧
      ∀ z : Fin n → Bool, circuitFun n D z =
        F (fun i => (P.wires (List.ofFn z)).getD i false) := by
  obtain ⟨gs, out, hok, hn, hlen, _, hread, _, hev⟩ := hb (n + P.size) le_rfl
  let D : Circuit := ⟨P.gates ++ gs, out⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ P.gates ++ gs at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hm g hg
    · refine ⟨?_, (hok g hg).2⟩
      rcases (hok g hg).1 with hand | hor | hnot
      · exact Or.inl hand
      · exact Or.inr hor
      · exact (hn g hg hnot).elim
  · change CleanUpper.Reads n (P.gates ++ gs)
    exact CleanUpper.reads_append n P.gates gs hr hread
  · simp only [D, Circuit.size, List.length_append]
    omega
  · intro z
    have hw : (P.wires (List.ofFn z)).length = n + P.size := by
      change (P.gates.foldl decStep (List.ofFn z)).length = _
      simp [lcLength, Circuit.size]
    have he := hev (P.wires (List.ofFn z)) hw
    change ((P.gates ++ gs).foldl decStep (List.ofFn z)).getD out false = _
    rw [List.foldl_append]
    exact he

lemma taFactorCircuit (n : ℕ) (P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (u v : Fin (n + P.size)) (vs : List (Fin (n + P.size)))
    (ts : List (Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      D.size ≤ P.size + vs.length + 1 + (ts.map taTermCost).sum + ts.length ∧
      ∀ z : Fin n → Bool,
        let x : Fin (n + P.size) → Bool := fun i => (P.wires (List.ofFn z)).getD i false
        circuitFun n D z =
          ((v :: vs).any (fun w => x u && x w) || ts.any (fun t => taTerm t x)) := by
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := taAppend n P hm hr _ _ (taFactoredBld u v vs ts)
  refine ⟨D, hdm, hdr, ?_, hdf⟩
  omega

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma frAndAfterLatest (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j)
    (k : ℕ) (hjk : j < k) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a ≠ b ∧
      a ≤ n + j ∧ b ≤ n + j := by
  have hclean : ¬ frDirty n (fun z => circuitFun n C z = false) C k := by
    intro hd'
    have h := hlast k hk hd'
    omega
  have hbefore (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : w ≤ n + j := by
    by_contra hn
    have hwn : n ≤ w := by omega
    have hwr := hr k hk w hw
    obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop w hw
    have hwd : frDirty n (fun z => circuitFun n C z = false) C (w - n) := by
      refine ⟨z, hf, ?_⟩
      simpa only [Nat.add_sub_of_le hwn] using hz
    have hx := hlast (w - n) (by omega) hwd
    omega
  have hkmem : gateAt C k ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hlen := (hm (gateAt C k) hkmem).2
  cases hin : (gateAt C k).inputs with
  | nil =>
    obtain ⟨z, hz, _⟩ := hd
    exact (hclean ⟨z, hz, by rw [frGateEval n C hr k hk z, hop, hin]; rfl⟩).elim
  | cons a rest =>
    have ha : a ∈ (gateAt C k).inputs := by simp [hin]
    cases rest with
    | nil =>
      obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop a ha
      exact (hclean ⟨z, hf, by
        rw [frGateEval n C hr k hk z, hop, hin]
        simpa [GateOp.eval] using hz⟩).elim
    | cons b tail =>
      have ht : tail = [] := by simpa [hin] using hlen
      subst tail
      have hb : b ∈ (gateAt C k).inputs := by simp [hin]
      refine ⟨a, b, rfl, ?_, hbefore a ha, hbefore b hb⟩
      intro hab
      subst b
      obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop a ha
      apply hclean
      refine ⟨z, hf, ?_⟩
      rw [frGateEval n C hr k hk z, hop, hin]
      simpa [GateOp.eval] using hz

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

def ofExpand (S : Finset ℕ) (w : ℕ) (ins : List ℕ) : Finset ℕ :=
  if w ∈ S then S.erase w ∪ ins.toFinset else S

noncomputable def ofAny (val : ℕ → Bool) (S : Finset ℕ) : Bool :=
  S.toList.any val

lemma ofAny_true (val : ℕ → Bool) (S : Finset ℕ) :
    ofAny val S = true ↔ ∃ w ∈ S, val w = true := by
  simp [ofAny, List.any_eq_true]

lemma ofExpand_card (S : Finset ℕ) (w : ℕ) (ins : List ℕ)
    (hbin : ins.length ≤ 2) :
    (ofExpand S w ins).card ≤ S.card + if w ∈ S then 1 else 0 := by
  by_cases hw : w ∈ S
  · rw [ofExpand, ite_eq_left hw, ite_eq_left hw]
    have he := Finset.card_erase_add_one hw
    have hu := Finset.card_union_le (S.erase w) ins.toFinset
    have hi := ins.toFinset_card_le
    omega
  · simp [ofExpand, hw]

lemma ofExpand_card_le (S : Finset ℕ) (w : ℕ) (ins : List ℕ)
    (hbin : ins.length ≤ 2) :
    (ofExpand S w ins).card ≤ S.card + 1 := by
  have h := ofExpand_card S w ins hbin
  split_ifs at h <;> omega

lemma ofExpand_semantics (val : ℕ → Bool) (S : Finset ℕ)
    (w : ℕ) (ins : List ℕ) (hw : val w = ins.any val) :
    ofAny val S = ofAny val (ofExpand S w ins) := by
  rw [Bool.eq_iff_iff, ofAny_true, ofAny_true]
  by_cases hmem : w ∈ S
  · rw [ofExpand, ite_eq_left hmem]
    constructor
    · rintro ⟨v, hv, hvtrue⟩
      by_cases hvw : v = w
      · subst v
        rw [hw, List.any_eq_true] at hvtrue
        obtain ⟨a, ha, hatrue⟩ := hvtrue
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), hatrue⟩
      · exact ⟨v, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvw, hv⟩), hvtrue⟩
    · rintro ⟨v, hv, hvtrue⟩
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ⟨v, (Finset.mem_erase.mp hv).2, hvtrue⟩
      · refine ⟨w, hmem, ?_⟩
        rw [hw, List.any_eq_true]
        exact ⟨v, List.mem_toFinset.mp hv, hvtrue⟩
  · simp [ofExpand, hmem]

def ofRun : List (ℕ × List ℕ) → Finset ℕ → Finset ℕ
  | [], S => S
  | (w, ins) :: rest, S => ofRun rest (ofExpand S w ins)

def ofCost : List (ℕ × List ℕ) → Finset ℕ → ℕ
  | [], _ => 0
  | (w, ins) :: rest, S =>
      (if w ∈ S then 1 else 0) + ofCost rest (ofExpand S w ins)

lemma ofRun_card (steps : List (ℕ × List ℕ))
    (hbin : ∀ e ∈ steps, e.2.length ≤ 2) (S : Finset ℕ) :
    (ofRun steps S).card ≤ S.card + ofCost steps S := by
  induction steps generalizing S with
  | nil => simp [ofRun, ofCost]
  | cons e rest ih =>
    obtain ⟨w, ins⟩ := e
    have hstep := ofExpand_card S w ins (hbin (w, ins) (by simp))
    have hrest := ih (fun e he => hbin e (by simp [he])) (ofExpand S w ins)
    simp only [ofRun, ofCost]
    omega

lemma ofCost_le_length (steps : List (ℕ × List ℕ)) (S : Finset ℕ) :
    ofCost steps S ≤ steps.length := by
  induction steps generalizing S with
  | nil => simp [ofCost]
  | cons e rest ih =>
    obtain ⟨w, ins⟩ := e
    have hrest := ih (ofExpand S w ins)
    simp only [ofCost, List.length_cons]
    split_ifs <;> omega

lemma ofRun_semantics (val : ℕ → Bool) (steps : List (ℕ × List ℕ))
    (heq : ∀ e ∈ steps, val e.1 = e.2.any val) (S : Finset ℕ) :
    ofAny val S = ofAny val (ofRun steps S) := by
  induction steps generalizing S with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨w, ins⟩ := e
    exact (ofExpand_semantics val S w ins (heq (w, ins) (by simp))).trans
      (ih (fun e he => heq e (by simp [he])) (ofExpand S w ins))

lemma ofRun_singleton_card (steps : List (ℕ × List ℕ))
    (hbin : ∀ e ∈ steps, e.2.length ≤ 2) (output : ℕ) :
    (ofRun steps {output}).card ≤ ofCost steps {output} + 1 ∧
      (ofRun steps {output}).card ≤ steps.length + 1 := by
  have hc := ofRun_card steps hbin {output}
  have hl := ofCost_le_length steps {output}
  simp only [Finset.card_singleton] at hc
  omega

lemma ofRun_singleton_semantics (val : ℕ → Bool) (steps : List (ℕ × List ℕ))
    (heq : ∀ e ∈ steps, val e.1 = e.2.any val) (output : ℕ) :
    val output = ofAny val (ofRun steps {output}) := by
  simpa [ofAny] using ofRun_semantics val steps heq {output}

end PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

noncomputable def otSteps (n : ℕ) (C : Circuit) (p : ℕ) : ℕ → List (ℕ × List ℕ)
  | 0 => []
  | m + 1 => by
      classical
      exact if (gateAt C (p + m)).op = GateOp.or then
        (n + (p + m), (gateAt C (p + m)).inputs) :: otSteps n C p m
      else otSteps n C p m

lemma otSteps_spec (n : ℕ) (C : Circuit) (p m : ℕ) :
    ∀ e ∈ otSteps n C p m, ∃ k, p ≤ k ∧ k < p + m ∧
      (gateAt C k).op = GateOp.or ∧ e = (n + k, (gateAt C k).inputs) := by
  classical
  induction m with
  | zero => simp [otSteps]
  | succ m ih =>
    intro e he
    by_cases hop : (gateAt C (p + m)).op = GateOp.or
    · simp only [otSteps, ite_eq_left hop, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨p + m, by omega, by omega, hop, rfl⟩
      · obtain ⟨k, hk, hkm, hko, heq⟩ := ih e he
        exact ⟨k, hk, by omega, hko, heq⟩
    · rw [otSteps, ite_eq_right hop] at he
      obtain ⟨k, hk, hkm, hko, heq⟩ := ih e he
      exact ⟨k, hk, by omega, hko, heq⟩

open Classical in
lemma otSteps_length (n : ℕ) (C : Circuit) (p m : ℕ) :
    (otSteps n C p m).length =
      ((Finset.range m).filter fun j => (gateAt C (p + j)).op = GateOp.or).card := by
  classical
  induction m with
  | zero => simp [otSteps]
  | succ m ih =>
    by_cases hop : (gateAt C (p + m)).op = GateOp.or
    · simp [otSteps, hop, Finset.range_add_one, Finset.filter_insert, ih]
    · simp [otSteps, hop, Finset.range_add_one, Finset.filter_insert, ih]

lemma otRun_roots (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (p m : ℕ) (hpm : p + m ≤ C.gates.length) (S : Finset ℕ) :
    ∀ w ∈ ofRun (otSteps n C p m) S,
      w < n + p ∨
      (∃ k, p ≤ k ∧ k < p + m ∧ (gateAt C k).op = GateOp.and ∧ w = n + k) ∨
      (w ∈ S ∧ n + (p + m) ≤ w) := by
  classical
  induction m generalizing S with
  | zero =>
    intro w hw
    simp only [otSteps, ofRun] at hw
    by_cases h : w < n + p
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hw, by omega⟩)
  | succ m ih =>
    have hk : p + m < C.gates.length := by omega
    intro w hw
    by_cases hop : (gateAt C (p + m)).op = GateOp.or
    · simp only [otSteps, ite_eq_left hop, ofRun] at hw
      obtain hlow | hmid | hhigh := ih (by omega) _ w hw
      · exact Or.inl hlow
      · obtain ⟨k, hk1, hk2, hka, hwe⟩ := hmid
        exact Or.inr (Or.inl ⟨k, hk1, by omega, hka, hwe⟩)
      · obtain ⟨hmem, hbound⟩ := hhigh
        by_cases hactive : n + (p + m) ∈ S
        · rw [ofExpand, ite_eq_left hactive] at hmem
          rcases Finset.mem_union.mp hmem with hold | hins
          · obtain ⟨hne, hws⟩ := Finset.mem_erase.mp hold
            exact Or.inr (Or.inr ⟨hws, by omega⟩)
          · have hlt := hr (p + m) hk w (List.mem_toFinset.mp hins)
            omega
        · rw [ofExpand, ite_eq_right hactive] at hmem
          have hne : w ≠ n + (p + m) := by
            intro he
            exact hactive (he ▸ hmem)
          exact Or.inr (Or.inr ⟨hmem, by omega⟩)
    · rw [otSteps, ite_eq_right hop] at hw
      obtain hlow | hmid | hhigh := ih (by omega) _ w hw
      · exact Or.inl hlow
      · obtain ⟨k, hk1, hk2, hka, hwe⟩ := hmid
        exact Or.inr (Or.inl ⟨k, hk1, by omega, hka, hwe⟩)
      · obtain ⟨hmem, hbound⟩ := hhigh
        by_cases he : w = n + (p + m)
        · have hgate : gateAt C (p + m) ∈ C.gates := by
            unfold gateAt
            rw [List.getD_eq_getElem _ _ hk]
            exact List.getElem_mem hk
          have hand : (gateAt C (p + m)).op = GateOp.and := by
            have hh := (hm _ hgate).1
            exact hh.resolve_right hop
          exact Or.inr (Or.inl ⟨p + m, by omega, by omega, hand, he⟩)
        · exact Or.inr (Or.inr ⟨hmem, by omega⟩)

noncomputable def otFrontier (n : ℕ) (C : Circuit) (p : ℕ) : Finset ℕ :=
  ofRun (otSteps n C p (C.gates.length - p)) {C.output}

lemma otFrontier_roots (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (p : ℕ) (hp : p ≤ C.gates.length) (hout : C.output < n + C.gates.length) :
    ∀ w ∈ otFrontier n C p, w < n + p ∨
      ∃ k, p ≤ k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ w = n + k := by
  intro w hw
  obtain hlow | hmid | hhigh := otRun_roots n C hm hr p (C.gates.length - p)
    (by omega) {C.output} w hw
  · exact Or.inl hlow
  · obtain ⟨k, hk1, hk2, hka, hwe⟩ := hmid
    exact Or.inr ⟨k, hk1, by omega, hka, hwe⟩
  · obtain ⟨hmem, hbound⟩ := hhigh
    simp only [Finset.mem_singleton] at hmem
    omega

open Classical in
lemma otFrontier_card (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (p : ℕ) (hp : p ≤ C.gates.length) :
    (otFrontier n C p).card ≤
      ((Finset.range (C.gates.length - p)).filter
        fun j => (gateAt C (p + j)).op = GateOp.or).card + 1 := by
  classical
  have hbin : ∀ e ∈ otSteps n C p (C.gates.length - p), e.2.length ≤ 2 := by
    intro e he
    obtain ⟨k, hk1, hk2, hko, rfl⟩ := otSteps_spec n C p _ e he
    have hk : k < C.gates.length := by omega
    have hgate : gateAt C k ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    exact (hm _ hgate).2
  have hc := (ofRun_singleton_card (otSteps n C p (C.gates.length - p)) hbin C.output).2
  rw [otSteps_length] at hc
  exact hc

lemma otFrontier_semantics (n : ℕ) (C : Circuit) (hr : ReadsBack n C)
    (p : ℕ) (hp : p ≤ C.gates.length) (z : Fin n → Bool) :
    circuitFun n C z =
      ofAny (fun w => (C.wires (List.ofFn z)).getD w false) (otFrontier n C p) := by
  refine ofRun_singleton_semantics (fun w => (C.wires (List.ofFn z)).getD w false)
    (otSteps n C p (C.gates.length - p)) ?_ C.output
  intro e he
  obtain ⟨k, hk1, hk2, hko, rfl⟩ := otSteps_spec n C p _ e he
  have hk : k < C.gates.length := by omega
  have hg := frGateEval n C hr k hk z
  simpa [hko, GateOp.eval, List.any_map] using hg

lemma otFrontier_safe (n : ℕ) (C : Circuit) (hr : ReadsBack n C)
    (p : ℕ) (hp : p ≤ C.gates.length) (w : ℕ) (hw : w ∈ otFrontier n C p)
    (z : Fin n → Bool) (hz : (C.wires (List.ofFn z)).getD w false = true) :
    circuitFun n C z = true := by
  rw [otFrontier_semantics n C hr p hp z, ofAny_true]
  exact ⟨w, hw, hz⟩

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma saMinimumOutputValid (n : ℕ) (C : Circuit)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) : C.output < n + C.gates.length := by
  by_contra hn
  let D : Circuit := ⟨[], n⟩
  have hfun : circuitFun n D = circuitFun n C := by
    funext z
    have hc : circuitFun n C z = false := by
      change (C.wires (List.ofFn z)).getD C.output false = false
      apply List.getD_eq_default
      change (C.gates.foldl decStep (List.ofFn z)).length ≤ C.output
      rw [lcLength, List.length_ofFn]
      omega
    have hd : circuitFun n D z = false := by
      change (List.ofFn z).getD n false = false
      apply List.getD_eq_default
      simp
    exact hd.trans hc.symm
  have hdm : Monotone2 D := by intro g hg; simp [D] at hg
  have hdr : ReadsBack n D := by intro k hk; simp [D] at hk
  have hs := hmin D hdm hdr hfun
  change C.gates.length ≤ 0 at hs
  omega

end PEqualNP.Outside.L_meta_3451


namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma raFiniteFactor (n : ℕ) (C P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (R A K : Finset ℕ) (hKR : K ⊆ R) (hKA : K ⊆ A)
    (u : Fin (n + P.size)) (partner : ℕ → Fin (n + P.size))
    (term : ℕ → Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))
    (hsem : ∀ z : Fin n → Bool,
      let x : Fin (n + P.size) → Bool := fun i => (P.wires (List.ofFn z)).getD i false
      circuitFun n C z =
        ((K.toList.map partner).any (fun w => x u && x w) ||
          ((R \ K).toList.map term).any (fun t => taTerm t x)))
    (hcost : ∀ w ∈ R \ K, taTermCost (term w) ≤ if w ∈ A then 1 else 0)
    (hbudget : P.size + R.card + A.card ≤ C.size + 1) : K.card ≤ 1 := by
  classical
  by_contra hlarge
  have hk : 2 ≤ K.card := by omega
  obtain ⟨v, vs, hv⟩ : ∃ v vs, K.toList.map partner = v :: vs := by
    cases hl : K.toList.map partner with
    | nil =>
      have hh := congrArg List.length hl
      simp only [List.length_map, Finset.length_toList, List.length_nil] at hh
      omega
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hlen : vs.length + 1 = K.card := by
    have hh := congrArg List.length hv
    simpa only [List.length_map, Finset.length_toList, List.length_cons] using hh.symm
  let ts := (R \ K).toList.map term
  have htlen : ts.length + K.card = R.card := by
    simpa only [ts, List.length_map, Finset.length_toList] using Finset.card_sdiff_add_card_eq_card hKR
  have hsum : (ts.map taTermCost).sum ≤ (A \ K).card := by
    have he : (ts.map taTermCost).sum = ∑ w ∈ R \ K, taTermCost (term w) := by
      simp [ts, List.map_map]
    rw [he]
    calc
      _ ≤ ∑ w ∈ R \ K, if w ∈ A then 1 else 0 := Finset.sum_le_sum hcost
      _ = ((R \ K).filter (fun w => w ∈ A)).card := by
        simp
        congr 1
      _ ≤ (A \ K).card := Finset.card_le_card (by
        intro w hw
        obtain ⟨hw, ha⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_sdiff.mpr ⟨ha, (Finset.mem_sdiff.mp hw).2⟩)
  have hacard : (A \ K).card + K.card = A.card := Finset.card_sdiff_add_card_eq_card hKA
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := taFactorCircuit n P hm hr u v vs ts
  have heq : circuitFun n D = circuitFun n C := by
    funext z
    rw [hdf z, hsem z, hv]
  have hle := hmin D hdm hdr heq
  omega

def raPrefix (C : Circuit) (p : ℕ) : Circuit := ⟨C.gates.take p, C.output⟩

lemma raPrefix_size (C : Circuit) (p : ℕ) (hp : p ≤ C.gates.length) :
    (raPrefix C p).size = p := List.length_take_of_le hp

lemma raPrefix_mono (C : Circuit) (p : ℕ) (hm : Monotone2 C) : Monotone2 (raPrefix C p) := by
  intro g hg
  exact hm g (List.mem_of_mem_take hg)

lemma raPrefix_reads (n : ℕ) (C : Circuit) (p : ℕ) (hr : ReadsBack n C) :
    ReadsBack n (raPrefix C p) := by
  intro k hk a ha
  change k < (C.gates.take p).length at hk
  have hks : k < min p C.gates.length := by simpa [raPrefix] using hk
  have hkp := (lt_min_iff.mp hks).1
  have hkc := (lt_min_iff.mp hks).2
  have he : gateAt (raPrefix C p) k = gateAt C k := by
    change (C.gates.take p).getD k _ = C.gates.getD k _
    rw [List.getD_eq_getElem (C.gates.take p) _ hk, List.getD_eq_getElem C.gates _ hkc]
    simp

  exact hr k hkc a (he ▸ ha)

lemma raPrefix_wire (n : ℕ) (C : Circuit) (p : ℕ) (hp : p ≤ C.gates.length)
    (z : Fin n → Bool) (w : ℕ) (hw : w < n + p) :
    ((raPrefix C p).wires (List.ofFn z)).getD w false =
      (C.wires (List.ofFn z)).getD w false := by
  have hs : C.gates = C.gates.take p ++ C.gates.drop p := (List.take_append_drop p C.gates).symm
  change ((C.gates.take p).foldl decStep (List.ofFn z)).getD w false =
    (C.gates.foldl decStep (List.ofFn z)).getD w false
  conv_rhs => rw [hs, List.foldl_append]
  symm
  apply lcRead
  simpa only [lcLength, List.length_ofFn, List.length_take_of_le hp] using hw

noncomputable def raTailAnd (n : ℕ) (C : Circuit) (p : ℕ) : Finset ℕ := by
  classical
  exact (((Finset.range (C.gates.length - p)).filter
    (fun i => (gateAt C (p + i)).op = GateOp.and)).image (fun i => n + (p + i)))

lemma raTailAnd_mem (n : ℕ) (C : Circuit) (p w : ℕ) :
    w ∈ raTailAnd n C p ↔ ∃ k, p ≤ k ∧ k < C.gates.length ∧
      (gateAt C k).op = GateOp.and ∧ w = n + k := by
  classical
  constructor
  · intro hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hi, hop⟩ := Finset.mem_filter.mp hi
    have hi' := Finset.mem_range.mp hi
    exact ⟨p + i, by omega, by omega, hop, rfl⟩
  · rintro ⟨k, hkp, hk, hop, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k - p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_of_le hkp] using hop
    · omega

lemma raTailAnd_budget (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (p : ℕ) (hp : p ≤ C.gates.length) :
    (raPrefix C p).size + (otFrontier n C p).card + (raTailAnd n C p).card ≤ C.size + 1 := by
  classical
  let S := Finset.range (C.gates.length - p)
  let A := S.filter (fun i => (gateAt C (p + i)).op = GateOp.and)
  let O := S.filter (fun i => (gateAt C (p + i)).op = GateOp.or)
  have hdis : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have ha := (Finset.mem_filter.mp hi).2
    have ho := (Finset.mem_filter.mp hj).2
    rw [ha] at ho
    cases ho
  have hunion : A ∪ O = S := by
    ext i
    simp only [A, O, Finset.mem_union, Finset.mem_filter]
    constructor
    · tauto
    · intro hi
      have hk : p + i < C.gates.length := by
        have hh := Finset.mem_range.mp hi
        omega
      have hg : gateAt C (p + i) ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      rcases (hm _ hg).1 with ha | ho
      · exact Or.inl ⟨hi, ha⟩
      · exact Or.inr ⟨hi, ho⟩
  have hsum : A.card + O.card = C.gates.length - p := by
    rw [← Finset.card_union_of_disjoint hdis, hunion]
    exact Finset.card_range _
  have ha : (raTailAnd n C p).card = A.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    change n + (p + a) = n + (p + b) at hab
    omega
  have hr := otFrontier_card n C hm p hp
  change (otFrontier n C p).card ≤ O.card + 1 at hr
  rw [raPrefix_size C p hp, ha]
  change p + (otFrontier n C p).card + A.card ≤ C.gates.length + 1
  omega

noncomputable def raReaderRoots (n : ℕ) (C : Circuit) (j : ℕ) : Finset ℕ := by
  classical
  exact (otFrontier n C (j + 1)).filter (fun w =>
    w ∈ raTailAnd n C (j + 1) ∧ n + j ∈ (gateAt C (w - n)).inputs)

lemma raMinimumReaderCard (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output < n + C.gates.length)
    (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    (raReaderRoots n C j).card ≤ 1 := by
  classical
  let p := j + 1
  have hp : p ≤ C.gates.length := hj
  let P := raPrefix C p
  have hPs : P.size = p := raPrefix_size C p hp
  let R := otFrontier n C p
  let A := raTailAnd n C p
  let K := raReaderRoots n C j
  have hKR : K ⊆ R := Finset.filter_subset _ _
  have hKA : K ⊆ A := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2.1
  let u : Fin (n + P.size) := ⟨n + j, by rw [hPs]; dsimp [p]; omega⟩
  have hpartners : ∀ w : ℕ, ∃ v : Fin (n + P.size), w ∈ K →
      ∀ z : Fin n → Bool,
        (C.wires (List.ofFn z)).getD w false =
          ((P.wires (List.ofFn z)).getD u false && (P.wires (List.ofFn z)).getD v false) := by
    intro w
    by_cases hw : w ∈ K
    · obtain ⟨k, hkp, hk, hop, hwk⟩ := (raTailAnd_mem n C p w).mp (hKA hw)
      subst w
      have hread : n + j ∈ (gateAt C k).inputs := by
        simpa using (Finset.mem_filter.mp hw).2.2
      obtain ⟨a, ha, _, hin⟩ := frMinimumLatestReaders n C hm hr hmin j hd hlast k hk hread
      let v : Fin (n + P.size) := ⟨a, by rw [hPs]; dsimp [p]; omega⟩
      refine ⟨v, fun _ z => ?_⟩
      change (C.wires (List.ofFn z)).getD (n + k) false =
        (((raPrefix C p).wires (List.ofFn z)).getD (n + j) false &&
          ((raPrefix C p).wires (List.ofFn z)).getD a false)
      rw [raPrefix_wire n C p hp z (n + j) (by dsimp [p]; omega),
        raPrefix_wire n C p hp z a (by dsimp [p]; omega), frGateEval n C hr k hk z, hop]
      rcases hin with hin | hin <;> simp [hin, GateOp.eval, Bool.and_comm]
    · exact ⟨u, fun h => (hw h).elim⟩
  choose partner hpartner using hpartners
  have hterms : ∀ w : ℕ,
      ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
        w ∈ R →
          (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
            taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
          taTermCost t ≤ if w ∈ A then 1 else 0 := by
    intro w
    by_cases hw : w ∈ R
    · rcases otFrontier_roots n C hm hr p hp hout w hw with hlow | htail
      · let v : Fin (n + P.size) := ⟨w, by rw [hPs]; exact hlow⟩
        refine ⟨.inl v, fun _ => ⟨?_, ?_⟩⟩
        · intro z
          exact (raPrefix_wire n C p hp z w hlow).symm
        · simp [taTermCost]
      · obtain ⟨k, hkp, hk, hop, hwk⟩ := htail
        obtain ⟨a, b, hins, _, ha, hb⟩ :=
          frAndAfterLatest n C hm hr hmin j hd hlast k (by dsimp [p] at hkp; omega) hk hop
        let va : Fin (n + P.size) := ⟨a, by rw [hPs]; dsimp [p]; omega⟩
        let vb : Fin (n + P.size) := ⟨b, by rw [hPs]; dsimp [p]; omega⟩
        refine ⟨.inr (va, vb), fun _ => ⟨?_, ?_⟩⟩
        · intro z
          subst w
          change (C.wires (List.ofFn z)).getD (n + k) false =
            (((raPrefix C p).wires (List.ofFn z)).getD a false &&
              ((raPrefix C p).wires (List.ofFn z)).getD b false)
          rw [raPrefix_wire n C p hp z a (by dsimp [p]; omega),
            raPrefix_wire n C p hp z b (by dsimp [p]; omega), frGateEval n C hr k hk z, hop, hins]
          simp [GateOp.eval]
        · have hwA : w ∈ A := (raTailAnd_mem n C p w).mpr ⟨k, hkp, hk, hop, hwk⟩
          simp [taTermCost, hwA]
    · exact ⟨.inl u, fun h => (hw h).elim⟩
  choose term hterm using hterms
  apply raFiniteFactor n C P (raPrefix_mono C p hm) (raPrefix_reads n C p hr)
    hmin R A K hKR hKA u partner term
  · intro z
    rw [otFrontier_semantics n C hr p hp z]
    rw [Bool.eq_iff_iff, ofAny_true, Bool.or_eq_true]
    simp only [List.any_map, List.any_eq_true, Finset.mem_toList]
    constructor
    · rintro ⟨w, hw, ht⟩
      by_cases hk : w ∈ K
      · exact Or.inl ⟨w, hk, (hpartner w hk z).symm.trans ht⟩
      · exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hk⟩, ((hterm w hw).1 z).symm.trans ht⟩
    · rintro (⟨w, hw, ht⟩ | ⟨w, hw, ht⟩)
      · exact ⟨w, hKR hw, (hpartner w hw z).trans ht⟩
      · exact ⟨w, (Finset.mem_sdiff.mp hw).1,
          ((hterm w (Finset.mem_sdiff.mp hw).1).1 z).trans ht⟩
  · intro w hw
    exact (hterm w (Finset.mem_sdiff.mp hw).1).2
  · exact raTailAnd_budget n C hm p hp

end PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma raUnfactoredContradiction (n : ℕ) (C P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (R A : Finset ℕ) (hR : R.Nonempty)
    (term : ℕ → Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))
    (hsem : ∀ z : Fin n → Bool,
      circuitFun n C z = (R.toList.map term).any
        (fun t => taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)))
    (hcost : ∀ w ∈ R, taTermCost (term w) ≤ if w ∈ A then 1 else 0)
    (hbudget : P.size + R.card + A.card ≤ C.size) : False := by
  classical
  obtain ⟨t, ts, ht⟩ : ∃ t ts, R.toList.map term = t :: ts := by
    cases hl : R.toList.map term with
    | nil =>
      have hh := congrArg List.length hl
      simp only [List.length_map, Finset.length_toList, List.length_nil] at hh
      exact (Finset.card_ne_zero.mpr hR hh).elim
    | cons t ts => exact ⟨t, ts, rfl⟩
  have hlen : ts.length + 1 = R.card := by
    have hh := congrArg List.length ht
    simpa only [List.length_map, Finset.length_toList, List.length_cons] using hh.symm
  have hsum : taTermCost t + (ts.map taTermCost).sum ≤ A.card := by
    have he : ((R.toList.map term).map taTermCost).sum = ∑ w ∈ R, taTermCost (term w) := by
      simp [List.map_map]
    rw [ht] at he
    simp only [List.map_cons, List.sum_cons] at he
    rw [he]
    calc
      _ ≤ ∑ w ∈ R, if w ∈ A then 1 else 0 := Finset.sum_le_sum hcost
      _ = (R ∩ A).card := by simp
      _ ≤ A.card := Finset.card_le_card Finset.inter_subset_right
  have hb := taAttach ts (taTerm t) (taTermCost t) (taTermBld t)
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := taAppend n P hm hr _ _ hb
  have heq : circuitFun n D = circuitFun n C := by
    funext z
    rw [hdf z, hsem z, ht]
    rfl
  have hle := hmin D hdm hdr heq
  omega

lemma raMinimumReaderOne (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    (raReaderRoots n C j).card = 1 := by
  classical
  have hout := saMinimumOutputValid n C hmin j hj
  have hle := raMinimumReaderCard n C hm hr hmin j hj hout hd hlast
  by_contra hnot
  have hz : (raReaderRoots n C j).card = 0 := by omega
  have hK : raReaderRoots n C j = ∅ := Finset.card_eq_zero.mp hz
  let R := otFrontier n C (j + 1)
  let A := raTailAnd n C (j + 1)
  have hp : j + 1 ≤ C.gates.length := hj
  have hR : R.Nonempty := by
    by_contra hn
    have hRE : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    let D : Circuit := ⟨[], n⟩
    have hfun : circuitFun n D = circuitFun n C := by
      funext z
      have hc : circuitFun n C z = false := by
        rw [otFrontier_semantics n C hr (j + 1) hp z]
        change ofAny _ R = false
        rw [hRE]
        simp [ofAny]
      have hd' : circuitFun n D z = false := by
        change (List.ofFn z).getD n false = false
        apply List.getD_eq_default
        simp
      exact hd'.trans hc.symm
    have hdm : Monotone2 D := by intro g hg; simp [D] at hg
    have hdr : ReadsBack n D := by intro k hk; simp [D] at hk
    have hs := hmin D hdm hdr hfun
    change C.gates.length ≤ 0 at hs
    omega
  have hU : n + j ∉ R := by
    intro hw
    obtain ⟨z, hf, ht⟩ := hd
    have hc := otFrontier_safe n C hr (j + 1) hp (n + j) hw z ht
    rw [hf] at hc
    cases hc
  let P := raPrefix C j
  have hPs : P.size = j := raPrefix_size C j hj.le
  have hterms : ∀ w ∈ R,
      ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
        (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
          taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
        taTermCost t ≤ if w ∈ A then 1 else 0 := by
    intro w hw
    rcases otFrontier_roots n C hm hr (j + 1) hp hout w hw with hlow | htail
    · have hne : w ≠ n + j := by intro he; subst w; exact hU hw
      have hlt : w < n + j := by omega
      let v : Fin (n + P.size) := ⟨w, by rw [hPs]; exact hlt⟩
      refine ⟨.inl v, ?_, ?_⟩
      · intro z
        exact (raPrefix_wire n C j hj.le z w hlt).symm
      · simp [taTermCost]
    · obtain ⟨k, hkp, hk, hop, hwk⟩ := htail
      have hnotread : n + j ∉ (gateAt C k).inputs := by
        intro hread
        have hwK : w ∈ raReaderRoots n C j := by
          apply Finset.mem_filter.mpr
          refine ⟨hw, (raTailAnd_mem n C (j + 1) w).mpr ⟨k, hkp, hk, hop, hwk⟩, ?_⟩
          simpa only [hwk, Nat.add_sub_cancel_left] using hread
        rw [hK] at hwK
        simp at hwK
      obtain ⟨a, b, hins, _, ha, hb⟩ :=
        frAndAfterLatest n C hm hr hmin j hd hlast k (by omega) hk hop
      have hane : a ≠ n + j := by intro he; apply hnotread; simp [hins, he]
      have hbne : b ≠ n + j := by intro he; apply hnotread; simp [hins, he]
      have halt : a < n + j := by omega
      have hblt : b < n + j := by omega
      let va : Fin (n + P.size) := ⟨a, by rw [hPs]; exact halt⟩
      let vb : Fin (n + P.size) := ⟨b, by rw [hPs]; exact hblt⟩
      refine ⟨.inr (va, vb), ?_, ?_⟩
      · intro z
        subst w
        change (C.wires (List.ofFn z)).getD (n + k) false =
          (((raPrefix C j).wires (List.ofFn z)).getD a false &&
            ((raPrefix C j).wires (List.ofFn z)).getD b false)
        rw [raPrefix_wire n C j hj.le z a halt, raPrefix_wire n C j hj.le z b hblt,
          frGateEval n C hr k hk z, hop, hins]
        simp [GateOp.eval]
      · have hwA : w ∈ A := (raTailAnd_mem n C (j + 1) w).mpr ⟨k, hkp, hk, hop, hwk⟩
        simp [taTermCost, hwA]
  obtain ⟨w0, hw0⟩ := hR
  obtain ⟨t0, _⟩ := hterms w0 hw0
  have hchoose : ∀ w : ℕ, ∃ t : Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)),
      w ∈ R →
        (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false =
          taTerm t (fun i => (P.wires (List.ofFn z)).getD i false)) ∧
        taTermCost t ≤ if w ∈ A then 1 else 0 := by
    intro w
    by_cases hw : w ∈ R
    · obtain ⟨t, ht⟩ := hterms w hw
      exact ⟨t, fun _ => ht⟩
    · exact ⟨t0, fun h => (hw h).elim⟩
  choose term hterm using hchoose
  apply raUnfactoredContradiction n C P (raPrefix_mono C j hm) (raPrefix_reads n C j hr)
    hmin R A ⟨w0, hw0⟩ term
  · intro z
    rw [otFrontier_semantics n C hr (j + 1) hp z, Bool.eq_iff_iff, ofAny_true]
    simp only [List.any_map, List.any_eq_true, Finset.mem_toList]
    constructor
    · rintro ⟨w, hw, ht⟩
      exact ⟨w, hw, ((hterm w hw).1 z).symm.trans ht⟩
    · rintro ⟨w, hw, ht⟩
      exact ⟨w, hw, ((hterm w hw).1 z).trans ht⟩
  · intro w hw
    exact (hterm w hw).2
  · have hb := raTailAnd_budget n C hm (j + 1) hp
    rw [raPrefix_size C (j + 1) hp] at hb
    rw [hPs]
    change j + R.card + A.card ≤ C.size
    change j + 1 + R.card + A.card ≤ C.size + 1 at hb
    omega

end PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma minimum_invariants (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      circuitFun (N + N) D = circuitFun (N + N) C ∧
      (∀ E : Circuit, Monotone2 E → ReadsBack (N + N) E →
        circuitFun (N + N) E = circuitFun (N + N) D → D.size ≤ E.size) ∧
      (∀ j < D.gates.length, mdDirty N I D j →
        ∃ p l : Fin N, I p l ∧ lcEssential N D j p l ∧
          ∃ p' l' : Fin N, I p' l' ∧ lcEssential N D j p' l' ∧ (p ≠ p' ∨ l ≠ l')) ∧
      (∀ j < D.gates.length,
        frDirty (N + N) (fun z => circuitFun (N + N) D z = false) D j →
        (∀ k < D.gates.length,
          frDirty (N + N) (fun z => circuitFun (N + N) D z = false) D k → k ≤ j) →
        (raReaderRoots (N + N) D j).card = 1) := by
  classical
  let P : ℕ → Prop := fun k => ∃ M : Circuit,
    Monotone2 M ∧ ReadsBack (N + N) M ∧
      circuitFun (N + N) M = circuitFun (N + N) C ∧ M.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hmono, hreads, rfl, rfl⟩
  obtain ⟨M, hm, hr, hf, hs⟩ := Nat.find_spec hex
  have hminM (E : Circuit) (hem : Monotone2 E) (her : ReadsBack (N + N) E)
      (hef : circuitFun (N + N) E = circuitFun (N + N) M) : M.size ≤ E.size := by
    rw [hs]
    exact Nat.find_min' hex ⟨E, hem, her, hef.trans hf, rfl⟩
  have hfunM : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) M z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [hf]
    exact hfun z
  obtain ⟨D, hdm, hdr, hds, hdf, hessential⟩ := minimum_dirty_essential N I M hm hr hfunM
  have hDM : circuitFun (N + N) D = circuitFun (N + N) M := by
    funext z
    exact Bool.eq_iff_iff.mpr ((hdf z).trans (hfunM z).symm)
  have hminD (E : Circuit) (hem : Monotone2 E) (her : ReadsBack (N + N) E)
      (hef : circuitFun (N + N) E = circuitFun (N + N) D) : D.size ≤ E.size :=
    hds.trans (hminM E hem her (hef.trans hDM))
  refine ⟨D, hdm, hdr, hds.trans (hminM C hmono hreads hf.symm),
    hDM.trans hf, hminD, hessential, ?_⟩
  intro j hj hd hlast
  exact raMinimumReaderOne (N + N) D hdm hdr hminD j hj hd hlast

end PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

lemma ocFilterSplit {α : Type*} (xs : List α) (A B : α → Bool) (x y : Bool)
    (hx : x = true → ∀ i ∈ xs, A i = true)
    (hy : y = true → ∀ i ∈ xs, B i = true) :
    ((x || y) && xs.any (fun i => A i && B i)) =
      ((x && xs.any B) || (y && xs.any A)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hxy, i, hi, hAi, hBi⟩
    rcases hxy with hxt | hyt
    · exact Or.inl ⟨hxt, i, hi, hBi⟩
    · exact Or.inr ⟨hyt, i, hi, hAi⟩
  · rintro (⟨hxt, i, hi, hBi⟩ | ⟨hyt, i, hi, hAi⟩)
    · exact ⟨Or.inl hxt, i, hi, hx hxt i hi, hBi⟩
    · exact ⟨Or.inr hyt, i, hi, hAi, hy hyt i hi⟩

lemma ocFilterCollapse {α : Type*} (xs : List α) (A B : α → Bool) (x y : Bool)
    (hx : x = true → ∀ i ∈ xs, A i = true)
    (hy : y = true → ∀ i ∈ xs, B i = true) :
    ((x || y) && xs.any (fun i => A i && B i)) =
      (((x || y) && xs.any A) && xs.any B) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hxy, i, hi, hAi, hBi⟩
    exact ⟨⟨hxy, i, hi, hAi⟩, i, hi, hBi⟩
  · rintro ⟨⟨hxy, hA⟩, hB⟩
    rcases hxy with hxt | hyt
    · obtain ⟨i, hi, hBi⟩ := hB
      exact ⟨Or.inl hxt, i, hi, hx hxt i hi, hBi⟩
    · obtain ⟨i, hi, hAi⟩ := hA
      exact ⟨Or.inr hyt, i, hi, hAi, hy hyt i hi⟩

end PEqualNP.Outside.L_meta_3451
