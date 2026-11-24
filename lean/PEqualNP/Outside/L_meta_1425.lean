import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1425

namespace PQ1425Lower

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
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

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
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

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
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

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
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

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
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

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
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

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
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

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
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

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
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

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
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

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
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




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)





theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]





theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih






def search (k : Nat) : Nat → List Nat → Bool
  | 0, ws => ws == [goal k]
  | s+1, ws => covers k (s+1) ws &&
      next (mask k) (s+2-ws.length) ws (fun _ zs => search k s zs)

theorem search_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : search k s ws = true := by
  induction s generalizing ws with
  | zero => simp [search,zero_done h rfl]
  | succ s ih =>
    rw [search, covers_ok h, Bool.true_and]
    exact next_complete h s rfl _ (List.Perm.refl _) _ (fun _ _ hh => ih hh)

def fn (T : Nat) : BFn 5 := fun x =>
  T.testBit (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def bound (T n : Nat) :=
  ∀ (gs : List Gate) (o : Nat), (∀ g ∈ gs, Ok g) →
    (∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) →
    (∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = fn T x) →
    (∃ g ∈ gs, g.op = GateOp.not) → n ≤ gs.length

theorem mkBound (T cap k : Nat) (rows : List Nat) (xs : List Nat)
    (hnc : fn T (fun _ => false) ≠ fn T (fun _ => true))
    (hm : mask k = 2^rows.length-1)
    (hi : (List.ofFn fun i : Fin 5 => fun x : Fin 5 → Bool => x i).map (fun a => encL a rows) = xs)
    (hy : encL (fn T) rows = goal k)
    (hp : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hn : ∀ s ≤ cap, ¬ NatRun (mask k) (goal k) s xs) : bound T (cap+1) := by
  intro gs o hok _ hev _
  by_contra! hn'
  have hc : HasCircuitSize 5 (fn T) cap :=
    ⟨⟨gs,o⟩, hok, (show gs.length ≤ cap by omega), hev⟩
  obtain ⟨s,hs,ws,hsub,h⟩ := exists_run (fn T) ⟨_,_,hnc⟩ cap hc
  have hr : NatRun (mask k) (encL (fn T) rows) s (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn 5 => encL a rows) (fun a => by rw [hm]; exact encL_inv a rows) (fun a b => encL_and a b rows)
      (fun a b => encL_or a b rows) h
  rw [hy] at hr
  have hsub' := hsub.map (fun a => encL a rows)
  rw [hi] at hsub'
  by_cases e : ws.map (fun a => encL a rows) = xs
  · rw [e] at hr; exact hn s hs hr
  · exact hp _ (List.mem_sublists.2 hsub') e (required hr)
def spr : List (Nat × Nat) → Nat → Nat
  | [],_ => 0
  | (i,m)::qs,v => (if v.testBit i then m else 0) ||| spr qs v

def used : List (Nat × Nat) → Nat
  | [] => 0
  | (_,m)::qs => m ||| used qs

def cleanMasks : List (Nat × Nat) → Bool
  | [] => true
  | (_,m)::qs => (m &&& used qs == 0) && cleanMasks qs

theorem spr_sub (p : List (Nat × Nat)) (v j : Nat) :
    (spr p v).testBit j = true → (used p).testBit j = true := by
  induction p with
  | nil => simp [spr]
  | cons a qs ih =>
    rcases a with ⟨i,m⟩
    simp only [spr,used,Nat.testBit_or,Bool.or_eq_true]
    split <;> grind [Nat.zero_testBit]

theorem spr_hom (p : List (Nat × Nat)) (h : cleanMasks p = true) (a b : Nat) :
    spr p (a &&& b) = spr p a &&& spr p b ∧
    spr p (a ||| b) = spr p a ||| spr p b ∧
    spr p (a ^^^ b) = spr p a ^^^ spr p b := by
  induction p with
  | nil => simp [spr]
  | cons v qs ih =>
    rcases v with ⟨i,m⟩
    simp only [cleanMasks,Bool.and_eq_true,beq_iff_eq] at h
    obtain ⟨ha,ho,hx⟩ := ih h.2
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      have hm := congrArg (fun x : Nat => x.testBit j) h.1 <;>
      simp only [Nat.testBit_and,Nat.zero_testBit] at hm <;>
      have hs := spr_sub qs a j <;> have ht := spr_sub qs b j <;>
      simp only [spr,ha,ho,hx,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> simp_all <;> grind

def sprOK (p : List (Nat × Nat)) (m y : Nat) : Bool :=
  cleanMasks p && (spr p m == m) && (spr p y == y)

theorem sprRun {m y s ws p} (h : NatRun m y s ws) (hp : sprOK p m y = true) :
    NatRun m y s (ws.map (spr p)) := by
  simp only [sprOK,Bool.and_eq_true,beq_iff_eq] at hp
  rw [←hp.2]
  exact Run.map _ (fun a => (spr_hom p hp.1.1 a m).2.2.trans (by rw [hp.1.2]))
    (fun a b => (spr_hom p hp.1.1 a b).1) (fun a b => (spr_hom p hp.1.1 a b).2.1) h

def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

def barrier (k gf : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          !(v/gf < N s && (rot (v % gf) zs).isPerm (S s (v/gf)))))

theorem barrier_sound {k gf S N act rot} {s i} (hb : barrier k gf S N act rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      !(v/gf < N s && (rot (v % gf) zs).isPerm (S s (v/gf))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k gf S N act rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k gf S N act rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h





def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]





def scorebarrier (k gf : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/(2*gf) < N s && (rot (v/2 % gf) zs).isPerm (S s (v/(2*gf))))))

theorem scorebarrier_sound {k gf S N act wits rot} {s i} (hb : scorebarrier k gf S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [scorebarrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/(2*gf) < N s && (rot (v/2 % gf) zs).isPerm (S s (v/(2*gf)))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem scorebarrier_all {k gf S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, scorebarrier k gf S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := scorebarrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h






namespace ce8a8a8a8
def rs : List Nat := [14, 14, 14, 22, 22, 22, 25, 25, 25, 26, 26, 26, 28, 28, 28, 1, 1, 2, 4, 6, 9, 9, 10, 12, 14, 17, 17, 18, 20, 22, 25, 25, 26, 28, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 30, 3, 5, 3, 5, 7, 11, 13, 11, 13, 15, 19, 21, 19, 21, 23, 27, 29, 27, 29]
def xs : List Nat := [0xffffedb6cc63181c0,0x5ad6b6db5294a0e3f,0xad6b5b6da318c703f,0xf07c12493c1f07fc7,0xff8012493fe007ff8]
theorem no : search 34 5 xs = false := by decide +kernel
end ce8a8a8a8
open ce8a8a8a8 in
theorem lower_e8a8a8a8 : bound 0xe8a8a8a8 6 := by
  apply mkBound 0xe8a8a8a8 5 34 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 34) (goal 34) 5 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction

namespace ce8a8e888
def rs : List Nat := [5, 5, 5, 5, 22, 22, 22, 22, 25, 25, 25, 25, 26, 26, 26, 26, 28, 28, 28, 28, 1, 2, 5, 6, 6, 9, 9, 10, 10, 12, 12, 17, 17, 18, 20, 22, 22, 25, 25, 26, 26, 28, 28, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 13, 14, 21, 3, 3, 7, 7, 14, 11, 13, 11, 14, 13, 14, 19, 21, 19, 21, 23, 30, 27, 29, 27, 30, 29, 30]
def xs : List Nat := [0x177d77ddddd86186500f0f,0x2dd6dfaaaaa99a19a0f0f0,0x3aebae7777761c61cf00ff,0x3f83f8333337e07e0fff00,0x3ffc00444447ff800ffff0]
theorem no : search 43 6 xs = false := by decide +kernel
end ce8a8e888
open ce8a8e888 in
theorem lower_e8a8e888 : bound 0xe8a8e888 7 := by
  apply mkBound 0xe8a8e888 6 43 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 43) (goal 43) 6 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction
namespace ce8e8e880
def wdA (i : Nat) := (if i<2 then (if i<1 then 0x492492244891224cf3cff80fe03f8014514993264c99300000000000007f1451491224489123cf3c07ffe0007f03f038f1e3c78f103f0000001fffff000fc78f1e3c78f000fc00001fffff000fc70e1c3870e000fc00000000000000008102040810000000001fffff000000000000000000000000000000 else 0xb6db6d5ab56ad5a30c3007f0000000a28a24c993264c90000000001fc0005d75dbb76eddbb70c30c000fe03fff5d75dbb76eddbb70c30c000fe0007f5d75dbb76eddbb7000000000003fff5d75db366cd9b360c30c000fe000005c05c3060c183060c00c000fe00000492492a54a952a5000000000003f80) else (if i<3 then 0xfc0fc78f1e3c78ffc0fffffffffffffc0fc70e1c3870efc0ffffffe00000fc0fc70e1c3870e3c03c07ffe00000fc0000000000000fc003ffffe00000ebaeb6eddbb76edc30c3f8001fff80ebaeb6eddbb76ed0000000001fff80b6db6ddbb76eddb30c3007f01fc07fb6db6ddbb76eddb30c3007f000007f else 0xffffffffffffffffffffffffe03ffffffffffffffffff3cf3c07ffffffffffffff7efdfbf7efffffffffe00000ffffff7efdfbf7efcfffffffe00000ffffff7efdfbf7e3cf3c07ffe00000fff5fb76eddbb76fff0fffffe00000fff03870e1c3870fff03ffffe00000fd7fdfbf7efdfbffc3ffffffe03fff))
def wd (i : Nat) := (wdA (i/8) >>> (120*(i % 8))) &&& 0xffffffffffffffffffffffffffffff
def stA (i : Nat) := (if i<1 then 0x66cd3941d9c5a305a7168c168b4a304e2d20c199c5a204e2d1881d9c5a105a71684009c5a1003b38b400e4e2d003738b400ece2c003f38a8138bdaa003b38ac00f7666003369181d9c5460767141819b3906003b169400eb4e500271684008b4a1000138280006e660001d918009bd46003ae4180000000000000000000000 else (if i<2 then 0x66d38b738b4e2dcdad38b736a4e2df66d38b7369c5adcda716a7369c5a6066d1697369c5a5cda7168c169c5a307fb38b41dece2d003b38b41dc4e2d076d38b41ab4e2d066d38b417b4e2d076938b41eece2d066b38b41d9c5ad076716a81d9c5a9066d38ac1ecda660767169b369c506003b16941db45a5066d16941d9c5a5 else 0x66d38b400ece2d076d38b7b9b4e2d))
def st (i : Nat) := (stA (i/34) >>> (30*(i % 34))) &&& 0x3fffffff
def off (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0 else 1) else (if i<3 then 2 else 3)) else (if i<6 then (if i<5 then 8 else 24) else (if i<7 then 56 else 71)))
def ct (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 1 else 1) else (if i<3 then 1 else 5)) else (if i<6 then (if i<5 then 16 else 32) else (if i<7 then 15 else 1)))
def state (s i : Nat) := unpackWords wd 5 8 (st (off s+i))
def oaA (i : Nat) := 0xe3d5cbc0b5adaaa49f9c97948d8b8985817e7a73716d6c696864605d5c57534f4a45403e3d3c3a393635343332312e2d2b2a29262421201c1916130f0c0b0a09080706050403020100
def oa (i : Nat) := (oaA (i/128) >>> (8*(i % 128))) &&& 0xff
def ovA (i : Nat) := 0x3bfe5378d1317bb2d1aeea3a02699322e87a097cde672dba6718a5e96d5916354d3a4c51e410f2394d62f0b72b8aa2989625487218852107b1e86c1ac621846016452114400e02b0901f0641404c120441003c0e0340800c0200400
def ov (i : Nat) := (ovA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def aValA (i : Nat) := (if i<1 then 0x10e0051000410003130190c20010c00836c008811b04e0000c00001850002090800000022950033060040000023800010000000810093c000100004004c0000802002c10020400811930010800000001c00000070030010000000030010070000030800c0003040002040003042000000000000000000000000000000000000 else 0xc6e049f3d91426c03973c20cc14e5c04900dc990846b824ab5c03cd4c35c51c050004f9940c08c710a080)
def aVal (i : Nat) := (aValA (i/170) >>> (6*(i % 170))) &&& 0x3f
def vValA (i : Nat) := (if i<5 then (if i<2 then (if i<1 then 0x40207802000401180010040105c030040322003000030e403210800fc000003b0ec3b0ec410ec3b0ec00080010fc450c4071400000c0300c031804011c000000300c0300c4900c0300c000003d10c400f43d080030ec03000000000000c0001c0701c000f40000400004000ec490f4000003b12c490000001c070f40000000 else 0xb5e00b5e0004003200000c2d0d42d3002d2800101c800000328001000601006012060780600000b0006000001000600040100401004000040700403000030000100001100000000000c0001c000040101c010040100c010002000401000000040178000004010000000003000070000100407004010040302c010002001020) else (if i<3 then 0x40000001005e000001005e0000010002f00000000010b40178001780c40000700000300070040358001004000000000003511400042b004010000b02c010000b02c0b02c0b02407001e0000010140348000074073c0000c40000c0300c0300ce00dc0300000074034000000c000000300c03000002a0000d42d01d0000c17 else (if i<4 then 0x4000000100001004010bc01004010b40102c0b024070140302c010000b001e00040b02c0b02c0b005e002c010140002c0b0000902c0002c01780010000100001004000000901c0500c01005e000401004010040100017004010bc0100c0100401401a00052c001e0001e00000000c0100401004010000b005c20040000400 else 0x40100401004000000701c00004e0380e0380e018300004a0300c434320005e06302f0b40000401005e00002b00000000010000058001004000040100188005e0780010040701c0300c01004000040100401000000000000c0000c000bde000c0101c0001c000cc0001c70004640b401780010046000420005e00042b005e0))) else (if i<7 then (if i<6 then 0x240100401003200040100000c800102c00002400040101c0900401d00010340d00011064150001104c0580003701c80032000c0d05c07c800d0000d004010000d035e000400601a0001823016030960481604a160c816002d400000300403000010000100001004010040101c0100401004010040300c80000010040040001 else 0x400c8009d8003004010040000001004050040700003004000000000401c8000004000140000001c8000b800100401026c000401002a00040f0000000401a8b2000403000010040bc8001004008b20000c00004010041700000004000000fa00010040b0040d0000100720c8000000010000100401004000040102c0301405) else (if i<8 then 0x2c01d88010040102c070940b0042100c050000100001004000040100001000000000038964381605c0010a41500400024050076209c0fe800d004030040700c010040700c01d80030040700720c8320c800100401007200000f0340002c0100720004000000100400e00000040100400004010000000401c8007000010000b else (if i<9 then 0x488509a000fb000e83e8b11f0e81b050280102889b144f8260792d0b01e0691a0e828cf0150e801b0000bd801d0740b64388f000002c2102f8007c2002f600000b085809024c0776002c00064004080b02f60087600778c02e4802c0b02d84000210076002f60000000032000403d800100c1db800000407c800900423f0001 else 0xae000a20014870084539802b0403314020000581a011022301a2528002a0603c0025807040120508aa2814c39090190e0080c8))))
def vVal (i : Nat) := (vValA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def act (s i t : Nat) : Nat :=
  let j := off s+i
  let p := oa j
  let q := ov j
  let a := oa (j+1)-p
  let b := ov (j+1)-q
  vVal (q + ((t/a + aVal (p + t % a))%b))
def opTab (i : Nat) := (if i<6 then (if i<3 then (if i<1 then ([(6,0x7f),(13,0x3f80),(20,0x1fc000),(43,0xc0000000000),(45,0x300000000000),(47,0xc00000000000),(49,0x3000000000000),(51,0xc000000000000),(53,0x30000000000000),(55,0xc000000fe00000),(57,0x3000007f0000000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x141020408102000000000000000),(106,0x482040810204000000000000000),(107,0xa04081020408000000000000000),(110,0x5008102040810000000000000000),(112,0x12010204081020000000000000000),(113,0x28020408102040000000000000000),(116,0x140000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else (if i<2 then ([(6,0x7f),(13,0x3f80),(20,0x1fc000),(43,0x3000000000000),(45,0xc000000000000),(47,0x30000000000000),(49,0xc0000000000),(51,0x300000000000),(53,0xc00000000000),(55,0xc000000fe00000),(57,0x3000007f0000000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x5008102040810000000000000000),(106,0x12010204081020000000000000000),(107,0x28020408102040000000000000000),(110,0x141020408102000000000000000),(112,0x482040810204000000000000000),(113,0xa04081020408000000000000000),(116,0x140000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x3f80),(13,0x7f),(20,0x1fc000),(43,0xc0000000000),(45,0xc00000000000),(47,0x300000000000),(49,0x3000000000000),(51,0x30000000000000),(53,0xc000000000000),(55,0xc000000fe00000),(57,0xc0003f800000000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x482040810204000000000000000),(106,0x141020408102000000000000000),(107,0xa04081020408000000000000000),(110,0x12010204081020000000000000000),(112,0x5008102040810000000000000000),(113,0x28020408102040000000000000000),(116,0x480000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)))) else (if i<4 then ([(6,0x3f80),(13,0x7f),(20,0x1fc000),(43,0x3000000000000),(45,0x30000000000000),(47,0xc000000000000),(49,0xc0000000000),(51,0xc00000000000),(53,0x300000000000),(55,0xc000000fe00000),(57,0xc0003f800000000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x12010204081020000000000000000),(106,0x5008102040810000000000000000),(107,0x28020408102040000000000000000),(110,0x482040810204000000000000000),(112,0x141020408102000000000000000),(113,0xa04081020408000000000000000),(116,0x480000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else (if i<5 then ([(6,0x7f),(13,0x1fc000),(20,0x3f80),(43,0x300000000000),(45,0xc0000000000),(47,0xc00000000000),(49,0xc000000000000),(51,0x3000000000000),(53,0x30000000000000),(55,0x3000007f0000000),(57,0xc000000fe00000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x141020408102000000000000000),(106,0xa04081020408000000000000000),(107,0x482040810204000000000000000),(110,0x5008102040810000000000000000),(112,0x28020408102040000000000000000),(113,0x12010204081020000000000000000),(116,0x140000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x7f),(13,0x1fc000),(20,0x3f80),(43,0xc000000000000),(45,0x3000000000000),(47,0x30000000000000),(49,0x300000000000),(51,0xc0000000000),(53,0xc00000000000),(55,0x3000007f0000000),(57,0xc000000fe00000),(59,0xc0003f800000000),(95,0x810204081000000000000000),(104,0x5008102040810000000000000000),(106,0x28020408102040000000000000000),(107,0x12010204081020000000000000000),(110,0x141020408102000000000000000),(112,0xa04081020408000000000000000),(113,0x482040810204000000000000000),(116,0x140000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat))))) else (if i<9 then (if i<7 then ([(6,0x1fc000),(13,0x7f),(20,0x3f80),(43,0x300000000000),(45,0xc00000000000),(47,0xc0000000000),(49,0xc000000000000),(51,0x30000000000000),(53,0x3000000000000),(55,0x3000007f0000000),(57,0xc0003f800000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0xa04081020408000000000000000),(106,0x141020408102000000000000000),(107,0x482040810204000000000000000),(110,0x28020408102040000000000000000),(112,0x5008102040810000000000000000),(113,0x12010204081020000000000000000),(116,0xa00000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat)) else (if i<8 then ([(6,0x1fc000),(13,0x7f),(20,0x3f80),(43,0xc000000000000),(45,0x30000000000000),(47,0x3000000000000),(49,0x300000000000),(51,0xc00000000000),(53,0xc0000000000),(55,0x3000007f0000000),(57,0xc0003f800000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0x28020408102040000000000000000),(106,0x5008102040810000000000000000),(107,0x12010204081020000000000000000),(110,0xa04081020408000000000000000),(112,0x141020408102000000000000000),(113,0x482040810204000000000000000),(116,0xa00000000000000000000000000000),(118,0x140000000000000000000000000000),(119,0x480000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x3f80),(13,0x1fc000),(20,0x7f),(43,0xc00000000000),(45,0xc0000000000),(47,0x300000000000),(49,0x30000000000000),(51,0x3000000000000),(53,0xc000000000000),(55,0xc0003f800000000),(57,0xc000000fe00000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x482040810204000000000000000),(106,0xa04081020408000000000000000),(107,0x141020408102000000000000000),(110,0x12010204081020000000000000000),(112,0x28020408102040000000000000000),(113,0x5008102040810000000000000000),(116,0x480000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat)))) else (if i<10 then ([(6,0x3f80),(13,0x1fc000),(20,0x7f),(43,0x30000000000000),(45,0x3000000000000),(47,0xc000000000000),(49,0xc00000000000),(51,0xc0000000000),(53,0x300000000000),(55,0xc0003f800000000),(57,0xc000000fe00000),(59,0x3000007f0000000),(95,0x810204081000000000000000),(104,0x12010204081020000000000000000),(106,0x28020408102040000000000000000),(107,0x5008102040810000000000000000),(110,0x482040810204000000000000000),(112,0xa04081020408000000000000000),(113,0x141020408102000000000000000),(116,0x480000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat)) else (if i<11 then ([(6,0x1fc000),(13,0x3f80),(20,0x7f),(43,0xc00000000000),(45,0x300000000000),(47,0xc0000000000),(49,0x30000000000000),(51,0xc000000000000),(53,0x3000000000000),(55,0xc0003f800000000),(57,0x3000007f0000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0xa04081020408000000000000000),(106,0x482040810204000000000000000),(107,0x141020408102000000000000000),(110,0x28020408102040000000000000000),(112,0x12010204081020000000000000000),(113,0x5008102040810000000000000000),(116,0xa00000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x1fc000),(13,0x3f80),(20,0x7f),(43,0x30000000000000),(45,0xc000000000000),(47,0x3000000000000),(49,0xc00000000000),(51,0x300000000000),(53,0xc0000000000),(55,0xc0003f800000000),(57,0x3000007f0000000),(59,0xc000000fe00000),(95,0x810204081000000000000000),(104,0x28020408102040000000000000000),(106,0x12010204081020000000000000000),(107,0x5008102040810000000000000000),(110,0xa04081020408000000000000000),(112,0x482040810204000000000000000),(113,0x141020408102000000000000000),(116,0xa00000000000000000000000000000),(118,0x480000000000000000000000000000),(119,0x140000000000000000000000000000)] : List (Nat × Nat))))))
def rot (g : Nat) (w : List Nat) := if g = 0 then w else w.map (spr (opTab (g % 12)))
theorem rokok (g : Nat) {s ws} (h : NatRun (mask 60) (goal 60) s ws) :
    NatRun (mask 60) (goal 60) s (rot g ws) := by
  unfold rot
  split
  · exact h
  · apply sprRun h
    exact (by decide +kernel : ∀ j : Fin 12, sprOK (opTab j) (mask 60) (goal 60) = true) ⟨_,Nat.mod_lt _ (by decide)⟩
def tickA (i : Nat) := (if i<1 then 0x180d0dc701a05f34140ec711c05f18330507117c6e18140e4711b85f18310347017c6e34310186e17c70180d0dc771d05f180d0dc761a05fdc390ec771d868ac2d0ec771d868182b0346a17c68342b0186817c6a180d0dc701b85f180d0dc701d05f34140ec771d85f180d0dc761b85f18140e4771d05f180d0dc761d05f else (if i<2 then 0x183b0507717c74e40d0dc761d07718140ec711b85fdc140ec771d874dc140e4771d07618140ec771d05fe43b0dc761d077dc3b0e4771d05f182f0506b17c68dc390ec771d87418390507717c7418140e4771d85f18370347617c7434370187417c76e43b0dc761d05f180d0dc6a1d05f182d0506b17c68180d0dc6a1b85f else 0xdc3b0e4771d076183b0e4771d05f))
def tick (i : Nat) := (tickA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def Z := scorebarrier 60 16 state ct act tick rot
theorem h0_0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0_0
theorem h1_0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1_0
theorem h2_0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2_0
theorem h3_0 : span (Z 3) 5 0 = true := by decide +kernel
theorem z3 : span (Z 3) 5 0 = true := h3_0
theorem h4_0 : span (Z 4) 12 0 = true := by decide +kernel
theorem h4_12 : span (Z 4) 4 12 = true := by decide +kernel
theorem z4 : span (Z 4) 16 0 = true := (@span_join (Z 4) 12 0 4 h4_0 h4_12)
theorem h5_0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5_12 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5_24 : span (Z 5) 8 24 = true := by decide +kernel
theorem z5 : span (Z 5) 32 0 = true := (@span_join (Z 5) 24 0 8 (@span_join (Z 5) 12 0 12 h5_0 h5_12) h5_24)
theorem h6_0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6_12 : span (Z 6) 3 12 = true := by decide +kernel
theorem z6 : span (Z 6) 15 0 = true := (@span_join (Z 6) 12 0 3 h6_0 h6_12)
theorem h7_0 : span (Z 7) 1 0 = true := by decide +kernel
theorem z7 : span (Z 7) 1 0 = true := h7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < ct s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
def rs : List Nat := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 9, 9, 10, 10, 12, 12, 17, 17, 18, 18, 20, 20, 25, 25, 26, 26, 28, 28, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 7, 11, 13, 14, 19, 21, 22, 11, 13, 11, 14, 13, 14, 19, 21, 19, 22, 21, 22, 27, 29, 27, 30, 29, 30]
def xs : List Nat := [0x5d75dbb76eddbb70c30c000fe03fff,0xb6db6ddbb76eddb30c3007f01fc07f,0xebaeb6eddbb76edc30c3f8001fff80,0xfc0fc70e1c3870efc0ffffffe00000,0xfff03870e1c3870fff03ffffe00000]
end ce8e8e880
open ce8e8e880 in
theorem lower_e8e8e880 : bound 0xe8e8e880 8 := by
  apply mkBound 0xe8e8e880 7 60 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have hh : NatRun (mask 60) (goal 60) 7 xs := extend_run h hs
  have hp : xs.Perm (state 7 0) := by decide +kernel
  exact scorebarrier_all rokok checked 7 (by decide) 0 (by decide) (Run.perm hp hh)
namespace ceaa8a888
def wdA (i : Nat) := (if i<6 then (if i<3 then (if i<1 then 0x8021084210807f800007fff008021084210802a8000003ff001e10842108400780000001f0001084210843f757fff07c0000010842108426647c1f07c00000108421084155503ff07c000000000000002a207c00000000000000000000075000007c0000000000000000000000000000000000000000000000000000 else (if i<2 then 0x1fe318c6318ea7ffc0007fff01fe318c6318c77f801f07fff01fe318c6318c07f800007fff01fe318c6318c06e800007fff01fe318c6318c05f800007fff01fe318c6318c00a8000003ff01f821084210807e000007fff0198210842108066000007c1f017e108421084055000007c000101084210840040000007c00 else 0x577e108421084000000000000560108421084150003ff00000517908421084145403ff07c001ffe739ce739c7ff801ffffff1fe06318c63187f8001ffffe01e1e5294a5294787801ff801f1119084210840444001f07c00111800000000000000000000007fe318c6318c1ff8000fffff01ff39ce739cff7fffff07fff)) else (if i<4 then 0x666694a5294a599983e0f83e057ff39ce739cd57f83ff07fff57fe318c6318c07f800007fff577f18c6318c7f757fff07c00577f18c6318c557503ff07c00577f18c6318c555503ff07c00577f18c6318c550003ff00000577f18c6318c545403ff07c00577f18c6318c4444001f07c00577f18c6318c4040000007c00 else (if i<5 then 0x99816b5ad6b5a0607c0007c0098014a5294a526007c1f000009199294a5294a4647c1f07c0089816b5ad6b5a2627c0007c1f88816b5ad6b5a6667c1f07c1f88806318c631a2227c000001f878739ce739ce1e1fc00ffc008181294a5294a0607c0007c00818021084210800000000000080010842108420007c0000000 else 0x99996b5ad6b5a6647c1f07c0099996b5ad6b5a6627c1f07c1f99996b5ad6b5a6027c1f0001f99996b5ad6b5a4667c1f07c1f99996b5ad6b5a0627c0007c1f99996b5ad6b5a0027c000001f99996b5ad6b58446001f07c1f99996b5ad6b58042000007c1f99986318c631800200000001f99816b5ad6b5a6607c1f07c00))) else (if i<9 then (if i<7 then 0xb999ef7bdef7aeeefc1ffffffa9fef7bdef7beafffc00fffffa881ef7bdef7bffffffffffffa880e739ce73aafffc00fffffa880e739ce73aaaafc00f83ffa880e739ce73a2aafc00f83ffa880e739ce73808a8000f83ff99ff7bdef7bde67ffc1f07fff99996b5ad6b5bf777fff07c1f99996b5ad6b5a6667c1f07c1f else (if i<8 then 0xe1e1ad6b5ad6a0687c0007fe0e1e1ad6b5ad6905803e007fe0e0018c6318c638007fe000000dfff7bdef7bdf7777fff07c1fdfff7bdef7bde6667c1f07c1fdfff7bdef7bdd55703ff07c1fdffe739ce739c00200000001fd9f96b5ad6b5b6767fff07c1fd7ff39ce739cf5757fff07c00d7ff39ce739cd55503ff07c00 else 0xf9f9ef7bdef7be7e7fff07ffff9f9ef7bdef7a66e7c1f07ffff9f8e739ce73800a0000003fff999ef7bdef7be667fff07c1ff801ce739ce73e007fff00000f801ce739ce726007c1f00000f7ffbdef7bdefd7d7fff07fe0f7ffbdef7bdef8787fe007fe0e1ffbdef7bdef87d7fe007fe0e1e1ad6b5ad6b8787fe007fe0)) else (if i<10 then 0xff7fdef7bdef7f807ffff8000ff19ce739ce73f807ffff8000fe1fdef7bdef7f857ffff8000fe07def7bdef7f81fffff8000fe01ce739ce73fa07ffff8000fe01ce739ce73f857ffff8000fe01ce739ce73f807ffff8000fe01ce739ce73f007fff00000fe01ce739ce738807fe0f8000fe00c6318c6300800000f8000 else (if i<11 then 0xffffffffffffc4ce801fffffffffef7bdef7beaaafc00f83fffffef7bdef7bc0ff8000ffffffffef7bdef7bc08a8000f83fffffef7bdef7bc00a0000003fffff9ef7bdef7bffe7ffffffffffe1ef7bdef7bff87ffffffe0ff99ef7bdef7bfe67fffffc1fff81ef7bdef7bf807ffff8000ff7fdef7bdef7fd57fffffc00 else 0xfffffffffffffffffffffffffffffffffffffff8afffff83ffffffffffffffff7f7fff07ffffffffffffffffefeffffffffffffffffffffff8faffe0ffffffffffffffffff7fffffffffffffffffffffffe6eefc1ffffffffffffffffffe0eafc00fffffffffffffffffd5df83fffffff))))
def wd (i : Nat) := (wdA (i/10) >>> (100*(i % 10))) &&& 0xfffffffffffffffffffffffff
def stA (i : Nat) := (if i<7 then (if i<3 then (if i<1 then 0x35507c8860001aa83c443c000d541e26160006ba0f110e0003550788848001aa6bc441c00001aaeab4400000d571522000006aaaa91000003554548800001a6eaa4400000aaa9106000006aab055000003532446800001a9e223200000d4a91150000000000000000000000000000000000000000000000000 else (if i<2 then 0x35507888a8001aa93c4444000d545e22220006aa0f11110003550648888001aa8394444000d541ba2220006ab2a911100035506a8888001aa83c4244000d541e1f22000507888886000355082f088001420bc2218000d4f1118220003c44608860003541786088001a93a23044000d541e221a0006aa0f1110 else 0x2ed9548830001768354418000bb41e1f0c0005da0f51050002ed0789020001aaed084f0000d58e841780006abb420bc000355da10590001aaed082dc000d5768415c0006abb660aa000355da105a8001768417818000d576840780006abb422ac000365da0fde0001aa83c444c000d59de22340006aa0f1112)) else (if i<5 then (if i<4 then 0x355d9cd510001aaed06888000d57683c400006abb4261f000355da12cf8001aaed0787c000d5767bc3e0006abb41e1e00034dda0f110001aaed75488000db76833440006abb3d9a2000355da0ccf8001aa83c4a88000d5768353a0006abb416a200031d07888300017683c4418000bb419220c0005da0dd106 else 0x355da0ed10001aaed07488000d576832440006abb41c22000355da6dd10001aaed06e88000d56e837440006abb418a2000355da0d910001aaed05c88000e9aaeaa440006abb65522000355daca910001aaed55488000d566aaa4400000d555522000355db0a910001aaabc5488000d53582a440006abb41aa2) else (if i<6 then 0x1aaed07888700d541e22223806abb41e22040355da0f110801aaed07888380d57683c440405da0f1106020355da105e0101aa83c444408001aaed08cf0000d57683c460006ac749e220003565a0f110001ab1d07888000d58a83c440006abf41e220003561a0f110001aaf507888000d58283c440006abb41e22 else 0x1aa83c4470880d541e222e4406bd541e22220356aa0f111101aad507888880d541e33444406aa0f111d2202ed07888886000283c4444300d541e22221806abb420bc220006aa105e1101aa8417888880d541e223044000d4f11182203550788889101aaed07888600d541e22223006abb41e221603550788888b))) else (if i<11 then (if i<9 then (if i<8 then 0x1aaed07ef1100d5768417ef006abb41e22060355da0f111a01db5507888880d59a83c444406ac941e222203aeaa0f111101aaed07888880d56683c4444000d541e22220355098f111101c35507888880d541f3c444406aa0f1e22220355078c111101aa83c5488880ddaa83c444406aa0f132222035507889111 else 0x355da105e00d576cd082f006abb42641780386abb420bc01aaed08b05e00d57684178f006abb420bc540376abb420bc01aaed082f1100d576841785c06cd576841780356abb420bc01aaed082f1980d5768417874000bb420bc0c02ed082f110601aaed082f0300d57684182f006abb41e2c440355da105e2c) else (if i<10 then 0x176cd07888300bb4263c4418070bb41e220c02ed07af1106017683c7888300bb41e2a441806ebb41e220c02ed07891106017683c4488300bb41e222e1806abb41e220c02ed078cd106017683c4474300bb41e220c1806abb41e220a02ed0788830501aaed07888200bb41e220c1006abb4223c4403b6abb420bc else 0x1af55da0f1100d5aaed0788806abb5e83c440355da125e2201c2ed078cd100e1aaed0668806abb41e33440355da0cd52201aaed06688b80d57683c528806ebb41e223a0376abb41e1d01ab1d07888e80d57683c447406abb41e1d2e0355da0f111601aaed086f1100d57683c4450076bb41e220c0005da0f1106)) else (if i<13 then (if i<12 then 0x1aaed078a1100ddaaed0788806abb4253c44036eabb41e22000355da0d5100d57683c6a8806ed576835440355da0f122201aaed07899100d57683c448806abb41e22360006abb41e1f01c355da0f0f80d57683c447c06abb4263c2e0355da13111701aaed07888beabb426bc445c06abb41e22140366abb41e22 else 0x1c355da0f1100d576c50788806fd57683c440355da12de2201aaed07af1100d576845788806abb41f3c440355da0f1e2201ab3dda0c910001aaed0648806abb41e32440355da0f17a2000355da0dd100e5aaed06e8806abb41e37440006abb6552201aaed978a9100d5769bc548806abb41e2a440355da0c1522) else (if i<14 then 0x1aaed07888e80017683c441806abb41e220c0006abb420bc01aaed082f1100d57683c4444000d541e222203aeac941e220003563a0f1100edaaed0788806ad17683c440006abb41e2201d355da0f1100e7aaed0788806abb6683c440355dad41e2201c755da0f1100d57684c788806abb4243c440355da11de22 else 0x355da0f110001aaed0788806abb6683c440355da131e2201c355da0f1100d57683c788806abb41e2a440376abb41e2201aaed07889100d57683c445c06ad57683c440355da0f19a2))))
def st (i : Nat) := (stA (i/20) >>> (49*(i % 20))) &&& 0x1ffffffffffff
def off (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0 else 1) else (if i<3 then 2 else 3)) else (if i<6 then (if i<5 then 4 else 14) else (if i<7 then 111 else (if i<8 then 273 else 291))))
def ct (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 1 else 1) else (if i<3 then 1 else 1)) else (if i<6 then (if i<5 then 10 else 97) else (if i<7 then 162 else (if i<8 then 18 else 1))))
def state (s i : Nat) := unpackWords wd 7 9 (st (off s+i))
def oaA (i : Nat) := (if i<1 then 0x23c8e22c8a21c862148420c811fc7e1f0781d4701b4651845e16c5a1645815c561545414c511384a1244610c42104400fc3e0f43c0ec3a0e4380dc360d4340cc320c4300bc2e0b42c0ac2a0a42809c260942408c220842007c1e0741c06c1a0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400 else (if i<2 then 0x5494d5314a51d46515425053f4f93d4f13b4e1374d1334c12c4a52648d224851e4751a45d164551243d0e4310b4290741905411033f8fb3d4f33c4ee3b4ec3acea39ce4388e1380dd370db364d835cd6354d4344d033cce32cca324c831cc6314c430cc2304bd2e4b62ccaf2b4a828ca027c9e2749a264972549424c9224490 else 0x39fe4f87ddb64d634ecf72fc8f17c3f00bcae6b5acaaeaaaa7a9ca5290a3a86a067c9de719b6679925d962539324590a3d8de348c62988a1d8561082dff7e5f47bdea795e1769d5739c6709be6f1ba6ddaf6a9a5691a267d9c6659664d8f629816017b5d5705b56a5a5665855c56957))
def oa (i : Nat) := (oaA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def ovA (i : Nat) := (if i<2 then (if i<1 then 0x14c09d04a023010807a03801940c805c02a014c0a4051028013c09804b024011c08c045022010c08404101f00f407803901c00dc06c03501a00cc05c02d01480a004e0260128090046022010808003e01e00e807003601a00c806002e01600a8050026012008803801a00c0058028012008003801800a0040018008002000 else 0x64031d18c8c506042fd1790bb85ce2e216f0b6c5aa2ce1648b145822bd15c0ad05602ad1530a9453429914c0a3451828b14009f44d0263124890845a22910807fc3d41cf0e407083761b30d906a43421a00cf867833a19c0cd86683241910c486202fc1760b705882b01500a004d024e11408003901b00c705902c41600a7) else (if i<3 then 0xeb27423969c60e066d935e1a60d2e6833349978c8062b30b1804bd45cd2e616d8b365812b61538a9a53528b13dc9c44c7257927892e48c243920c8fc47923a91bc8d446523091748984492221104854425208102c7f03f01f18f747b43d31e60f207863be1d68ea87483a11cf0e6471c38d1c60e246e236c1ac0d48672327 else 0x431e13f0778173f91f2cf5d787bb05d12e41703b6f9adad4567cb34590ec3c60a2fed7a4bb75cf2dd96aeb3b590ac055ccacb55a2a6d4fca61520a87d4109ef4ec270d35097b4aca50522e8f846b229d11487242a20d502e7fb3ef1efcf28775))
def ov (i : Nat) := (ovA (i/78) >>> (13*(i % 78))) &&& 0x1fff
def aValA (i : Nat) := (if i<3 then (if i<1 then 0x1830000183000000000140070000100000c28000000830e003040a0c00a32141001e101000614009001020010000000000000000400302000091400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if i<2 then 0x300000400000042000004000000c200002800000000000208000000000f200c300000800100140020000004000400100000001400080040048000000800000000000000000000000000000000000000000000000000000008000001801804000002018000000040014080000420300000800a30000000400000000010000000 else 0x120e2800217286468c06006070018400000050020003061400b8d000c30016000000e002821e10d80120c28000080001800104002c18200082832c00404080008600300020018280102400a002048f04000051814506220018100001001200081000000100000000000000000000100001000018001000400014001000000009)) else (if i<5 then (if i<4 then 0x40200149800c0c08000100020a001131200c82003939b4a01117061420424008042610002023508a08012140800182182048d0c0c00a36690914c0d0803e5d087082420100100800a0821900586880e040191a1018100009990064102240000c2e14889006c38d088c480000001a005c1010044280000000d001c4001400110 else 0x2922bc50f0808ba6480801b3208dc570089bd58084bf58080394408dc15a1083f501034574a40351ea450f0808ba6480801b32081001a906030084a0300280800a00725000c0222a0c49e260c00f16044000200681240028c0010180140401406100020a143000a04409220018a2230180180078100340181e080043810586) else (if i<6 then 0xf0d0114aae561072c487cdb57ae003152e0024445d08628087357f24d1d2a313035a1243d72d402a509e4417675b80623dc8b3e5d41d66c0b035c4cf80545120e74a9e9886dc1008c9de0b4a3d48040b14aa886dc37687988048401986a35cb526513b7426cc4b00c45c3143c2022e99202006cc823911f8a24c9b8a10b55af else 0x28784045d3240400d990428784045d3240400d9904c21c070a93c108e5223305039b1801802410ddbd6860497)))
def aVal (i : Nat) := (aValA (i/146) >>> (7*(i % 146))) &&& 0x7f
def vValA (i : Nat) := (if i<25 then (if i<12 then (if i<6 then (if i<3 then (if i<1 then 0x2b0c70330bd06f00306b00004801500300004003301300000000306f00303800006b0150bb03000000303300000300000003300000000302001001500006500000008708700306b00301500303300301300000000000000000000006f01300000300000006f0030000980000e706f0b708706f06f06f00006f000000000000 else (if i<2 then 0x3300003301507b07b03300007b07b00000007b07b07b03300007b07b00000007b00000002b01300007b00001300000002b01300007b00001309300f08900f09500f00000f07500f09b0500000070070070000070610070000390000150e103d03703703703703700002d02d02d02d03302d02d02d02b02b02b02b03302b02b else 0x400260dd0b50d900006f0d30000d50000300b70db0d706f06f0d30000d50df06f0d307007006f06f0130e708705d0000370600130130130130130eb07005d0ed05d05d05d06f05d0b500005d05d06f00005d00006f0a90000720700f106f0f306f0f30f507806f0d306f06f06f00000006f000033033033033000083033033)) else (if i<4 then 0x870000bb0370500000870e70800000870000870870870000870870870030630870650000370700030030030030030700e30e500000000000006300000006306305d06f0d30630000000e10ef06f07006306306f0630870630630630d30000650650d10700370d300000006500006f06506500000006507006f06f065000 else (if i<5 then 0x7d01100001107f01100001106f00300306f01506f0030630000090090000ab08800900306300006b06b0000ab07806b0030830870870870000870000870000870000000430150000870000150000000cd0150000cb0000150ab0680000a10ad0a10770a10e70a10870a10b30130cb0130cf0130000130cd0130000000e90bb else 0x1507b01303300357800003303300000000300000001301301301301300300000300300000300300000056056000356056000000300000356000003300300303300300300300300330000000030000030000000300026000026000316000000016000016007f00001101101107d0110110030330000330330330c90330c9033))) else (if i<9 then (if i<7 then 0x330000030090005980030000335600301601741600331700000000150005600000330330330030130030330000330330190030330330330030001600330200035820000000030000030030000030000330035880030030030330030000035f0003003003000003000003003033003000000000000003033003003003009003 else (if i<8 then 0x330150c00000e00a03000e00e00a41600e00e00030151600000d00c00940d00d00902600d00d00030030900000b00a01600b00b00801620b00b001516016000300300000300301d00300300300300356000300300000300300300303300316000000305000000304100000003300000303f033033033033033033000592 else 0x150e01600b01600b41600d01605601600000050001601600f0060000013160134160160000015050000003000160003160000000120000160003160110160040000033160114160000033160030000033000160000033000160000033000160020160160000033000033000160000019000160011160000184160340180160)) else (if i<10 then 0x35a20000000030000030030000035a00330035a80030030030330030000030000030330030000031b0003000000000000000003003003003033003033003000160160160000003160160003160154000009000160160140003144100003015000015033015000003000003003015015000000033015000070120160160003 else (if i<11 then 0x2602602600332600112602782702722600333000002000c00c82002000c22602002000030032602600030000030030bd0030110035600030330bf0030000030030000330030030030050bb0000032602600001e00030030000000330000110030330335600330000000030190170330330330330332600001d0000000 else 0x150000030000030002600000000000002600000d20002600035602002602600d80d02600002562600032200000002600052462601f00000130002441e02600002340032362600000030002602200000002600032162600332102140000030000330330030330030000030030030030030030000032600330000001d0033)))) else (if i<18 then (if i<15 then (if i<13 then 0x330030030330113000003183103123000330033003000000030330000110030030000000000030000130030030030330030690005600030003000000032a0000033033033000033000033000033003033000000560033033003003033033033300300033290000015015000000015033033003015003000003015003015 else (if i<14 then 0x30000000030030330193003003000000033003000030e03000e23000e83002003005603002d02f63000033000000050003002e63000132e42b03003000000032a00000030003000002d00003000033002c62c00332c4300300000033300290000033000300000033000300003003000000000000003000003003003003 else 0x335600330330330330000000330000000000330330330330333c00330330330000330000330000030030000030030000005605b20035b05600000030000035600000330030030330030030030030000033200030030330bd3243260000030000030030c50030000c7003003000033033003000003000000033003003000000)) else (if i<16 then 0x1101103300000008303303333033633408508100003303303300003300003303303300003303303306f06f5e00310335c000006f5e40335c003300003300000001d00003303303300006f0330330330330335c00330330000035c20410035c00330035c8033560033033000000033045000033033033000003000033000009 else (if i<17 then 0x1101100301103301156001100002d02d02d45400050002d01507101507302d01b03302d02b07502d00007707902d02d02d00000003303303300003337003300000000003300000003303303342002303303303301101101100307d60000007f0030000010000030115d0003000011033560003011000011011560000560 else 0x2f00000300302101906702f00002f01702f01100301f02f03302300056002f03304702304901100903300004101b01101104500002301f0005c802303300302302302302b36202b02b02b01102d36035002b02b03302b00000002b00002b02b00003302b02b00001100000000002d01100303300001100302b56001f000003))) else (if i<21 then (if i<19 then 0x3303303300000300000000300303303300000303303300003303301300003300300000000000300056003300303303303301503300303300000001556003301900003303301500303300303303303301100003301703303301900301701501101303303303303303303356056000300000000000000301b03300002f560380 else (if i<20 then 0x3300003303301303303300000003300900308f00003303300000003300003500003303303300003300003300003303303300000300000000003303303303303300356000003300000303303300300303303300056003300001d00300300303300303300000001d055000560033033560003033000000033033000560033083 else 0x3500130130330000130330130333c03c03c005100f01303301301301304d3d001304b0000452b00f228800001301301300000000001307b0130133b00000130133c00130330133b20130130130130003c001301301300002b03301303303303300000000004b00004d0330333e00000450453c00410335600330335c8033033)) else (if i<23 then (if i<22 then 0x903300000000000056000300703303300000000300003356003300003303103300303300003303300303300003300901d0000000000000330000070330000330330090330000335600335600050030330330330330000330000330000330030030000005600330330030030330330330000000000000f010805304f02b033 else 0x3342001f03342003342001f03311203303311003342001f00001f01f01f03303302301108101f00301f01d01f00300b00100356001f03300003300042000001f01f01f00300003300003342003341203341000042000042000000003303303303303d03301f033033033033033033033003005033033033033033033033003) else (if i<24 then 0x3342001f00901d0c300300107100703300000501f03302302700002956000003301f01f01f00000308337000003303300003301f0033c003300040603301503303303340403301303303503342003303300056003301f00000000001f42003d2100350000000330000330331c800003302303300003303d33000003d00b2c0 else 0x49403106b06f0000a906b06b0000770000000005300ad06b0ab06b07d0a506b00006343000356007b06f00000008700300302b00300000356003300000304301900000003301100000300356000300300300000000000356000042603342403342008356003303303300303d00301f00303303303303303303303300001f081))))) else (if i<38 then (if i<31 then (if i<28 then (if i<26 then 0x4a00030610030030030050034a005f0000110670000130030030030030000030650030874b000006106100107306108d00000003308900008706108b0610000610000610610005600110030030035600034a00000030000c100300300006100303302d00004f00300000100f00306b00306300306b06b06b49608706b000 else (if i<27 then 0x6100300301503300000050000503f00300301500303300356000000300002d04f00000300300f0030110030130030030030000000000004600000002d01b64b04704804a04a01202204a003700f00600303100303100301103d00300300300338003b01901503900300300900300703b037003000015003003063440003000 else 0x50110630030030000030030030090000000002e01422400001301aa05b04302d03336401501503300001503301503305901500f03300001501505701501504100003f5005005005100150130150000430000000000000000000330004f00000150150000150875000150150155000150150153b4015033000000015003)) else (if i<29 then 0x5302f01522500a50a307d03900006b06b03103706b03100003b00006b0a109f03d09b06b06b06b00006b09d44803b46853053053006b06b06b00000301101156000303b06505100300348806b06b00300000353000306903306b00006d00003b003063003003000003000000000003000000003003560003001011000033013 else (if i<30 then 0x309900300303309700301500300000309b00356003301501500001502307b01502b01500301501501500301556000303301300000000300000000300356000000501100300300300300300306b53053006b06b00006b06b06b53003703106b06b06b00000047800006b07b00006b06b00000006b00000000044a150198530 else 0xf01350400f03300f00308900f4d607b01300004500303302307b00000900007b0050030a70415c807b0450450335600450450000000030000453c00450330000450330030030030000110030000000130000030030150030030055600030330330030030034c45600000030000330030000000050000130110030000004c6))) else (if i<34 then (if i<32 then 0x300100100100007b0030005040000130135600000030133c000303301350601301501300300056001300301300002b00001345000000002f5040030035600000070130030000000030030030050000130110000330030034e605d00300300f00356000f00300350000f0950000000750000150003a000f000000033000093 else (if i<33 then 0x330030030030030030030030090000000030000000c156003300300556000300000500703300002300507b0050030050000050690000000150030000110030000000130000030030030030030055600030330330030030af0010a90090a90010010030075600010030050330030010010010a90b1 else 0x150150150030035603f00030030150150000000150005600030035600000070034a000000300300001500000300300003353606500300300000302f06300353606500006500000349200356003353400349000500006300000000001d01300000300000301300300300302f033003560003526003524003560003560003)) else (if i<36 then (if i<35 then 0x30001601683001622600190170110330000030030330000030330030330000030150130330150030030090000030070000050005605605600030030030000000030070004b000300356000706100039009b00900700002f033556007007007003007560007007007000007560000003015000003033560546015015015015 else 0x2700330b90b503300006f06f0333d606f03306f03306f0b70b303300006f06f06f00006f03100001d0005c05c05c006f06f06f033003560003560003560003560003560003000000000000000000000033003003003003003003003560003000003560003000033000009000000000000003091003033003003003560003000) else (if i<37 then 0x1503300001501501501503f2802100000150151401101901d01701f00002700b40000b00e09d02240d01301002441601a02002540002500e41e01742400700f41b42341b02300902202602600f028006f5c000006f06551800006f05d51200006f0333e606f00006f00006f03306f00006f06f06f000000000010188310182 else 0x50170110330030330030330030000150130030030090030070030003c03c00150032141c02b42a01501200000000300f20c40f82b02c00000330331800000800d08d62900006c00c00a00000000158e078028028001503302d0330150330000330000150330000330130330150339f00418e4015033043033015015015015)))) else (if i<44 then (if i<41 then (if i<39 then 0x4383e20003e01101183f63f03403c04162f04103e84060004041124003864143801223164323144303103f44404401201280300000000001023203003709f03501088f07700103b01003300036d03d03263b63243b40004504200000330038f64268f4424019033033003003033003000003033033003003000003000003 else (if i<40 then 0x5901524e00000000300000000000001324a04809f00000035665605a09007904d44c00030005645204a61384a44e04e04b03400330331306b00190110030030330000330000030330030130030030099060079040030330170330030030030030030330150334e00030030030030054d64d00200150333609d03903303843a0 else 0x330390330330215d600d0330215d00335f00390330336200330000215f03705e40330336b00395e61680330395e00007700350000330330339160215d40339100336000000330331403605465005325760005804940004901429d05444b01503505884f65565305740005701485105385824961584f45544f0550470540590)) else (if i<42 then 0x6524d00116700000110230000111729d002f0116b066001101165093601101166001b5d066002d01138063002302393400002502d6600110116606800230006326400116608d01700110000235b86089d00000001605f06020000009d00330001625f00330000339140215f0000a02a000394c05f0a085f00236105f05c0033 else (if i<43 then 0x337007007000330336b06666646605f06b09469449407f00000330350336b06b06b00000001901980006b04e019239003303303502303300003702f03300001b03303303303303302303702f03303302f0350000236b00000009d00330330330007e00000000119d002366002901101102b660000027000023188660023011 else 0x3303303301d03303101d03300003303103301d0000330009760330331b24685d01b03b09d09d07106e07007007004f01c86400330335e07d09660006e20007209647708d070003301d00003503303300001d03300001d03300003302303300003b03303300103500001d0000330330330330336f001d03300003303503301d))) else (if i<47 then (if i<45 then 0x1f7b601f7f003d1f07f00330337a601f0000330007f03d003303d0337f003303303303303302303d03d00000b03301f0337a403303303361003d9867c00000330000000330330000000005001d877003301d1d07700330231d23c00319d00330017707709d07f05f0770706033033974704970700770770770031033035 else (if i<46 then 0x82000300b0139966540010030008208502000010038200112188100000038308d00170078200030098402129d00010006308200030008440000016e092000f0036508200030059509d00030030030000153e00330000350006b07f09809849d07b40000000336207f07c47700001f25207f02e07f07c67b00337a07f01f8033 else 0x130130008d00198d00159400210000039a201d0000039a09d09700038d001122000000300300366001f0018d082200901d0038d028800300300301700001302300301d0039d00008200077002228d00055408d03f00150000038340000030032d600d6f68000110038140190008205300030008d401b820015000)) else (if i<49 then (if i<48 then 0x598000589601d9c02509700059700050058760007400009d08869d07508669b07306b09b28d0980033013940864940940940680560298000874240410a1867088406824201301303300004f01301301303300003394094001301301303305102b03301301300001300004503301301301305300f03300001304d01304b033 else 0x1f02f9a001901d8408b600301327001d0150039e09a00037608440036a00030039a09d00008d05709700212520059d00019700239700050050050450050050470050059c297083400597042000003f01d03fa1800583600500000500001d72000502501d00597000571000505897002300504969001f77001d8940012a801d) else (if i<50 then 0x9400009a87060007042604408d67704e02889466607f08289a20009a02629706669445f02828229768209747008d49d09d02803c00000039d00070150030112b20468d00039c00050030009a000301d8d402f8500000000099a00039b001d0030319a09d00070030000000032b80218c60030170038a60154309a0580003000 else 0x500080800d00740e00001080960000940000300d60a00400180e60700b00c81020001000020f00760e40600120c20f60c00f40900d41101100100205902686b08d0664))))))
def vVal (i : Nat) := (vValA (i/85) >>> (12*(i % 85))) &&& 0xfff
def act (s i t : Nat) : Nat :=
  let j := off s+i
  let p := oa j
  let q := ov j
  let a := oa (j+1)-p
  let b := ov (j+1)-q
  vVal (q + ((t/a + aVal (p + t % a))%b))
def opTab (i : Nat) := (if i<3 then (if i<1 then ([(35,0x800000000),(36,0x1000000000),(37,0x200000001f),(38,0x4000000000),(39,0x80000003e0),(40,0x10000000000),(41,0x20000000000),(42,0x40000007c00),(43,0x800000f8000),(44,0x100000000000),(45,0x200000000000),(46,0x400001f00000),(47,0x800000000000),(48,0x100003e000000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x18000000000000000000000),(90,0x60000000000000000000000),(91,0x80210842108000000000000),(92,0x100000000000000000000000),(94,0x600000000000000000000000),(95,0x800421084210000000000000),(96,0x1000000000000000000000000),(97,0x2000842108420000000000000),(98,0x4000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else (if i<2 then ([(35,0x800000000),(36,0x1000000000),(37,0x200000001f),(38,0x4000000000),(39,0x800000f8000),(40,0x100000000000),(41,0x200000000000),(42,0x400001f00000),(43,0x80000003e0),(44,0x10000000000),(45,0x20000000000),(46,0x40000007c00),(47,0x800000000000),(48,0x100003e000000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x18000000000000000000000),(90,0x600000000000000000000000),(91,0x800421084210000000000000),(92,0x1000000000000000000000000),(94,0x60000000000000000000000),(95,0x80210842108000000000000),(96,0x100000000000000000000000),(97,0x2000842108420000000000000),(98,0x4000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else ([(35,0x800000000),(36,0x1000000000),(37,0x80000003e0),(38,0x10000000000),(39,0x200000001f),(40,0x4000000000),(41,0x20000000000),(42,0x40000007c00),(43,0x800000f8000),(44,0x100000000000),(45,0x800000000000),(46,0x100003e000000),(47,0x200000000000),(48,0x400001f00000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x60000000000000000000000),(90,0x18000000000000000000000),(91,0x80210842108000000000000),(92,0x100000000000000000000000),(94,0x600000000000000000000000),(95,0x2000842108420000000000000),(96,0x4000000000000000000000000),(97,0x800421084210000000000000),(98,0x1000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)))) else (if i<4 then ([(35,0x800000000),(36,0x1000000000),(37,0x80000003e0),(38,0x10000000000),(39,0x800000f8000),(40,0x100000000000),(41,0x800000000000),(42,0x100003e000000),(43,0x200000001f),(44,0x4000000000),(45,0x20000000000),(46,0x40000007c00),(47,0x200000000000),(48,0x400001f00000),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x60000000000000000000000),(90,0x600000000000000000000000),(91,0x2000842108420000000000000),(92,0x4000000000000000000000000),(94,0x18000000000000000000000),(95,0x80210842108000000000000),(96,0x100000000000000000000000),(97,0x800421084210000000000000),(98,0x1000000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else (if i<5 then ([(35,0x800000000),(36,0x1000000000),(37,0x800000f8000),(38,0x100000000000),(39,0x200000001f),(40,0x4000000000),(41,0x200000000000),(42,0x400001f00000),(43,0x80000003e0),(44,0x10000000000),(45,0x800000000000),(46,0x100003e000000),(47,0x20000000000),(48,0x40000007c00),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x600000000000000000000000),(90,0x18000000000000000000000),(91,0x800421084210000000000000),(92,0x1000000000000000000000000),(94,0x60000000000000000000000),(95,0x2000842108420000000000000),(96,0x4000000000000000000000000),(97,0x80210842108000000000000),(98,0x100000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)) else ([(35,0x800000000),(36,0x1000000000),(37,0x800000f8000),(38,0x100000000000),(39,0x80000003e0),(40,0x10000000000),(41,0x800000000000),(42,0x100003e000000),(43,0x200000001f),(44,0x4000000000),(45,0x200000000000),(46,0x400001f00000),(47,0x20000000000),(48,0x40000007c00),(49,0x20007c0000000),(84,0x1084210840000000000000),(86,0x6108421084000000000000),(88,0x600000000000000000000000),(90,0x60000000000000000000000),(91,0x2000842108420000000000000),(92,0x4000000000000000000000000),(94,0x18000000000000000000000),(95,0x800421084210000000000000),(96,0x1000000000000000000000000),(97,0x80210842108000000000000),(98,0x100000000000000000000000),(99,0x8000000000000000000000000)] : List (Nat × Nat)))))
def rot (g : Nat) (w : List Nat) := if g = 0 then w else w.map (spr (opTab (g % 6)))
theorem rokok (g : Nat) {s ws} (h : NatRun (mask 50) (goal 50) s ws) :
    NatRun (mask 50) (goal 50) s (rot g ws) := by
  unfold rot
  split
  · exact h
  · apply sprRun h
    exact (by decide +kernel : ∀ j : Fin 6, sprOK (opTab j) (mask 50) (goal 50) = true) ⟨_,Nat.mod_lt _ (by decide)⟩
def tickA (i : Nat) := (if i<3 then (if i<1 then 0x9c2b0945f16c6194290b85417c5b942a0b8541805b94290b8541805ba8310945f160548c2c0c45416c568c2c0c45417c568c280c45418c568c260c45418c568c2c0c454184568c2a0c45418c56942d0a85416c5f942e0a8541705fac2c0c45418c569c2c0c45418c56942c0c45418c568c2c0c45418c56942d0a8541705f else (if i<2 then 0x942c0c45417c5694260c45418c568c280c45417c569c280c45418c5694280c45418c569c2a0c0541885b9c2f0a854170619c290c0541845bc03109c5b16854942b09c6116c5f94270ac6117c5b9c290c0541885bb8310945b160548c280c454184568c260c45418456ac2c0c454184569c2c0c45418456942c0c45418456 else 0xac2c0c45418c58942c0c45418c58b8310945b16854ac280c45418c5eac2c0c45418c5a9c260c45418c5a9c290b8541885bac260c45418c5e8c280c45416c568c300c45418c56ac280c45418c56ac2f0b854180618c260c45416c568c2e0c45418c568c260c45417c56ac260c45418c569c260c45418c56942c0c45416c56)) else (if i<5 then (if i<4 then 0x94270ac611785ba83109c6116854ac260c45418c5a9c2a0c45418c5a9c280c45418c5a9c2a0c0541845b9c250ac5f1845b942a0b85417c5bac2c0c4541845aac2c0c4541845894260c45418c58ac280c4541845aac280c454184588c2a0c454184569c280c4541845a94300a8541705fac2c0c45418c5eac260c45418c58 else 0xac2e0c45418c5eac2d0c0541845f942e0a8541685fac280c45417c589c280c45418c5eac2d0c0541885f94260c45418456ac2c0c45416c58ac2c0c45417c58ac280c45418c58ac2e0c45418c589c2c0c45418c589c280c45418c588c260c45418c5e8c260c45418c5a8c2a0c45417c56942a0c45418c588c240c45418c56) else (if i<6 then 0xac2a0c0541885bac2f0a85417061ac290c0541885b9c2c0c45418c5e8c2e0c45416c568c300c45417c569c300c45418c5a9c2b0945f16c628c2c0c45418c5e8c2c0c45418c5a94300b8541805b94280c45418c588c260c45418c588c2c0c45418c588c280c45418c58ac2c0c45417c5eac300c45418c5eac2c0c4541845e else 0xac300c45417c5eac300c4541845eac290b8541805bac2c0c45416c5aac290b8541885b942c0c45418c5e8c280c45417c58ac280c45418c5ac0310945b1605494280c45418c5aac280c45416c5ac0310ac5b17854ac2c0c45416c5eac2a0c45418c5eac290c0541845b)))
def tick (i : Nat) := (tickA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def Z := scorebarrier 50 8 state ct act tick rot
theorem h0_0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0_0
theorem h1_0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1_0
theorem h2_0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2_0
theorem h3_0 : span (Z 3) 1 0 = true := by decide +kernel
theorem z3 : span (Z 3) 1 0 = true := h3_0
theorem h4_0 : span (Z 4) 10 0 = true := by decide +kernel
theorem z4 : span (Z 4) 10 0 = true := h4_0
theorem h5_0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5_12 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5_24 : span (Z 5) 12 24 = true := by decide +kernel
theorem h5_36 : span (Z 5) 12 36 = true := by decide +kernel
theorem h5_48 : span (Z 5) 12 48 = true := by decide +kernel
theorem h5_60 : span (Z 5) 12 60 = true := by decide +kernel
theorem h5_72 : span (Z 5) 12 72 = true := by decide +kernel
theorem h5_84 : span (Z 5) 12 84 = true := by decide +kernel
theorem h5_96 : span (Z 5) 1 96 = true := by decide +kernel
theorem z5 : span (Z 5) 97 0 = true := (@span_join (Z 5) 96 0 1 (@span_join (Z 5) 48 0 48 (@span_join (Z 5) 24 0 24 (@span_join (Z 5) 12 0 12 h5_0 h5_12) (@span_join (Z 5) 12 24 12 h5_24 h5_36)) (@span_join (Z 5) 24 48 24 (@span_join (Z 5) 12 48 12 h5_48 h5_60) (@span_join (Z 5) 12 72 12 h5_72 h5_84))) h5_96)
theorem h6_0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6_12 : span (Z 6) 12 12 = true := by decide +kernel
theorem h6_24 : span (Z 6) 12 24 = true := by decide +kernel
theorem h6_36 : span (Z 6) 12 36 = true := by decide +kernel
theorem h6_48 : span (Z 6) 12 48 = true := by decide +kernel
theorem h6_60 : span (Z 6) 12 60 = true := by decide +kernel
theorem h6_72 : span (Z 6) 12 72 = true := by decide +kernel
theorem h6_84 : span (Z 6) 12 84 = true := by decide +kernel
theorem h6_96 : span (Z 6) 12 96 = true := by decide +kernel
theorem h6_108 : span (Z 6) 12 108 = true := by decide +kernel
theorem h6_120 : span (Z 6) 12 120 = true := by decide +kernel
theorem h6_132 : span (Z 6) 12 132 = true := by decide +kernel
theorem h6_144 : span (Z 6) 12 144 = true := by decide +kernel
theorem h6_156 : span (Z 6) 6 156 = true := by decide +kernel
theorem z6 : span (Z 6) 162 0 = true := (@span_join (Z 6) 96 0 66 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 12 0 12 h6_0 h6_12) (@span_join (Z 6) 12 24 12 h6_24 h6_36)) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 12 48 12 h6_48 h6_60) (@span_join (Z 6) 12 72 12 h6_72 h6_84))) (@span_join (Z 6) 48 96 18 (@span_join (Z 6) 24 96 24 (@span_join (Z 6) 12 96 12 h6_96 h6_108) (@span_join (Z 6) 12 120 12 h6_120 h6_132)) (@span_join (Z 6) 12 144 6 h6_144 h6_156)))
theorem h7_0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7_12 : span (Z 7) 6 12 = true := by decide +kernel
theorem z7 : span (Z 7) 18 0 = true := (@span_join (Z 7) 12 0 6 h7_0 h7_12)
theorem h8_0 : span (Z 8) 1 0 = true := by decide +kernel
theorem z8 : span (Z 8) 1 0 = true := h8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < ct s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
def rs : List Nat := [5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 14, 14, 14, 14, 14, 17, 17, 17, 17, 17, 22, 22, 22, 22, 22, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 1, 2, 5, 6, 9, 10, 12, 14, 17, 18, 20, 22, 24, 26, 28, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 13, 21, 25, 30, 3, 3, 7, 7, 11, 11, 13, 15, 19, 19, 21, 23, 25, 27, 29]
def xs : List Nat := [0xfffef7bdef7bc08a8000f83ff,0x577f18c6318c555503ff07c00,0x99996b5ad6b5a6667c1f07c1f,0xe1e1ad6b5ad6b8787fe007fe0,0xfe01ce739ce73f807ffff8000]
end ceaa8a888
open ceaa8a888 in
theorem lower_eaa8a888 : bound 0xeaa8a888 9 := by
  apply mkBound 0xeaa8a888 8 50 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have hh : NatRun (mask 50) (goal 50) 8 xs := extend_run h hs
  have hp : xs.Perm (state 8 0) := by decide +kernel
  exact scorebarrier_all rokok checked 8 (by decide) 0 (by decide) (Run.perm hp hh)

namespace ceaa8c888
def rs : List Nat := [13, 13, 13, 13, 17, 17, 17, 17, 22, 22, 22, 22, 26, 26, 26, 26, 28, 28, 28, 28, 1, 2, 5, 5, 6, 6, 9, 9, 10, 10, 12, 13, 13, 17, 18, 20, 22, 22, 24, 26, 26, 28, 28, 3, 14, 21, 25, 3, 14, 21, 25, 3, 14, 21, 25, 3, 14, 21, 25, 3, 14, 21, 25, 3, 3, 7, 21, 7, 14, 11, 25, 11, 14, 14, 15, 29, 19, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def xs : List Nat := [0x16fcefeeeee8038cd000ff,0x2db7bb999999b43320ff00,0x39cf1e33333639c3cf0f0f,0x3f0ff0555557c1fc0ff00f,0x3ff844666667fe000ffff0]
theorem no : search 43 6 xs = false := by decide +kernel
end ceaa8c888
open ceaa8c888 in
theorem lower_eaa8c888 : bound 0xeaa8c888 7 := by
  apply mkBound 0xeaa8c888 6 43 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 43) (goal 43) 6 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction
namespace ceaa8e880
def wdA (i : Nat) := (if i<7 then (if i<3 then (if i<1 then 0x5e2c58b162c58b001e00000000007f0054204081020408007e000000000000002a1c3870e1c38700000000001fffff000a0c183060c183001e0000001fffff00020408102040810006000000003fff000000000000000007860007f00000000000000000000000000000000000000000000000000000000000000000000000 else (if i<2 then 0x382c58b162c58b1000000000fe03fff0380c183060c183007800007ffe00000028244891224489106860007f000007f020204081020408100000000000000000080408102040810008000000fe0007f007e3c78f1e3c78f07fe0007f01fffff007e3c78f1e3c78f007e0000001fffff007e3c78f1e3c78f001e0000001fffff else 0x1b0b8f1e3c78f1e33f1e03fff01fff8018894a952a54a952389803f80fffc07f128a4c993264c993000000000000007f1280408102040810000000000000000003fefdfbf7efdfbf07fe0007ffffffff0382c58b162c58b13f9e03ffffe03fff0382c58b162c58b107860007ffe03fff0382c58b162c58b106860007ffe03fff)) else (if i<5 then (if i<4 then 0x5b83c78f1e3c78f1000000000fe000005b81c3870e1c387007800007ffe000005b81c3870e1c3870000000000fe0000058291a3468d1a34600000000001fc00053aaddbb76eddbb70000000000003fff492193264c993264c961fc000fffff801b8bcf9f3e7cf9f33f9e03ffffffffff1b81c3870e1c38703f8003ffffe00000 else 0xa4542040810204080000000000000000a400000000000000ff81fffff00000005bffffffffffffff007e00000fffffff5babdfbf7efdfbf707860007ffffffff5babdfbf7efdfbf7000000000fffffff5babdfbf7efdfbf7000000000fe03fff5babdfbf7efdfbf700000000001fffff5b8bcf9f3e7cf9f3000000000fe0007f) else (if i<6 then 0xae57264c993264c90e060007ffffc000a7d6e5cb972e5cb9ffffffffffe03fffa67e3c78f1e3c78f067e0007f01fffffa65624489122448906060007f0000000a60000000000000006000007f0000000a47e3c78f1e3c78ffffffffff01fffffa454204081020408fffffffff0000000a454204081020408369e03fff0000000 else 0xb6de6cd9b366cd9b301803f80000007fb6de6cd9b366cd9b06060007f000007fb6de6cd9b366cd9b000000000000007fb6d664c993264c99368603fff0000000b68a4c993264c993368003fff000007fb680408102040810368003fff0000000b65e2c58b162c58b361e03fff0000000b45c2850a142850a301803f800000000))) else (if i<11 then (if i<9 then (if i<8 then 0xe4743060c183060cc061fc0000000000b7deeddbb76eddbb379e03ffffe03fffb6fe7cf9f3e7cf9f36fe03fff01fffffb6de6cd9b366cd9bfffffffff000007fb6de6cd9b366cd9b369e03fff000007fb6de6cd9b366cd9b369e03fff0000000b6de6cd9b366cd9b368603fff000007fb6de6cd9b366cd9b361e03fff000007f else 0xfc01020408102040f801fff800000000f7fefdfbf7efdfbff7fffffff0003ffff7fefdfbf7efdfbf369e03fff0003ffff7deeddbb76eddbbf79ffffff000007ff780c183060c1830f781fffff0000000f6fe7cf9f3e7cf9ff6fffffff000007fe776b56ad5ab56adc767fc07f0003f80e776b56ad5ab56ad06060007f0003f80) else (if i<10 then 0xff7fbf7efdfbf7efff7ffffff01fff80ff77b76eddbb76edc767fc07f0003f80feff7efdfbf7efdffefffffff01fc07ffefd7af5ebd7af5ef879fff8001fc000fe7f3e7cf9f3e7cff879fff8001fc000fc7d3a74e9d3a74ef8f9fff8001fc000fc7d3a74e9d3a74ef879fff8001fc000fc7d3a74e9d3a74ec061fc00001fc000 else 0xff81c3870e1c3870ff87ffffffe00000ff81c3870e1c3870ff81ffffffe00000ff81c3870e1c3870ff81fffff0000000ff81c3870e1c3870f801fff80fe00000ff81c3870e1c3870f781ffffffe00000ff81c3870e1c3870c701fc07ffe00000ff81c3870e1c3870368003ffffe00000ff81c3870e1c387006000007ffe00000)) else (if i<13 then (if i<12 then 0xffd5e3c78f1e3c78ffffffffffe00000ffd5e3c78f1e3c78ff9fffffffe00000ffd5e3c78f1e3c78ff81ffffffe00000ffabdfbf7efdfbf7ff81ffffffffffffffabdfbf7efdfbf7368003ffffffffffff8bcf9f3e7cf9f3ff81ffffffe0007fff83c78f1e3c78f1ff87ffffffe03fffff83c78f1e3c78f1ff81ffffffe00000 else 0xfff7f7efdfbf7efdffe7ffffffe03f80fff5f3e7cf9f3e7cc061fc000fe00000ffdfefdfbf7efdfbff9fffffffe0007fffdfefdfbf7efdfbff9fffffffe00000ffdfefdfbf7efdfb369e03ffffe0007fffddebd7af5ebd7aff99ffffffe00000ffd7e7cf9f3e7cf9ff87ffffffe00000ffd7e7cf9f3e7cf906060007ffe00000) else (if i<14 then 0xfffffffffffffffff879fff80ffffffffffffffffffffffff7ffffffffffffffffffffffffffffffc767fc07ffffffffffffffffffffffff369e03ffffffffffffffffffffffffff06060007ffffffffffffffffffffffff000000000ffffffffffdfbf7efdfbf7efff9ffffffffc000fffdfbf7efdfbf7ef879fff80fffc000 else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03ffffffffffffffffffffffffffff01fffffffffffffffffffffff9fffffffffffff))))
def wd (i : Nat) := (wdA (i/8) >>> (128*(i % 8))) &&& 0xffffffffffffffffffffffffffffffff
def stA (i : Nat) := (if i<6 then (if i<3 then (if i<1 then 0x12632c462404982ed4890105da3222404176a488900ed196222404982ed18801260bd461c04982ed28501260bb461404982ece8501260bb541404982ed4850105da3221404982ed184000344e768c000cd3dda30002b495e8c00092b0e9b00024c03a54000aced1970000060926c0000000000000000000000000000000 else (if i<2 then 0x15a0bb464405482ed19101460bb464405682dd191015a0b646440568cb11910105da33c44041768ce910105daa464405f82ed491015a0bb524404176a4e910159da32c4403b4674b110159da92c440564668b1101660bb463805682ed190015a0be463405682ed20f01260bb46280567eed18b01260bb462404982d9189 else 0x15a4c1768405692b119b01260bb3a6c056930119501b24c13a54063930519401260bb548c0619305da9017e4c176a405e9305da9015a4c176a40519305da9015a4c16ca4056931962901260bb527404982ed529017e4c176980569305e28015a7bb466404982ed198015a0bb464806282ed19101860bb464405f82ed191)) else (if i<4 then 0x1464c1768c0609305da301424c1768c0569305d23015a4c1728c0659305a23018e4c1648c0569305c23015a4c16c8c0529305b23015a4416c8c0569305aa301260bb5a8c0619319623015a4c6588c056931562301260bb46780569305da201260bb467c05f9305d9d01320bb467404982ed19d01260b646740498cb119d else (if i<5 then 0x9305da3121eb4982ed18501260bb46164c1768c485ad260bb461ab4982ed183ad260bb4606b4982ed481ad05da322064c1768c48101aab4982ec0569905da3015a5c1768c0569505da301924c1768c0619305da301764c1768c0589305da3017e4c1768c05e9305da3015e4c1768c0569305da301564c1768c0539305da3 else 0xad260bb462f9c982ed189cb260bb4626e4982ed189ad260bb462404982ed189931a0bb462764982ed1899305ebb46264c176ed1899305db246264c176b11899305da546264c1768d1899305da33a264c1768ca89ad260bb522404982ed4899305da94626b41768c8899305da32224041768c8899305da31226b4982ed187))) else (if i<9 then (if i<7 then 0xad05dbb4646b4176c9191ad05db04646b4176b1191ad05da44646b41768d191ad05da33a464c1768ce910105da33a46b41768ce11ad05da32a4405682ed491ad260bb5246b4176a51910159da32c46b41768cb11ad05da32246b4982ed18ead05da3223ab4982ed18dad05da32236b4982ed18fad05da3223eb4982ed182 else (if i<8 then 0x1260bb52764c176a519dad260bb5256b4982ed4a9ad260bb4c8eb4982ed4a6ad260bb508eb4982ed4a8ad260bb4666b4982ed193e75a0bb46474d682ed191cb5a0bb4646e5682ed191b35a0bb4646b5682ed191015a0bb4646b4d82ed191df5a0bb4646b4982ed191ad1e0bb4646b4682ed191d95a0bb4646b417ced191 else 0x9305da33a56b4982ed1949305da33a52b4982ed18cad260bb5c8eb4982ed52301260bb548e4c176a919d017e4c176a79d69305da9cb5a4c176a6e569305da9bf5a4c176a6b569305da9015a4c176a6b498d05da9d95a4c176a6b4982f1da9ad260bb76a6b4982ed929ad260bb58a6fc982ed4a3ad260bb528eb4982ed49d)) else (if i<11 then (if i<10 then 0xad260bb568eb4982ed3a3ad260bb488eb4982ed2a3ad260bb468eb4982ed1a0b95a4c176772c982ed19db9260bb4676b4982ed19d01260bb46764c682ed19dd9260bb46771c982ed19d9305dbb46764c176c919d9305dac46764c1768d19d9305da33a76b4982ed19bd95a4c176576569305195ad260bb4656b4982b1195 else 0xc75a4c1768edd69305da3ad464c1768c0519305da3d9464c1768eb498b05da3d75a4c1768eb4982f1da3ad260be768eb4982f5da3ad260bb768eb4982eda23ad260bb668f2d69305923cb260bb648eb4982ed923ad260bb628c0569305b23db5a4c16c8eb4982edb23015a4c6588eb498ced623c3260bb588eb4982ed623) else (if i<12 then 0xad260bb4646b4982ed18901260bb46273e59305da301864c1768c05f9305da3e75a4c1768f9569305da3e15a4c1768f2d69305da3c35a4c1768ee569305da3b55a4c1768efd69305da3b35a4c1768eb569305da3015a4c1768f8d69305da3dd5a4c1768eb498d05da3ad26241768eb498705da3ad26141768f6569305da3 else 0x569305da3cb5a4c1768ee569305da3ad5a4c1768c0569305da3ad26341768f6569305da3ad260bb768eb4982ed923ad260bb588eb4982ed1a3ad260bb467404982ed19dad260bb46540569305da9ad260bb528c05682ed191))))
def st (i : Nat) := (stA (i/24) >>> (42*(i % 24))) &&& 0x3ffffffffff
def off (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0 else 1) else (if i<3 then 2 else 3)) else (if i<6 then (if i<5 then 4 else 10) else (if i<7 then 110 else (if i<8 then 285 else 304))))
def ct (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 1 else 1) else (if i<3 then 1 else 1)) else (if i<6 then (if i<5 then 6 else 100) else (if i<7 then 175 else (if i<8 then 19 else 1))))
def state (s i : Nat) := unpackWords wd 7 9 (st (off s+i))
def oaA (i : Nat) := (if i<1 then 0x1f87d1f07b1e8791e0741cc721c4701b06b1a8691a0671986519063188611805f16c5a15c521444e1304a1204511043108411003f0f83d0f03b0e8390e0370d8350d0330c8310c02f0b82d0b02b0a8290a0270982509023088210801f0781d0701b06819060170581505013048110400f0380d03009020060140400c0200400 else (if i<2 then 0x4c9314b52c4ad2a4a52849d2548d214751c46d184551143d0c425074190541103400ff3f4fc3ecf83dcf53d0f13c0ef3b0e93a0e7394e4388e1380dd370db368d9360d5344ce328c7310c1300bf2f8bd2ecb92dcb62ccb22c4ae2b4ac2a8a92a0a6290a3288a027c9c2609524c912408d22889220872188521083208812007f else 0xe4b86ddf6bd7f53d233cccb24c630cbeeefb86d5b16b9aa699a3688a02769ca6d9a6649765b95a5193a4c912408f2378ca2f8aa2587a1c85e0f82a05801fb7e9f77cdec799e5789e076dd3739ca709bc6e9b56c1ab6a5a76919c66d966559262d856057b5e1735b96c5a56458d6056d585494d52945509414f93b4e1374d935))
def oa (i : Nat) := (oaA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def ovA (i : Nat) := (if i<2 then (if i<1 then 0x17a0bc05902c414e09804b82240fa07103081480a2050027813809a04c02581280920480238118086042020810007e03e01e80f007603a01c80e006e03601a80d006603201880c005e02e01680b005602a014809804a024011808804202000f807803a01c00d806803201800b805802a00e006801800a0040018008002000 else 0x6363181858c2860e2ee1750b5059e2b915a0a6c50c27f13d89e04ca257128892848a24111f08dc46422d10b084842220610108044001f50f907703ae1c10d906a83281820b285782ae1500a7851c28c1450a2050c2841410a004fc27c13d09e04ec27412f097049824a11d089844821210007b83b81da0e006a032018e0c6) else (if i<3 then 0xeb473f3941c18db86be34f19f8cce64d317185cc025e52f21730b6459d2be157ca7c52228813f49de4d926593109824be25c92d49504a324f126492a49124511cc8b845622390c085842620890347ec3f11ee0f247843bf1dd8ee07663af1d18e807363891c28dfc6f03731b78db06ce3601ad8d586a433d1980cb065031c else 0x8e1c66a29f109868c2a20bf0107eabe39e82f0675bba35c88e1b6e6b691aaed0d6723335944c7862e30fd846c085f52f51776b9c5c3adc568cb2a5872bcd5b4ac35562a3d4e2a5b51ea8493ea9d74dc26853149734aea50525492948aa3f91c48b744d21e109683140a1fdcfbe7c03d39e38ef075b))
def ov (i : Nat) := (ovA (i/78) >>> (13*(i % 78))) &&& 0x1fff
def aValA (i : Nat) := (if i<3 then (if i<1 then 0x40000004400000000000000000000000000000000001c08000000000008480000000000000000000000000038100001000204003000c000002418006001000400080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0800006000000000000 else (if i<2 then 0x2800b0a00000000068000000000014002000020002000800000000000000900000020000000000008000000000000000000000000004800000380000000000000021600000000099500040000600080000000e0a0000000000890000000020000000000000000080000020000000000a000000e0800100000000228000 else 0x200020800100101800214005000c001002801a004c681000450016180080049300443c20730003010014580003048500003061c180000c080060210e00101c7000008a812a080010008003141000302080800248581002c100022808d001c50004305810c0000800141800a2010000000000000005000038000000000014005)) else (if i<5 then (if i<4 then 0x230e0c0000c240000c243000a0c3050038180024c0030008183124400b0c1880a0c2c00202001800a3400f4c18180461c18922005861a0c00d2a3c7002818010281c0800a40000000018a0208a8100040850400203001c0800e00d8c180800f4c20a0050151851204580007c0041ca0da500883a5181429702004802410100 else 0x100366411c870421228e010a52bc100649810a08441174c90100366411b86d41947ca818a512468078e869976e821254bc20a588d800048180a1e101174c9010036641002a0c3861e98683008c003008071f106421d0a080000c2400e0a2c20000184831a3450006440161c007810000888220c60c0240000002c0801e98303) else (if i<6 then 0x18a3c101144c7c100300010a1e101174e94100326c1002c2593d289dfae60646b538ecc327cec029580c03902d4f32388c4b2628124447085332cd003c1e9473750f0dac14f404b807d337145c6b002780293a8112d8f00b3e46ccd14783d803000540a50101174838100366413382401ab8661b0b5001ea37c28f04045d324 else 0x50f0808ba74a0801936085428ad162528747340c6d13a003580a04616b26a0149a)))
def aVal (i : Nat) := (aValA (i/146) >>> (7*(i % 146))) &&& 0x7f
def vValA (i : Nat) := (if i<27 then (if i<13 then (if i<6 then (if i<3 then (if i<1 then 0x9d09900000100b00100100100100100900100000000000b00000009500100d00b00100100100100100100900100100000000000000000000000000000100000000100b00003800100100900000000000000100000000100100100000000d0b30080bb0b70b70b90000b700003d00003d00003d0b503d0b100009b000000000 else (if i<2 then 0x100102f00003d03d02f00003d03d02003d00003d04603d03d00102f00000002f02f0a500002f02f02000002f02f09307502000003b00d03b03b03b00003b03d03b0450100670670000670670670000670970670ad01200003b0ab01000003b00003b03b03b00003b03b03b09909900009905a09b000000000099099058 else 0x107f00000100100000000100100107f00000100100000000109f02f02f00000002f02f0a90a902f02f00000002f00000900000900002f00000900003d00900900008d00008d00002f00008d0000a708d08d00100d00b00b04300000b00b00000000b00103f0580000010410010010010010010010010a301403d001001000)) else (if i<4 then 0xf00000f000100000100000100003f00000100b00102f00b00100b00100100100100100100109b04600000b0000a100b00b00b00b00b00100003d00000900002f0000090010000af06306300006300006309b00009909909d09909909909909900100100107f00000100100000000100100107f000001001000000001001 else (if i<5 then 0x10010000010010015b00010010010000090010070010000010000010010010090000000090000000000000070010010070010010000010010010010010070010010000010010015805800010010005805800005800000000000010010090010010010010010013300000003300003300012500000002500002500010f0000 else 0xb00940b00a00b00f00b02500b00010f00f000100000700000908300000000100700b00000700700d0070035800070070070010f00000070700000000010015800400010000000010010050010000000000010010000030010010010500000000010500100500120500180500200505b00500000500000f0001000001060000))) else (if i<9 then (if i<7 then 0x70f00f00f00800000010e60e40f00f00000010700000070000f00010f00000f00000004900f00d000b0f00000010f00600f00f00010000500000850010010010f00010400010000000000010000010000010830010010010010010000030000f00012e00a00c00a20c00a80c00f00c03300c0000020001370001001010090 else (if i<8 then 0x60259000100100100100100160800000100000100100100000100100100100d0010000071000010010000010010010090010010f00f00f00000010f00f00000070000f00010500f00000010010000000000090010010010010010000010000010010010070000000500010b00f00b20f00b80f00c00f05800f00000d00000f0 else 0x6d00000000100100900100100100100100100100700100025000115000700700100105503b00000000100000b00000700000900700d00000700758000125000000713000058000100100000000100000500000100000d00100000005500100100100d001001250250001120000001001000009001001000000000001000007)) else (if i<11 then (if i<10 then 0x100100003b00100100100d00100000100000103d00000100100d0010010011e00000011801e01841e01a01e01d01e04001e00000010002500000030002501701c01b00003300a01b01b01742501b01b00010012601a0190000170000190180250090190190252160190001001250250000061001001000000001580000001 else 0x1b025058025000725000024022000122425000900000000d00000000000000700100100d00100100000100100100000100025000020000025000725025025014000000123021425025000000d13000000700025000125000000000025028000d25027000000025020000b2501f00012501202502500010001e00001e0001250) else (if i<12 then 0x10010010010013302c00013403300010010000950092a00010002b000100100000700000100100d0010010010000000010010000000000090010010010010010000010000010010010072502502500000012502500010002500000070002500010002501502502500000010000010002501e00010b0250190250194250 else 0x2f02f02f02f02f01a01a21a84002e000003b0010000000010010012f000100100100100100103d0000010015b00010010010000030003303303300003500000010000010010010010010090000010000000005800010070010010000010010010003300012d00070000015a0001580001000000001000009001000001000001)))) else (if i<20 then (if i<16 then (if i<14 then 0x73300003203140013163303300000073302c000000700033000000100033033000000033000b3603000130000015b00012f000000000000100002d0010000010000010000010010010010010070000015b00012f00000000000010000090010000010000010000010010010010010004200012f0000330420000000001350 else (if i<15 then 0x1d03703702e04000303700001d800137005037000100100100000000000000000004000000103d00000100100100100100103b0001c00003500005b03500201c23503501c80013503303303300000013303300070003300010003302d03303303500010000010003300003303303303303303500010c01b01b21b8580300330 else 0x3d00000138000100100100103f00000140000100100104100100000000161000b58000000900000b00000b58000b00700100000b00b00b0000570015c000b58000100b00000d00700000000000100100100d0000010090010010010010000010000000010000090000010000010070010000010010010010000010010001d2)) else (if i<18 then (if i<17 then 0x6700b00300b4d000b00000b03d00304500d04340000b04700040000b00000303b00300303b00000300300100300104900000000000000339000300100d00000100162000000000158000900103f00000158000700100100100000000100000100158000100100162203b400410000001001001000001001412000001001000 else 0x500d00000302f00000000102158004b3b001500700d02102102100102101104f0450000670670670673a23a006b00000006706706700006706700006706706706906739000000300b00000000000900701306700358000d00100100305700000000300300d00000300300100b00000b00b00000000002f00946400000100b) else (if i<19 then 0x10003e000b00b03d00b00b00000b40000000b03b00b00000100054004300100b00100100b00b00b03d00b07500b40000000300100100000000000000500000100140000140000140000100000000100100000100103d40000100100140000100103b00100000000000100100000100100140000100100104d0003c0021009 else 0x100000000003b00003b03b00140004100000000003b07303f00300000003f03b00b03b03b38000100003b00d03b00d40000300103b03b03b00003b03b03b00000d00000000040003b00300000b03b03b40003b00100103b03b03b4f003b00140004100100700100100100055000100100000000100000000100103d001001))) else (if i<23 then (if i<21 then 0x31e200140000100d03d0000010010011e800100100d40000503b00140000140003b37003b00140000104b00000d03d07503b3b000100003d3e000000003b03b00103b03b03b00000d03b40003b00000103b00003b4000013900013f60013f400140000140004540000100100500103b001001001001001001000000000 else (if i<22 then 0x3b03b00d03b03b00300140003b00000100003b03b00000100100140000100100100103d00100140000100100100003b00000100000100000100100900100100100000158000100740000100000100100100000100000100003b00000100000100158000103d00100000100100b00003d2f00001e000140000100003b00003d else 0x100000100000140000100000100000106d00100100158000100100100000100000100100058000100100540000100000100100000000300100000100100100100300300300d00000700700100100140001100d06f06f00f00b00000000358000300001305f00300300300b00103f00d00003b00b03b40007300103b00003f)) else (if i<25 then (if i<24 then 0x570000090015800000015800070000010010015800010000000000000010010010010010010010000015800010000000770090015800010015800070010010000006300000000010010000015d000100000100100000106100000100100100000145000000000100000106d001001001580001001001000001000001061000 else 0x900909105b47005b00000005b05b02f09105b47002f00002f08d08d05505b08f05b00907505b00005b05548000000000b5e000b00b05505700000000000000000000b5e000b00000b04d00b00b00b00b00b5e000b00100000900947000b00b00b58000b00b00000700100b00000005b00b58000b0015e000b00b00b000001) else (if i<26 then 0x4d04d000100100100100000100100100000000b00900b0094d058000006500300700000300300300100000100300100700300300300300300300d01b00d0074700000002002b64704704700d010630000900902901f00000902f08100002f02300002f00000900902f02d00900905d02f3e000900900902f4800003c0000009 else 0xb02f00702f58000002f02f0000570015f002900000902f02f00100d05702f0e022231021029a4d04d04d000100100100100000d00d00100000b0050000034d04d000100900300100100901b0013f00090010030010090013a400000100100100000000000007f0010004b00000010014d04c0001001001001001001009003))))) else (if i<40 then (if i<33 then (if i<30 then (if i<28 then 0x100100000108700058001701701705500b00b00000701300000000700158006700100303b01301300001300101300d01301305306305f00005d05500000706105d00000700703f00700000700700700700700000000158000158000000100000900000000100000100000100100100100100700102f00000002f001000009 else (if i<29 then 0x8b00d00d00000000700d58000000d00d00d00100d00d00100000100d00000500d00d00000100100100100109300000007700100100700000100100158000100100000000103b58058000000700700300100d00700000000000700700700b00700700000100750000b5e000000002f05700108905500b00900000000701702f else 0x46000000700500758000700100702100000003b00700100000702100d00000104d0004d400700700100700d05b00107f4a60000010015300010010014d40010010010010010000050674d000100100100000100300158000100000000700b00b00000700758000700100700d03b00700000300700d007001001000007007)) else (if i<31 then 0x55000900158000100100100000700100100000100100000000023024811823232000100100100100000d00d00100000b0050000030000000010710070010010710070014000070010710010075505505500010010010000010004c40000010014c6550001001001000005001550067001001001000007001550001000001000 else (if i<32 then 0x500158006700100100100000700158000100000100000055000700b0550000610004f000704103b00000700000000300700058000700d00700000d001007001007007003001580001000000000001550001000001001001001051001001001013001001001001000007001000001001000000071000000000001001000 else 0x700700700b00758000d00100000b00705503b00700007700000300000100700700700100700700700000000100158000000900900100000100100100700700100000100100100100100102158000b00100100000000703b00000008b00d00008b00700700100700700700700b0000010004d40000010014d6550001001001))) else (if i<36 then (if i<34 then 0x5800010010010015800013d00010010010010090010070010010010010010010010010000000000015700005800015800015800015800010010010010090010070010010010010010010010010000000000015600004e600158058002100700947058005b00100000100000000003b00000d00700d001007007000000001000 else (if i<35 then 0x100000000700d58000100100000000100d0010000010010010010000010010090010000000000015800015800010000010000010010090010010010070010010010000000002502580f025233000100100100100000d00d00100000b005000003000000001009007001001009007001400007001009001007580580 else 0x105705500b01700100b00b00b00158000100000000000158000100000100100100102d00100100101300100100100001300007301301301300000b58000001300101301300300101300d03f00d01300703b01300100100042000100100000000958000100100000000700102d0010010010015b0013001001001001001)) else (if i<38 then (if i<37 then 0x100d00d00000d00d00000000d00d00158000158000100100100100900100700100100100100100100100100000000000158000051600151400700d00100000700700d00700000158000700700705500b00358000000106100000700703b0000075805e000b00900000000b05900100000b00b00700b00b05700b001017000 else 0x505b02685b035002d0002605b001300100b00100102d00142000d00100101301300d0030010130050010010012625b000102d00158000158000100100100100900100700100100100100100100100100000000000158000058000158000000000d00000d00158052600d00d00d00000d00d00d009007580440) else (if i<39 then 0x1501681b20960d81241941201900601801c01c00d21d005505507b5000005e005502f05507d05506f05500000000b05505550406f05500b05500000000027028800628236005700b05500b00000b02f07900000b00b00002f00000005700b05500b00b05705500b43005500b00000b0005e05e05e000b00b00b000000000400 else 0x9ab01741301f61f02009007e01d01d00070000b01100a60e80a490600090400100100100d00100100500100700100900100100100000100100000d00100b0090031f41e00090010010070010070010011d00e0a200010010000c01001861401621a60001b00940700900c2a101840b00d00f01b81261961601a40001a00c8)))) else (if i<47 then (if i<43 then (if i<41 then 0x4004702a2ab03d09142802a82908f6001001260240000460009a303200003700100009107f00000000070d02d000100100100d00100000500100700100900100100100000d00100100100100d00100b0090033e03e000900100100700100700d0010303e02640010010000001761700000300000000000000000a00800000e2 else (if i<42 then 0x1000001000003001001007001009001000009ab00010012c800d00100b005001510ac00090010010070010070010075305305300010010000c02e04203403804400003c02540002502b0a103942900e02c04543304303603b43903b03103503844502702a42f43a42f03a02302b44104102a03e03743000010010004043f0 else 0x6900390036101002e85c05705645f00005a84a62e24a42e0a105764e01102d85f65605d05585a20005a00005805665f44c02d25525865505844a05745b05b02d05305000005200004b60004b40304f00202c25e00099260009245405906004d00000074f60004f44b02c04e0a400010015960005949200f07d000100100100d)) else (if i<45 then (if i<44 then 0x7007187626763286947446907406f07307707703226200000006c00001206b0a106b00252f26b06580030000279440036b04f06a202f025003000003a500256b00030030252f06b07d003900000300303966202f0000036b000300002f00300368001b6d00396a002f0000036b000300000300301b9460256600038f0003308 else 0x57a6680a1000d00001578000178000b0000017a0a2099600178068478001f7903387800016f07a47b0001001994780001015780780001001990a1000013000172078072600177001f0000010000037800013300016400003180000003105107127560007606747706703126307346f0320500768696746710754000750736) else (if i<46 then 0x66081000b00b0000001403480010017d000002334000100b0007d0770a603425306b60010019a4a109a0a107d07d07d000500100300100000d7d07d00210059a600300000100578000100d0210010036b40016b00017d000170000100100168600001f00000172400033201500d00000000100001f7d00010015200016f0 else 0x10010018a0007a10001000001000a10001001372550ad0820000820850830a10000a1000b00b820820820820930710000160378a708406a48006a00008f40008f036049600b01700b01702f03100001700b00002f82082003301700b00b01900b00b00b00b9b601784400b03500b00b00b00b01703100b00b00b00b00b00b))) else (if i<50 then (if i<48 then 0x1300000082200300701701da8000700701b9e20070000078200037300078f0007a109a00070078f00000003d81708a08b09807200298a05600000010000016800073808a0488001029001a200079d60018100298f00030003828a00010070000298a00010000050010010298120010010018a00070000179d40010010018c0 else (if i<49 then 0x7501a03f86d00000006c00010018743b059000100100100000100700003700100000500100500100000100100100d007960007a1000100100700100100500100000d00100b0010039a09a00000010013908f0a100008f03e88f03928f00170070150070190000110076b09e000000f1808f05700030000000070070170078a0 else 0x785001d00000000f0093c00079e00210075a00000070000090000079e00077600008f0007000009a100078400091b00079e00009e00099e00078f40079c0844015025a000000270079e09f0017007aa08960130110074028760009a0886884a10000000000a908649a08669f07d00010079509a09a09709f28f09a02283b2)) else (if i<52 then (if i<51 then 0x90010000054205c000100100100100d007a20007a1000100100900100100d00100b001003009a20a200010011c0418a208f07708a4a800009e86b60006b48f67d04105b01d03e8a868a0a608289e20009e04129a08a6a847803e28229a68209a46b08f4a10a103e05306e0a100000000070000070002160070074089e09e0 else 0xa20a968d0a60a60a607900010130504420001e0448000a604405e00010010017b000101300002d00100000500102d00100100100100100d013a1001300000100101300100102d00102d00d00100b001003a60a60a60001001000000000000a208a4a80000000000000a20a20a868a0a601d04288a6a84780000001001007422) else (if i<53 then 0x11000a80a8001d000007a20017a90007ae0013a80003a808e4003000a80007019a100007c00078f0000452003a800078e60078b00170000075f00070000030480071f0007aa00070008c0aa2007a800077a002bae2007468007a1000f450015000007a80003000017a80007a80000000a10000000a608d4a908d6a947d0 else 0x381000c00700b41200000e80660000640c60900300500100281260b01100a80e20000e00320d00b61240800220a20d60a00d40600c40f00f0020040017))))))
def vVal (i : Nat) := (vValA (i/85) >>> (12*(i % 85))) &&& 0xfff
def act (s i t : Nat) : Nat :=
  let j := off s+i
  let p := oa j
  let q := ov j
  let a := oa (j+1)-p
  let b := ov (j+1)-q
  vVal (q + ((t/a + aVal (p + t % a))%b))
def opTab (i : Nat) := (if i<3 then (if i<1 then ([(6,0x7f),(13,0x3f80),(20,0x1fc000),(27,0xfe00000),(50,0x6000000000000),(52,0x18000000000000),(54,0x60000000000000),(55,0x80000000000000),(56,0x100000000000000),(58,0x6000007f0000000),(59,0x800000000000000),(61,0x300003f800000000),(63,0xc001fc0000000000),(113,0x20408102040810000000000000000),(115,0x80810204081020000000000000000),(117,0x201020408102040000000000000000),(118,0x542040810204080000000000000000),(119,0x804081020408100000000000000000),(120,0x1008102040810200000000000000000),(121,0x2000000000000000000000000000000),(123,0x8010204081020400000000000000000),(124,0x10000000000000000000000000000000),(126,0x40000000000000000000000000000000),(127,0xa4000000000000000000000000000000)] : List (Nat × Nat)) else (if i<2 then ([(6,0x7f),(13,0x1fc000),(20,0x3f80),(27,0xfe00000),(50,0x18000000000000),(52,0x6000000000000),(54,0x60000000000000),(55,0x80000000000000),(56,0x800000000000000),(58,0x300003f800000000),(59,0x100000000000000),(61,0x6000007f0000000),(63,0xc001fc0000000000),(113,0x80810204081020000000000000000),(115,0x20408102040810000000000000000),(117,0x201020408102040000000000000000),(118,0x542040810204080000000000000000),(119,0x804081020408100000000000000000),(120,0x8010204081020400000000000000000),(121,0x10000000000000000000000000000000),(123,0x1008102040810200000000000000000),(124,0x2000000000000000000000000000000),(126,0x40000000000000000000000000000000),(127,0xa4000000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x3f80),(13,0x7f),(20,0x1fc000),(27,0xfe00000),(50,0x6000000000000),(52,0x60000000000000),(54,0x18000000000000),(55,0x100000000000000),(56,0x80000000000000),(58,0x6000007f0000000),(59,0x800000000000000),(61,0xc001fc0000000000),(63,0x300003f800000000),(113,0x20408102040810000000000000000),(115,0x201020408102040000000000000000),(117,0x80810204081020000000000000000),(118,0x542040810204080000000000000000),(119,0x1008102040810200000000000000000),(120,0x804081020408100000000000000000),(121,0x2000000000000000000000000000000),(123,0x8010204081020400000000000000000),(124,0x40000000000000000000000000000000),(126,0x10000000000000000000000000000000),(127,0xa4000000000000000000000000000000)] : List (Nat × Nat)))) else (if i<4 then ([(6,0x3f80),(13,0x1fc000),(20,0x7f),(27,0xfe00000),(50,0x60000000000000),(52,0x6000000000000),(54,0x18000000000000),(55,0x100000000000000),(56,0x800000000000000),(58,0xc001fc0000000000),(59,0x80000000000000),(61,0x6000007f0000000),(63,0x300003f800000000),(113,0x201020408102040000000000000000),(115,0x20408102040810000000000000000),(117,0x80810204081020000000000000000),(118,0x542040810204080000000000000000),(119,0x1008102040810200000000000000000),(120,0x8010204081020400000000000000000),(121,0x40000000000000000000000000000000),(123,0x804081020408100000000000000000),(124,0x2000000000000000000000000000000),(126,0x10000000000000000000000000000000),(127,0xa4000000000000000000000000000000)] : List (Nat × Nat)) else (if i<5 then ([(6,0x1fc000),(13,0x7f),(20,0x3f80),(27,0xfe00000),(50,0x18000000000000),(52,0x60000000000000),(54,0x6000000000000),(55,0x800000000000000),(56,0x80000000000000),(58,0x300003f800000000),(59,0x100000000000000),(61,0xc001fc0000000000),(63,0x6000007f0000000),(113,0x80810204081020000000000000000),(115,0x201020408102040000000000000000),(117,0x20408102040810000000000000000),(118,0x542040810204080000000000000000),(119,0x8010204081020400000000000000000),(120,0x804081020408100000000000000000),(121,0x10000000000000000000000000000000),(123,0x1008102040810200000000000000000),(124,0x40000000000000000000000000000000),(126,0x2000000000000000000000000000000),(127,0xa4000000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x1fc000),(13,0x3f80),(20,0x7f),(27,0xfe00000),(50,0x60000000000000),(52,0x18000000000000),(54,0x6000000000000),(55,0x800000000000000),(56,0x100000000000000),(58,0xc001fc0000000000),(59,0x80000000000000),(61,0x300003f800000000),(63,0x6000007f0000000),(113,0x201020408102040000000000000000),(115,0x80810204081020000000000000000),(117,0x20408102040810000000000000000),(118,0x542040810204080000000000000000),(119,0x8010204081020400000000000000000),(120,0x1008102040810200000000000000000),(121,0x40000000000000000000000000000000),(123,0x804081020408100000000000000000),(124,0x10000000000000000000000000000000),(126,0x2000000000000000000000000000000),(127,0xa4000000000000000000000000000000)] : List (Nat × Nat)))))
def rot (g : Nat) (w : List Nat) := if g = 0 then w else w.map (spr (opTab (g % 6)))
theorem rokok (g : Nat) {s ws} (h : NatRun (mask 64) (goal 64) s ws) :
    NatRun (mask 64) (goal 64) s (rot g ws) := by
  unfold rot
  split
  · exact h
  · apply sprRun h
    exact (by decide +kernel : ∀ j : Fin 6, sprOK (opTab j) (mask 64) (goal 64) = true) ⟨_,Nat.mod_lt _ (by decide)⟩
def tickA (i : Nat) := (if i<3 then (if i<1 then 0xc836034751c476c834018731c47634320fc7f1d47118320f4761f071341b018771c47834360e87f1e47518340e87f1e47318320f47f1cc71183a0f47f1f07118320f47f1dc7118340e87f1dc73180d06c781dc71181406c7b1dc7334320fc7f1f87118320f47f1f0711814034751c4733414018731c475180d050751cc71 else (if i<2 then 0x6c3f018731dc7b180d0507f1cc71503d0fc7f1d4736c0d050751cc71183a0f47f1ec71343a0fc7f1d471183a0f47f1cc7150360f47f1ec75181b034781c47718340e8761e4736c3b0e87f1e47b181b0507b1cc77341406c7b1e075343a0fc7f1f8716c370fc7f1f87734320fc761f871501b018771cc7b34360e87f1e075 else 0x1814034761c473183a0d0761cc71180d050761cc713414018761c475501b034781d47b18320f47f1ec7134140187b1e075341b0507b1d47818320f47f1f87118340e8761e07350340fc7f1f87318340e87f1e07334060507b1d471343a0fc761ec711832050761cc71341406c7b1dc73e83d018731c47f6c3f018711dc78)) else (if i<4 then 0x34320f47f1f07134320f47f1f871340606c771e0716c3b0e87f1e47318340e87f1c47334320d87f1d47118320d07f1cc7134320fc7f1e0713406050761d47118140347b1dc73501b034781d473f43f050751cc7f3406050731d471183a0f47f1d471183d0e87f1e07334320fc761d471f43f06c781dc7f34320fc7f1ec71 else (if i<5 then 0x180d06c7e1dc71183a0fc7f1cc716c14034751e07b183f0f47f1cc71183f0e87f1c473341b0507b1d479343a0f47f1d4713432050761d47134060507f1d471183a0f47f1d479180d050751cc796c0d050751dc78343a0fc7f1d4796c0d050751ec78183a0d8761cc71180d0507e1cc7134320d8761d47118320fc7f1f871 else 0x500606c771f873503d0fc771f873181406c7e1dc73343f06c7b1e075)))
def tick (i : Nat) := (tickA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def Z := scorebarrier 64 8 state ct act tick rot
theorem h0_0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0_0
theorem h1_0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1_0
theorem h2_0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2_0
theorem h3_0 : span (Z 3) 1 0 = true := by decide +kernel
theorem z3 : span (Z 3) 1 0 = true := h3_0
theorem h4_0 : span (Z 4) 6 0 = true := by decide +kernel
theorem z4 : span (Z 4) 6 0 = true := h4_0
theorem h5_0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5_12 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5_24 : span (Z 5) 12 24 = true := by decide +kernel
theorem h5_36 : span (Z 5) 12 36 = true := by decide +kernel
theorem h5_48 : span (Z 5) 12 48 = true := by decide +kernel
theorem h5_60 : span (Z 5) 12 60 = true := by decide +kernel
theorem h5_72 : span (Z 5) 12 72 = true := by decide +kernel
theorem h5_84 : span (Z 5) 12 84 = true := by decide +kernel
theorem h5_96 : span (Z 5) 4 96 = true := by decide +kernel
theorem z5 : span (Z 5) 100 0 = true := (@span_join (Z 5) 96 0 4 (@span_join (Z 5) 48 0 48 (@span_join (Z 5) 24 0 24 (@span_join (Z 5) 12 0 12 h5_0 h5_12) (@span_join (Z 5) 12 24 12 h5_24 h5_36)) (@span_join (Z 5) 24 48 24 (@span_join (Z 5) 12 48 12 h5_48 h5_60) (@span_join (Z 5) 12 72 12 h5_72 h5_84))) h5_96)
theorem h6_0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6_12 : span (Z 6) 12 12 = true := by decide +kernel
theorem h6_24 : span (Z 6) 12 24 = true := by decide +kernel
theorem h6_36 : span (Z 6) 12 36 = true := by decide +kernel
theorem h6_48 : span (Z 6) 12 48 = true := by decide +kernel
theorem h6_60 : span (Z 6) 12 60 = true := by decide +kernel
theorem h6_72 : span (Z 6) 12 72 = true := by decide +kernel
theorem h6_84 : span (Z 6) 12 84 = true := by decide +kernel
theorem h6_96 : span (Z 6) 12 96 = true := by decide +kernel
theorem h6_108 : span (Z 6) 12 108 = true := by decide +kernel
theorem h6_120 : span (Z 6) 12 120 = true := by decide +kernel
theorem h6_132 : span (Z 6) 12 132 = true := by decide +kernel
theorem h6_144 : span (Z 6) 12 144 = true := by decide +kernel
theorem h6_156 : span (Z 6) 12 156 = true := by decide +kernel
theorem h6_168 : span (Z 6) 7 168 = true := by decide +kernel
theorem z6 : span (Z 6) 175 0 = true := (@span_join (Z 6) 96 0 79 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 12 0 12 h6_0 h6_12) (@span_join (Z 6) 12 24 12 h6_24 h6_36)) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 12 48 12 h6_48 h6_60) (@span_join (Z 6) 12 72 12 h6_72 h6_84))) (@span_join (Z 6) 48 96 31 (@span_join (Z 6) 24 96 24 (@span_join (Z 6) 12 96 12 h6_96 h6_108) (@span_join (Z 6) 12 120 12 h6_120 h6_132)) (@span_join (Z 6) 24 144 7 (@span_join (Z 6) 12 144 12 h6_144 h6_156) h6_168)))
theorem h7_0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7_12 : span (Z 7) 7 12 = true := by decide +kernel
theorem z7 : span (Z 7) 19 0 = true := (@span_join (Z 7) 12 0 7 h7_0 h7_12)
theorem h8_0 : span (Z 8) 1 0 = true := by decide +kernel
theorem z8 : span (Z 8) 1 0 = true := h8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < ct s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
def rs : List Nat := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 17, 17, 17, 17, 17, 17, 17, 22, 22, 22, 22, 22, 22, 22, 26, 26, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 6, 6, 10, 10, 12, 12, 18, 20, 22, 22, 24, 26, 26, 28, 28, 7, 11, 13, 14, 19, 21, 25, 7, 11, 13, 14, 19, 21, 25, 7, 11, 13, 14, 19, 21, 25, 7, 11, 13, 14, 19, 21, 25, 7, 11, 13, 14, 19, 21, 25, 7, 11, 13, 14, 19, 21, 25, 7, 11, 13, 14, 19, 21, 25, 7, 14, 11, 14, 13, 14, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def xs : List Nat := [0x5babdfbf7efdfbf7000000000fffffff,0xb6de6cd9b366cd9b369e03fff000007f,0xe776b56ad5ab56adc767fc07f0003f80,0xfc7d3a74e9d3a74ef879fff8001fc000,0xff81c3870e1c3870ff81ffffffe00000]
end ceaa8e880
open ceaa8e880 in
theorem lower_eaa8e880 : bound 0xeaa8e880 9 := by
  apply mkBound 0xeaa8e880 8 64 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have hh : NatRun (mask 64) (goal 64) 8 xs := extend_run h hs
  have hp : xs.Perm (state 8 0) := by decide +kernel
  exact scorebarrier_all rokok checked 8 (by decide) 0 (by decide) (Run.perm hp hh)

namespace ceaaac880
def rs : List Nat := [3, 3, 3, 3, 13, 13, 13, 13, 22, 22, 22, 22, 26, 26, 26, 26, 28, 28, 28, 28, 1, 3, 5, 5, 6, 6, 9, 9, 10, 10, 12, 13, 13, 16, 18, 20, 22, 22, 24, 26, 26, 28, 28, 7, 11, 14, 17, 7, 11, 14, 17, 7, 11, 14, 17, 7, 11, 14, 17, 7, 11, 14, 17, 17, 19, 7, 21, 7, 14, 11, 25, 11, 14, 14, 15, 29, 17, 19, 21, 23, 30, 25, 27, 30, 29, 30]
def xs : List Nat := [0x16fcefddddd8018cf000ff,0x2da7bb3bbbb9b43320ff0f,0x39cf1e2aaaae39c3cf0ff0,0x3f0ff0333337c1fc0ff0f0,0x3ff845c44447fe000fff00]
theorem no : search 43 6 xs = false := by decide +kernel
end ceaaac880
open ceaaac880 in
theorem lower_eaaac880 : bound 0xeaaac880 7 := by
  apply mkBound 0xeaaac880 6 43 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 43) (goal 43) 6 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction

namespace ceac0e8c0
def rs : List Nat := [9, 9, 9, 9, 19, 19, 19, 19, 21, 21, 21, 21, 26, 26, 26, 26, 28, 28, 28, 28, 2, 3, 3, 4, 5, 5, 10, 10, 12, 12, 17, 18, 19, 19, 20, 21, 21, 24, 26, 26, 28, 28, 6, 11, 13, 25, 6, 11, 13, 25, 6, 11, 13, 25, 6, 11, 13, 25, 6, 11, 13, 25, 6, 7, 11, 6, 7, 13, 11, 14, 13, 14, 25, 22, 23, 27, 22, 23, 29, 25, 27, 30, 29, 30]
def xs : List Nat := [0x5ed5dbbbbb81b43600fff,0xb3eb7ccccccc38c70f0f0,0xe76eed555571c338f0f00,0xfc9f93bbbbbe03c0ff00f,0xfff00222223ffc00ffff0]
theorem no : search 42 5 xs = false := by decide +kernel
end ceac0e8c0
open ceac0e8c0 in
theorem lower_eac0e8c0 : bound 0xeac0e8c0 6 := by
  apply mkBound 0xeac0e8c0 5 42 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 42) (goal 42) 5 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction

namespace ceac8e0c0
def rs : List Nat := [11, 11, 11, 11, 21, 21, 21, 21, 26, 26, 26, 26, 28, 28, 28, 28, 2, 3, 3, 4, 5, 5, 9, 9, 10, 11, 11, 12, 12, 17, 17, 18, 18, 20, 21, 21, 24, 26, 26, 28, 28, 6, 13, 19, 25, 6, 13, 19, 25, 6, 13, 19, 25, 6, 13, 19, 25, 6, 7, 19, 6, 7, 13, 13, 25, 14, 15, 27, 13, 14, 19, 25, 19, 22, 22, 23, 29, 25, 27, 30, 29, 30]
def xs : List Nat := [0x179ddeddddc0c66f600ff,0x2cf6e3eaaaa6187070f0f,0x39e36f666678e1838f0f0,0x3f0bfc15555f01fc0ff0f,0x3ffc9099999ffe000fff0]
theorem no : search 41 4 xs = false := by decide +kernel
end ceac8e0c0
open ceac8e0c0 in
theorem lower_eac8e0c0 : bound 0xeac8e0c0 5 := by
  apply mkBound 0xeac8e0c0 4 41 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have h' : NatRun (mask 41) (goal 41) 4 xs := extend_run h hs
  have hh := search_ok h'
  rw [no] at hh; contradiction
namespace ceac8e880
def wdA (i : Nat) := (if i<10 then (if i<5 then (if i<2 then (if i<1 then 0x482040810204000cc00001fc00000014183060c1830003c00001fffff0000408102040810730c000fe03fff0000408102040810000c0000003fff000000000000000c90c3f8000000000000000000000000730c000fe00000000000000000000000000000000000000000000000000000000000000000 else 0xfc78f1e3c78fc90fff8001fffff000fc78f1e3c78f073fc000fffffff000fc78f1e3c78f000fc00001fffff000fc78f1e3c78f000cc00001fffff000fc78f1e3c78f0003c00001fffff000ec68d1a3468d000cc0000003f800005c3870e1c3870000c00001fc07f0004c2850a14285000cc00001fffff) else (if i<3 then 0x3d058b162c58b106f0c000fe03fff03d058b162c58b100c000000003fff03d0183060c183007f00000fe00000038050a142850a10700c000fe03f800250489122448910630c000fe0007f02004081020408100000000000000001801020408102001c000000003f8000500810204081000f00000000007f else (if i<4 then 0x18712952a54a95238f3007f01fc07f12514993264c99300000000000007f12500810204081000000000000000003dfdfbf7efdfbf07ffc000fffffff03d058b162c58b1cffcff80fe03fff03d058b162c58b13ff3c07ffe03fff03d058b162c58b107f0c000fe03fff03d058b162c58b10730c000fe03fff else 0x4c2020408102040cf303f80fe00000460fc78f1e3c78f060fc000fffffff4604c2850a142850600c000fe0000046000000000000006000000fe00000440482040810204c70cff80fe000004404820408102040000000000000001bf179f3e7cf9f33ff3c07ffffffff1bf03870e1c38703ff0007ffe00000))) else (if i<7 then (if i<6 then 0x4ff03870e1c3870cff03f80fe000004c2fe7cf9f3e7cfcf3fff80fffffff4c2fa74e9d3a74ec80f3f8001fc0004c24a2448912244fffffffffffc0004c24a2448912244cf3cff80fffc0004c24a2448912244c80c3f8001fc0004c24a2448912244c73cff80fffc0004c24a24489122440630c000fffc000 else 0x5e702850a14285006300000fe000005e25e3c78f1e3c70600c000fffc0005c75ab56ad5ab56fffffffffffc07f5c2fa74e9d3a74e000f000001fc0005c25a3468d1a3460000000001fc0005c20204081020400000000000000005655cb972e5cb970600c000fe0007f4ff4faf5ebd7af5cffcff80fffffff) else (if i<8 then 0x5e75ebd7af5ebd70630c000fe0007f5e75ebd7af5ebd706300000fffc07f5e75ebd7af5ebd70600c000fffc07f5e75ebd7af5ebd70000000001fc07f5e75ab56ad5ab5606300000fffc0005e74ead5ab56ad50630c000fe000005e7169d3a74e9d306300000fe0007f5e712952a54a9523ef3007ffffc07f else (if i<9 then 0xa18a142850a1428f9cf3fff0003f805ff5fbf7efdfbf707f0c000fffffff5ff03870e1c387007f00000fe000005e7fefdfbf7efdf063fc000fffffff5e75ebd7af5ebd7cf3cff80fffc07f5e75ebd7af5ebd73ef3c07ffffc07f5e75ebd7af5ebd70630c000fffc07f5e75ebd7af5ebd70630c000fffc000 else 0xb3db5dbb76eddbb38c3007f0003fffb3db5dbb76eddbb37f3c07ffe03fffb3db5dbb76eddbb30c3007f0003fffb3db5dbb76eddbb000000000003fffb3db1d3a74e9d3a30c3007f0000000b3d0183060c183030c0007f0000000b00b050a142850a3003007f0000000a38a54a952a54a9000000000003f80)))) else (if i<15 then (if i<12 then (if i<11 then 0xe78e962c58b162cc70c3f80fe00000e78a54a952a54a9c7003f80fe03f80e784d2a54a952a5c700ff80fe00000e78010204081020c7003f80fe00000e60ec68d1a3468dc60cff80fe00000e40fc78f1e3c78fc00fff8001fffffe40e860c183060cc00c3f800000000e40000000000000c0003f800000000 else 0xe78ed6ad5ab56adc70cff80fe03f80e78ed6ad5ab56adc70cff80fe00000e78ed6ad5ab56adc70c3f80fe03f80e78ed6ad5ab56adc700ff80fe03f80e78ed6ad5ab56adc60cff80fe03f80e78ed6ad5ab56adc00c3f800003f80e78ed6ad5ab56ad0600c000fe03f80e78ed6ad5ab56ad000000000003f80) else (if i<13 then 0xf7d0183060c1830f7c03ffffe00000f78fd7af5ebd7aff70ffffffe03f80efaef6eddbb76edcf3cff80fffff80efaef6eddbb76edcf3cff80fe03f80edaeb66cd9b366cfffffffffffff80e7dedebd7af5ebdc7fcff80fe03fffe78fd7af5ebd7afc70fff80fffffffe78ed6ad5ab56adffcffffffe03f80 else (if i<14 then 0xfc2fa74e9d3a74e3003007f01fc000fc2020408102040f8003fff0000000f7dfdfbf7efdfbff7cffffffe03ffff7dfdfbf7efdfbfc70cff80fe03ffff7dfdfbf7efdfbf36c3c07ffe03ffff7dfdfbf7efdfbf30c3007f0003ffff7dedebd7af5ebdf7ccfffffe03f80f7db5dbb76eddbbf7c33ffffe03fff else 0xfe7faf5ebd7af5ef80f3fff01fc000fe2fe7cf9f3e7cff80f3fff01fc000fdafb76eddbb76ef9cf3fff01fc000fc2fa74e9d3a74eff3ffffffffc000fc2fa74e9d3a74ef90f3fff01fc000fc2fa74e9d3a74ef8cf3fff01fc000fc2fa74e9d3a74ef80f3fff01fc000fc2fa74e9d3a74ec00c3f8001fc000))) else (if i<18 then (if i<16 then 0xfff03870e1c387006300000fe00000ffaff7efdfbf7efff0ffffffffff80ffaff7efdfbf7efc70cff80fffff80ffafb76eddbb76ef80f3fff01fc000ffaef6eddbb76edff0cfffffe03f80ffa03060c183060ff003ffffe00000fe7fefdfbf7efdffe3ffffffffc07ffe7fefdfbf7efdfc63cff80fffc07f else (if i<17 then 0xfff03870e1c3870fffc3ffffe00000fff03870e1c3870fff0fffffe00000fff03870e1c3870fff03ffffe00000fff03870e1c3870ff303ffffe00000fff03870e1c3870f8c03fff0000000fff03870e1c3870f7f03ffffe00000fff03870e1c3870c7303f80fe00000fff03870e1c387036f0007ffe00000 else 0xfff5bb76eddbb76fff03ffffffc000fff4faf5ebd7af5fff0fffffe00000fff4ba74e9d3a74fffcfffffffc000fff4ba74e9d3a74fffcfffffe00000fff4ba74e9d3a74fff03ffffe00000fff179f3e7cf9f3fff03ffffe0007ffff078f1e3c78f1fff0fffffe03ffffff078f1e3c78f1fff03ffffe00000)) else (if i<19 then 0xfffefefdfbf7efdc73cff80fe03f80fffebe7cf9f3e7cfffc3ffffe00000fffb7dfbf7efdfbfff33ffffe03ffffffb7dfbf7efdfb30c3007f0003ffffffb3d7af5ebd7afff33ffffe00000fff5fbf7efdfbf7fff0fffffffc07ffff5fbf7efdfbf7c730ff80fffc07ffff5fbf7efdfbf736f0c07ffffc07f else (if i<20 then 0xfffffffffffffffc73cff80ffffffffffffffffffffff36f3c07fffffffffffffffffffffff30c3007f01ffffffffffffffffffff0630c000fffffffffffbf7efdfbf7effff3ffffffc000ffffbf7efdfbf7ef8cf3fff01fc000fffefefdfbf7efdfffcfffffe03f80fffefefdfbf7efdfffcfffffe00000 else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80ffffffffffffffffffffffffe03fffffffffffffffffffffcfffffffffffffffffffffffffffff3ffffffffffffffffffffffffffff3ffffffffffffffffffffffffffff8cf3fff01fffffffffffffffffffff7fffffffffffff)))))
def wd (i : Nat) := (wdA (i/8) >>> (120*(i % 8))) &&& 0xffffffffffffffffffffffffffffff
def stA (i : Nat) := (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x5f4d41190d00005f4d47190d00005f412b190d00004d411f190d0000715f4d410c000071614d410a0000715f4d410b0000715f4d44090000715f4d41080000715f4d41060000009d935f410000009a974d41000000935f4d3c000000855f4b3c00000000000000000000000000000000000000000000000000000000 else 0x854d411f19000085412b1f190000895f4d41150000855f4d4118000085624d41140000855f4d41170000855f4e41160000855f4d46130000715f4d410e0000855f4d410500009a5f4d410d0000715f4d410d0000715a4d410d000071594d410d0000715f4d3c0d00005f4d41340d0000715f412b0d0000715f472b0d) else (if i<3 then 0x715f4d41200000855f4d411a000097854d41190000965f4d41190000935f4d411900008e5f4d41190000855f4d41190000835f4d41190000815f4d41190000855a4d41190000805f4d4119000085594d41190000855f4c411900005f4d4541190000855f4d3c190000855f4d47190000855f412b190000855f472b19 else (if i<4 then 0x85715f412b000083715f412b000081715f412b000085705f412b000085715a412b000080715f412b0000856f5f412b0000857159412b000085715f3c2b000085715f472b00008d715f41270000855f4d412d000085745f412a000085715f412900008571654123000085715f43280000855f4d411b0000715f4d410f else 0x85785f4d33009b995f4d41330000965f4d41330000935f4d41330085715f4d3a330000715f4d412600009c85714d25000085714c41250000857159411e000085715f412c0000715f4d412f0000978571412b0000857164412b00009a855f412b000096715f412b000093715f412b00008e715f412b00008c715f412b))) else (if i<8 then (if i<6 then 0x8571594d4100008071594d410000856f594d4100008571584d41000085714d41380000715f4d4541000085715f4d40000085715f4d3e000085715f4d3f00009f85714d3a009b715f4d413a00009a5f4d4137000085715f4d3d00009b855f4d3c000085715f4d3c000083715f4d3c000085715a4d3c0000855f4d4134 else (if i<7 then 0x8c715f4d41000087715f4d41000086715f4d41000085715f4d41000084715f4d41000082715f4d41000081715f4d41000085715d4d41000085715e4d4100009971574d41000085715c4d4100009771544d41000085715b4d41000085715a4d41000083715a4d410000715f524d41000080715f4d4100007f715f4d41 else 0x85716a5f41000085715f4f410000a1935f4d4100009a995f4d4100009a955f4d4100009a855f4d4100009a835f4d410000857c5f4d41000085775f4d41000085765f4d41000085755f4d41000085735f4d41000085725f4d41000098715f4d41000096715f4d4100008e715f4d4100008b715f4d41000088715f4d41)) else (if i<9 then 0x85715f412b0d0000715f412b0d00715f4d412b0d00855f4d41190d00715f4d41190d00005f4d41190d00715f4d410d0d0085715f4d410a00715f4d410d0a0085715f4d410900715f4d410d090085715f4d41070085715f4d41040085715f4d41010085715f412b0100855f4d41190100715f4d410d0100009485715f41 else (if i<10 then 0x99715f4d410d0092715f4d410d0085715f4d410d007e715f4d410d0000715f4d410d00716d5f4d410d009f715f4d410d0071615f4d410d00715f5f4d410d00715f544d410d00715f514d410d009e715f4d410d00715f4d44410d00715f4d41410d00715f4d41370d00715f4d41330d00715f4d41250d00715f4d411e0d else 0x855f412b190085715f412b1900855f4d412b190000854d411f1900855f4d411f1900855f4d4119190085715f4d411500855f4d4119150085715f4d411400855f4d4119140085715f4d411600855f4d4119160085715f4d411300855f4d4119130085715f4d41110085715f4d41020085715f4d411000a7715f4d410d)))) else (if i<17 then (if i<14 then (if i<12 then 0x855f5f4d411900855f544d411900855f514d4119009e855f4d411900855f4e4d411900855f4d4d411900855f4d4a411900855f4d49411900855f4d48411900855f4d46411900855f4d41411900855f4d41371900855f4d41331900855f4d41251900855f4d411e190000855f4d47190085715f4d471900855f4d474119 else (if i<13 then 0x85715f4d41210085715f4d411c00a7855f4d4119009b855f4d41190099855f4d41190095855f4d41190092855f4d41190089855f4d41190085855f4d41190000855f4d411900857e5f4d411900a1855f4d41190085795f4d41190085715f4d411900856e5f4d411900856d5f4d4119009f855f4d41190085625f4d4119 else 0x85715f43412b0085715f41412b0085715f41372b0085715f41332b0085715f412b250085715f412b1e000085715f472b0085715f47412b0085715f412b2b0085715f4d41270085715f412b270085715f4d412a0085715f412b2a0085715f4d41230085715f412b230085715f4d41280085715f412b280085715f4d4103)) else (if i<15 then 0x85715f412b00857e715f412b00a185715f412b008579715f412b008574715f412b008571715f412b0085716e5f412b0085716d5f412b009f85715f412b008571655f412b0085715f5f412b0085715f54412b0085715f51412b009e85715f412b0085715f4d412b0085715f4a412b0085715f49412b0085715f48412b else (if i<16 then 0x85715f4d41240085715f4d4122009e85715f411e0085715f4d411e0085715f4d331e0085715f4d411d0085715f4d4112008571635f4d410085715f4d41350085715f4d41300085715f4d412e00a785715f412b009b85715f412b009985715f412b009585715f412b009285715f412b008d85715f412b008585715f412b else 0x715f4d4a41370085715f4d4136000085715f4d3c00a185715f4d3c0085715f4d413c008579715f4d33009b855f4d41330085795f4d41339985715f4d41330085715f4d413300855f514d41330085715f4d41320085715f4d4131009f85715f4d25009f85714d4125008e715f4d41250085715f4d41250085714d484125))) else (if i<20 then (if i<18 then 0x9c85715f4d4100008571594d410085715f594d41009e8571594d410085715f4d43410085715f4d42410085715f4d46410085715f4d44410085715f4d41410085715f4d413b0085715f4d413a0085715f4d4139009285715f4d37009785714d4137009b715f4d41370092715f4d41370085715f4d413700715f544d4137 else (if i<19 then 0x85715f554d4100998571544d410099715f544d410085715f544d41000085715a4d4100a185715a4d410085715f5a4d410085715f534d4100857e5f514d410096715f514d410085715f514d410085715f504d41009e85715f4d41009085715f4d41008580715f4d41000080715f4d41009e80715f4d410085716b5f4d41 else 0x8571675f4d41008571665f4d41009f85715f4d41009785715f4d41009185715f4d41008581715f4d41000081715f4d41009f81715f4d4100857d715f4d41008578715f4d410085716c5f4d41008571605f4d41008571655f4d41008571625f4d41008571615f4d410085715f5f4d410085715f574d410085715f564d41)) else (if i<21 then 0x9685715f4d4100a385715f4d41009285715f4d41008f85715f4d41008e85715f4d41008a85715f4d41008d85715f4d41008985715f4d41008585715f4d41000085715f4d4100a285715f4d4100857e715f4d4100857b715f4d4100857a715f4d4100a085715f4d410085716d5f4d41008571695f4d41008571685f4d41 else (if i<22 then 0x85715f4d411e000085715f412b0085715f4d412b0000855f4d41190085715f4d41190085715f4d410d0000715f4d410d00a19b855f4d4100009a855f4d41009b99715f4d41000096715f4d41009992715f4d4100008e715f4d4100a785715f4d4100a685715f4d4100a585715f4d4100a485715f4d41009985715f4d41 else 0x85715f4d41009985715f4d41009285715f4d41008585715f4d41000085715f4d4100857e715f4d410085716d5f4d41009f85715f4d410085715f5f4d410085715f544d410085715f514d41009e85715f4d410085715f4d41410085715f4d41370085715f4d41330085715f4d4125)))))
def st (i : Nat) := (stA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def off (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0 else 1) else (if i<3 then 2 else 3)) else (if i<6 then (if i<5 then 4 else 8) else (if i<7 then 145 else (if i<8 then 389 else 411))))
def ct (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 1 else 1) else (if i<3 then 1 else 1)) else (if i<6 then (if i<5 then 4 else 137) else (if i<7 then 244 else (if i<8 then 22 else 1))))
def state (s i : Nat) := unpackWords wd 8 9 (st (off s+i))
def oaA (i : Nat) := (if i<2 then (if i<1 then 0x650c818c310610c01782d85a0ae150298520a21402784e09a1302584a0921202384608a110218420821001f83e07a0f01d83a0720e01b83606a0d0198320620c01782e05a0b01582a0520a01382604a090118220420800f81e03a0700d81a0320600b81602a050098120220400780e01a0300580a0120200300400600800800 else 0xf51e43c0758e91d039c730e41c6384700df1bc3746e0d91b035c6b0d51a8344680cf19c334660cb194324630c51863005e8ba16e2d85a8b41662c8588ae1542a4538a4146288508a013e2784e09913025c4b09512824c4909112023c4708d112220420831042044007f0fc1f43e07b0f41e43c0770ec1d43906f0d61a833866) else (if i<3 then 0x18a312620c398630a610c09802fc5f4be17b2f45e4bc1772ec5ccb91712dc5b4b51692d059cb31652c858caf95e2ba570ad9582ae550a995029a528a39442824fc9f13d2784ec9d13726c4d0999322624b89692c2564a89492824a4909092023e4708d91a23245c8b1132244448810f21c4348610b214424831021fe3f87d8f7 else (if i<4 then 0x307608c097d2f65e4bb5752e65c2b796e2d95acb45652c6586aed5b2b155aaa152aa0536a694aa8e512a1141a804fa9dd39a6e4d099d3225f4b89612aa504909111fa3a4608ad13a254468790d21842682903a064067f8fd9fa3ea7ccf69e53c276ced1d63a6738e49c63866f4de1b73686bcd59a8346688ce99832a640c798d else 0x4969151f2384648b11322043384f06e05bfd7e2f89ea3c8776ebdd0b9570edddb5b666bcd5da6b4a684cf99cb3265cca59131e636c5987b0a)))
def oa (i : Nat) := (oaA (i/93) >>> (11*(i % 93))) &&& 0x7ff
def ovA (i : Nat) := (if i<3 then (if i<1 then 0xb405902c015c0ac05502a014c0a4051028013c09c04d026012c094049024011c08c045022010c08404102000fc07c03d01e00ec07403901c00dc06c03501a00cc06403101800bc05c02d01600ac054029014009c04c025012008c044021010007c03c01d00e006c03401900c005c02c01500a004c0180040018008002000 else (if i<2 then 0x45621510787e83ea1e40e986d835e1a80d086643301970c405e82da1630ac05442a014f0a4051c28c13c09a84b425812b09504a4250127093049424812308d844021e105082040c1f80fb07d03e41f00f707b03bc1dc0ed07603ac1c60d306703041800b2055829013a09c04a023c11c08103e01ec0dc05f02f01740b805b else 0x86642020c905882640f206101c8063f81fa8fc07d83db1eb8f5079a3c71e20f0077a3b61d88eb474e3a21cf8e6872c3901c60e1c7063781bb8dd86d636a1b48d786ba35a1a08cf46503221868c205e62ee16e8b1856a2ae1558aa052a2921438a104fa27713a09c04d426312f09684aa251126092048e23c11d88e847222e)) else (if i<4 then 0x10da85041d20990127f63ef1f20f3877f3af1d74e907363959c3cdf06da3619b08d5669033b197cc8c62a3149844bfc5e12e316d0b4258d2bc15c4adc56a2b39590abe55b2a81534a9054429f14eca6e533296149ca4652028d9458a0a50227f93f09ee4f327713a89ca4e126b13549a44b9259127092c48023c91948c0447 else (if i<5 then 0x210706981e407dfeafe27dc3e75f00f627a3bcb1e16ef076c3b05d40e87737b965c86e1b70037adba4dba6cfb621ae2d5c6a2b4b9a22ceb668b2c190ac68627b0d1834c035f5af5177ebaa5c62dcd6aeb565a0aca9600ae3561aaa5550a8e539a971482a29505a78d3909b14c7259528e92c48ba4091d68d546022a511086e else 0x5926c435d4ac6d556a5b4e5a4fd1428313d19c3cce66032b593548863b31b18b3c4fe1eb0ab)))
def ov (i : Nat) := (ovA (i/78) >>> (13*(i % 78))) &&& 0x1fff
def aValA (i : Nat) := (if i<4 then (if i<2 then (if i<1 then 0x1200000001c48000000000000000000000000000020010100000010100002000c00000000000004000000000100020800500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000 else 0x80000000000000000000000000400000000000000000000010b00000000400200001850002000000600000000c0800c042000a00000000400900000000000080000000000000010000000000000000200060000180000000002000000008800000000000280010004000000400100100000000000000000000000000000000) else (if i<3 then 0x150800881020090b000010412001101c008860004101220018100088110008805000008200000000000000000000012000000000000000008000000000000000000400000000000000000000000000080080018008000400900000090000000000010404000000200000000000000004800000000000000000000000000000 else 0x1002004830018295380050600847a01a781150448605006440020040000a04003061c100000000f0c004000028b120014a0034082042a00b800600701001440608001000600082002c001020c000024d5002e013832e00010260c0803e0008000004920200081060c100020020100080052000d81020800002004000410000)) else (if i<6 then (if i<5 then 0x418589022000c1c3840004580000030702003d4880a01302462c4811000884162400000147810014882000830e0600088020000b0000089200c001000c480001c28a00300803010c02000018000140024800f100a0001026341002e1038604001040000803005008304103800040080040018300146801e50303008c383 else 0x10106000911ea4594008c2a6140c18104004004a3d00d4608a8442342001e51384009038400400802824086003498222003830040080042c808000ca802a04296004008000082830220800065c00c0214d801a1c883001c08400080801e50303008c383004008000005850018682041428000400800c0010304001060c00093) else (if i<7 then 0x16266628b8d3c04b0052750482841912720152878100bb44816a15e749c434085bf00f92c21d0da39370189f011543a0091e8f44cd9170008b252228784045d3240400d9904d608e22b61993e2dc007e9010a1e101174c90100366412d7038e937e69e8b5c01da50465dba084952f082962360001206028784045d3240400d99 else (if i<8 then 0x1202006cc8220b013722f83ae387c02a4cf06b01408c2d64d8029340c51e0808a263e08018000850f0808ba6480801b320882d8448e322b0002f48fc4b764e4a2c2c080283ce4b49062e0288c4d92c4c00e005619418048540c5c2828e724811750be10058d011e90541937c68689769968056e172f7625a947e492807a2411d else 0x50f0808ba6))))
def aVal (i : Nat) := (aValA (i/146) >>> (7*(i % 146))) &&& 0x7f
def vValA (i : Nat) := (if i<28 then (if i<14 then (if i<7 then (if i<3 then (if i<1 then 0x234791e48f2347900000004ad004010041318c7103c01144010040f004010040f00000004000040000001004830040104c631c4011440103c01004010040f000000000000000004000040000051004010040f0040f00400000000000000001000010006304ce132c533b45339c5338453000e739ce73bce70ece70000000000 else (if i<2 then 0x1440014c00004010040100401000032c45314c0014c5314c000008514c0014c0f03c0003c0f03c5303c0f0000f03c0f14c0f03c0003c0f03c01000db16c5b0005b0005b0ac000ac2f3642b14cdf030000ac000ac2b0ac2b0ac000ac00044b3364002f48d00000234eb038e92348d000002348d018710000000079000b3 else 0x1c40034c001c40f11c0f0045100401004011440000400004001c4000040031cc9000002f42f0bc2f0bc2f00400324dd0bcbd0bc2f0bc2f0bc0103c5303c0f0000f03c0f20c0100401004010cc0f03c0003c0f03cbb004111440003c0003c0018c0003cd1000002ccb305c002cc0033cb32ccb3244b30082b3648305cc72dc08)) else (if i<5 then (if i<4 then 0x453394530000038c0014ce714ce114c5314c0414c9314c00334850000032cb72dcb72dcb714c9914c0014c190005314c5314c5314c51004b7004000045300401004002dc51144001445114453144002dc0100400004010040111cd700401000010040100401000712f4710007107471354710ac1304c0004c1304c0007400 else 0x4010040110040004080000f044000000000001000010040100400004010040f0441100000000000040103c0f004010040100401004010040f004010000100401721c800401001c872000720000000000401044010040100401004fc000003f0003f001270000009c0009c0044000000100001000000051004001fc000040f) else (if i<6 then 0xe0400c00110008000010004000000004461000000400100004c000100090000700040004280002c070400b02c088fc0b02c00401004200002406040090240709c090240044010001024110440b72000044bb0440b04400004bb044110000103c1103c000400010000044000000001c000040000400005c8004090040100401 else 0x411004000040104401000010000100001044010040003c010004010040000011004004440000010004000001000000000004401004010040100001000010040103c111004000424100261002c1002e101c81000f100400d840050000043e10000040000040010011100400000100040000401019804c0010040030000043a))) else (if i<10 then (if i<8 then 0xb0441103c01044000005c0009c0001114400000110000103dc802c0f03c0f0040f03c4703c0f03c000049c0000f1500000000000470000f000010000172001024010440100401004010049c27001140000040104401000010000100001000010040103c0100000005ee00400004001440f0061a005cc000010000f00001 else (if i<9 then 0x9c000ac00400000010009c000a00009c0240001c0027070000780809c1e0781a8fe1e078004011c0001d01c270741d0683f0741d0010046a0006c0609c1b06c1a09e1b06c004012709c000530040100000005c8000011f40000001004110040100401004010040f00400270011900900000004007201104400044af00011 else 0x1e09c7209c04400270982700f2407c000010009c0441100000000000040103c0f00401004010040100400004002700f2709c2109c1800000494270001700004400270112709c000010009c270a804c9c2705800001230882709c0000f1500003c002700027000004005f8000009c2900f02c9c2709c2000127050000010009c)) else (if i<12 then (if i<11 then 0x30000000010040100400001f00000000000001f2740110040100400004010040f0040120cb4004110000000400000000040f000010040104c010040000400000000001100401004010040000400004010040f2709c270000049c270010009c0449c2700003c00270010009c1909c270000040000400270010909c1b09c1d09c else 0x72001004000040100411004010040000401000014500000000350fc004010040003c000000f0000100011004010040f005c80000f00401000cc000fc000017500f7200003c000000103c0f03c1103c0103c0103c0103c0f03c0f310003f00003c0040001000000040100400044010000f03dc8004010040103c01004fc3f001) else (if i<13 then 0x3d0f03f0fc0001131000044003f0013f000000fc3f10c04ce838001390fc03c110000000000004000040100401000010040103c013f11003d083f00b3f0003f000004fc30000004003f118000013f0fc00001000fc3f0fc410090000001c003f072000d80a0fc360d81c0fe360d8004013f0fc03c0000000004010007f001f6 else 0x10040103c010040100400044010040f004010000100001004d00040100401004013f0fc3f000004fc3f0013f0fc00011000fc03c003f001000fc350fc3f00000400004003f0010b0fc1d0fc1e8fc360fc720fc044fc3f0f83b00f3f0dc00001000fc000cc00001000fc004fc3f000004003f00003c003f0fc3f0c800001)))) else (if i<21 then (if i<17 then (if i<15 then 0x40000401005fe7200100400721fc001c80000000001004110040100401004017e000024000440011c0011dc80f40f0044711c0011dc8005d811c470000111dc800401000070040100011004010001100001000010000100001000000000003c010040100401000010000102c0103c012b51c004110000000400000000040f else (if i<16 then 0x74000040100400001c8000000000000000721c80440100401000010040103c017200f7200003c000440f03c0f0061c0000f0040f03c0003c0f720017700f0000103c0f4901d0004703c110f4070040772007720010000014c0701c2b01c0001c000042b000c10ad540002b0ac310e4590002b0ac2d0002b0ac000040103c01 else 0xac210048d1e400234001e4791e4b54a0001e47923cb31e479234001e471858791e5e01c445780001c4711c5e01c400000001c4330003b00071000711c4001c4711c4090000007479025c802400004000000f025c8024111c40178047024090f4010240f0740f4b13a6301d000790cc0903c000001d2fc1d02c1d0741d0741d)) else (if i<19 then (if i<18 then 0xac01005c8000110000f000530002b0000103c0172001000000000000400004310ac0100400000310c42b20401001a251001004000c431000310c431000000c53c809c8004010000f72001880010040100001000010040100401000001fc00005c8144110040014c001940000009044000000703c01085c8000030042100021 else 0x2c0f03c0f0840f540005500f5300f5500f5500f0000f00021004030fc51000730f4000ac010f4001c43b07c0101c3903c0f550210042172000000000840f084210040100401500000ac010007f000010ac0119c530ac0000401004011840017c010000100459000010045d00400004010045b0442b00540044014d07d04411) else (if i<20 then 0x40100400005600000000562000000059403c010040100401004011ec0114401000110000002411000390e40100025720050043f000000943d094011f0dc0d0864880f0a40f00c0004c0f0ac0002c3b0003955154551580000f03c0b03c3f0003d03c3d4a80f07c0003c0003c0b0840f03c0f0000f0005303c0f03c0f03c0f else 0x20a00001004000040100401004010040000001004011a40000c63004010040100000004018487f0046b0040d00400000010020e00071000011d40900401004001dc0100401005c800001005c80000000401000010040f00401004010460a004000000000401004000040000000000010040000400044002ada800401005bc))) else (if i<24 then (if i<22 then 0x7200700401005c800011004000e4531440115c01004000040f0ec001540100401004015a000000470240924c0078164005341c409074118282b0240f1e411055c80f409000091c401024090000f01c000040701c2b0000108c517200026435000000001101c070000901c010040104400000030000182801004010020a00401 else (if i<23 then 0x17200102401004010040100401004a50000001c0100000000000000002400004017200100401004010040101c0128c010040100453000010057872001000010000100001004010007d00453004010040100401004010040000000720005207d0040000001004000000000000000090000100401004010040172001 else 0x1c010000000000000000e18c380886300b005240040f0b40b630e6004be63001004010040f0041303c0101c0900001000010040102c0002c11004000040b72000024016300003c110040b02c130040102c1102c2d02c0002c1302c0000588005840058c0058c0058c00000004010040102c0103c0100401004010040100001)) else (if i<26 then (if i<25 then 0x26c0f0040126c0f0040003c0126c0103d94651940040100400005940058a00588005940059400000004010040102c0103c01004010040100401004000840003c000040000000000010040f03c0f6300f03c0b03dc803dc8000010018c00401005904b0010040700401004000000130d82004010040102c79558010040100001 else 0x1650016380163001720017200000001004010040b0040f004010040100401005940040100401004010000901c0100001005c80040100001004011c401004010000f00400004010000026c000000000401001940440172001004010000f004010000100400000b8238ea00401004010001303c010000b0240001c8c3a001) else (if i<27 then 0x72009184090000f074090040011c01004097a071024010241302409000090f4007902704c1304c0004c3104c1304c1304c131ac1304c0004c130000004c13790000c40004dc804c13004000000f000110041303c00005e403c0004c130041304dc804dc8720000041100401004000000103c01004010040100401005c800001 else 0x3da02c9a00f4000ac90680f20cc0003c0f03c0b0cc0304c0003c0f03c3303c0b0003303c390003c680ec6800f03c0f02c0f0000f0005303c0f03c0f03c0f02c0f03c0f0840f670006800f6800f6800f5300f0000f00013000000000102c0b0440b720330cc000047103c0f6800b03c0004c1902c290040002c0b02c3d0f411))))) else (if i<42 then (if i<35 then (if i<31 then (if i<29 then 0x446f0001972000024010000103c1900019000190000103c1104c1902c01064190240972009074000240003c00044000008f0041d0000929c0178027024710043d02413024a90440004411024a70002f0002f0006b0447b04400044710441104400001c8720110040100411000010000103c01004010040100401004010a400 else (if i<30 then 0x440102c000440004400720a300009004000000103c11000007200003c130041128c11004110441100400004010040000411005c80040100400004c500400000010040b0441100411004007200003c1104c11000117201102401044111ac001ade41a4007206d04c0119c0002411074000040103c0100000045b003c0104411 else 0x4317200100411044000ac0104400004000000072001004010040100400510010040900407004010040129401005a208407044115581100401000000d5c80440f000630004104411044010041104400044110440104409001c803c0b000110440103c110440b00411044010001100411024130241103c01044000440000011)) else (if i<33 then (if i<32 then 0x829c803c0100000004010040100001005bc00401250f41389a3e9bc6f1bc004010040100011224010008b0240001c00818010448900401044890040022401224016f1bc0041100401004000000000079001bc000010059e6f00100401000010040104407549bc00401004000000104400044110003509411005a21041104400 else 0x401689c80040100400004010041101d5672001004010000000401024000440f1c5bc034110c40082803005a8044ab1ec0004400000110440902c1102cab000001ac01000110440072001004010040900407004010040100401005bc1c4000000100001001c800000000010000004489000000040000000000010000000401) else (if i<34 then 0x7200f03c11044110440104409001c803c0b000110440103c110440b0041104401000011440f0640003c0003dc803c0f01c0f0040f0000f0000f0000f0000000401720000441100400004010040f03c010000100401004010041104411004110d4007200f10400044110040f0441110401044110440000000000001e4006f000 else 0x441100400720007207b000000000002c010440b044011ac0f001c80040f044110441100411024117200f1fc00004000040000011000000040100401004010440100001004010000170001698017200172001720000000100401004110040f004010040100401004217200f004010000003c00000000000f000010040f03c0f))) else (if i<38 then (if i<36 then 0x17200172001000010000100411004010040f004010040000040278fe00401004010001303c010000b0240001c9c3f0010440f004010440f0040003c010440103dc8721c80040100400005c4005c8005c80055e005c80000000401004010440103c0100401004010040100411004110441110401094010441104411 else (if i<37 then 0x3de002411004091c49724c95000710f43b00000074000008f24401000090240f02409720090000f01c1501c0701c00025c801c510040126407004070003903c0703c7701c0f0a5c800401004000041103c00004010000000400004012e401004012dc0003c11000000040f0000000000004000000100401720510040100001 else 0x346b03c0f0000009c0104c010ac0f00013000290041303c0f0000f03dc803c00005c8005ae005ac005c8005c80000000401004010440103c010040100401004010040100401004000240100400004077200000401004010040000401720711f40f72001004010002900451004010047f000110045300401004000040902409)) else (if i<40 then (if i<39 then 0x44415d97400411045c80001103c0f0016c18c01000000000f000000000103dc803c0f03c017200f085c803c1103c0f6d80f00001720016e801720015c801720000000100401004110040f0040100401004010047102c0003c017200103c111ec0172011044110440002400004001ac1104411000110440f03c0f7900304401 else 0x114a7780711c400000711c471074001c4710003b114062990a0003b1c4a11c53a1c4490bc000cc710009d281040ec7127c711c43b0ec710009d1c4711c5e0781e08587111c330000172001720017200172001720000000100401004110040f004010040100401004110000009400000000001100401721c8004110441104411) else (if i<41 then 0x2c4d00007822080041114c010041114c0114c5300560004110061083001004011ac6b1c4136c86b18c00001640014000085508831ac00000001adb021d661ac6b04c6b790004f800001e42a1e42a9e44313c0006b04c00034131ac337910e1ac6b0002704c1303c130c41304c2708c270001309c1304c131acbd1c4001c400 else 0x440722084044010040f0040f0040120034e00010042c0f86a1504a1d8001d0200001a0bb7c1a0280c03a1f04c1b84e1c0001703c160601c8220e0481b04416818158781e032200000008514c5300d6a00053006080005314c53000215600014c5314cb114c5300000000444420882208120ae4680104453006040040100400)))) else (if i<49 then (if i<45 then (if i<43 then 0x4400002b0004fc0040103c0c02d28004a8004cc004010055403cb8044000040f0440003ca00053800401007b403cb001eb6004c24b0010040000066148000300000000000000781c00036047b41905022886232aeab0802000f000281082610024c8800c80010040104c01004090040f004110040100400004010000f0040b else (if i<44 then 0x6e18e03001004000040103d8404de8005ac03d880056c00600004010072e03d7401fb4004d66e00103c2c371403c10052000490ac000a43137c460bc0d0d4540ec510f848000430d03d114530b4320e4470e04209c4113c4f0c04b00001134000e800000001300c12c4b0d84b31e045104b158004000272400784044bc4b011 else 0x8b22c0562c1100708e248883901f328c8398c22cdf22c01c398b03c641f4691c47f0007b178001703437c771881018c821a07e1c079000740de6a1d8811803699c7819873168721f07c0cc6e000020006f1940e1b8045b86e2aa0060c02728004c86e1b0004110040000401e20110040f7501100000ae0016d0010040f5f00b)) else (if i<47 then (if i<46 then 0xec09c7000b32400000912c0902449024000d40900047902400ec4d024090ec2f0ec1d02400024000244f02409024270ec279100902415114099023c9200902400000008800001c000000701d940001500330df0078b0008b00765839000398a039084070001501eaa3880701c078b03905445e300708ea88a8073800787007 else 0xa200b3b001a22580025cdf37c1325c3ea5c000e89721a00400006600ae6c000010002fce001e5025004000b42d8a264aa0018f8010042b9702d970018880167001004019a02b95031000010ac2b0002b970010000100401c782b8d023b2801971ae00401ee2403fa1612198df0e46ca38d5b7c9324090240aa220e400911634) else (if i<48 then 0x240101c01df023aa2a808409d98070000102688004270840101e400062c006a80040000401004010000040a88014000000d00762890050068800612004038e29000f7c0000100400d3009f280500c50004016d800a20030028800401a228ca00019529800403b7a8800007016a868001a2380a1001df2880000100001a5001 else 0xb0000da37cdab7c00000002d8002e0592e0172e0006e0b1aaa03c0003d0e03f9cb12a8000010010cb82be03e3000400b81bc00400b400b006bc0040102c0f04c090000101c0102c010042db080bb8001b80010040100001000018cae06f80103c0000401151a4094000041d002a800398419ba9700100750df2e0aa2a8aa0f0))) else (if i<52 then (if i<50 then 0x4429004010a4000a40100401044010041100401df00b0040100407df304c1001006ec44af00000000258cd31e8db1c58000181c00001309f7c0037cba000ba000cdae8ba2e8441c204c130341304fa00cef204c23b901304c270441304c13f002704c1104c1304c3104c2704ee80441304c1309c110441396ae88d01104ed4 else (if i<51 then 0x480010000097b500031cd93a4df1deba0684b800c731c044050001102c1102c00044090440006c09044110b774c100002c110541104419c701105c09c724004411c700b461c80441100000c3304c1000dcb5ce0000c22e41915ec7304a101100656d2304004298e12a76800001147100100401000010a70404409004010a704 else 0xa40f03c0f03c370440f03c0f0840f0442b03c0f03c0b0442100364d900f03f1c01c000040000400005d0000000000000750d400004400be800df001ea350bf81f00750f381704400d400100672d4001005ea007789da48006a800000007509334004768003500647001f3c07401c0807d409604401d10019e809df0014d811)) else (if i<54 then (if i<53 then 0x9fb78bc36c000907b3744e1ee1f13a04411014000441100011094000ef74044110641104441044110f400044410b774dd0110441b0fc1104425ec0170f44104439df2f2000110440000000df000c7364de80000364d93641d132003649400f046aada266eb124752f60009a79b64d626e03c1100c0004c0f0840f084000d40f else 0xe0380e9a8ae60807d306e9288000010040f5081100400025407d801004010041303f8003f7c00401044010040f0040b0040704780e0001004787c380aab04e6800dd25c002404f1f2c7aa8201b8e9a8ae62e8d4800d913eb8306e92884ba42d9a5ed422cc737cdf12c6e800000000001104774dd374c737ac7b749f374) else (if i<55 then 0x47a4024110441104411000110541b000110440b0000b000110441100000df00000000e6310e7316ea2a8e03aea7b98e63bca300101c1653800211fc00398522020040100698004070003f004000240102401004010040109c3fdf02100001004070040102401024430041d00407e6398e6001004000000000380c139a00000 else 0x504c0a83414800110200001c030160e8280101015826140300f8001000e0b036150240281e108220f0180e0481200804b7cc7000a9800f1000e0000eb000c200004ba4543a4df2a0ec31a55ba80029202c000466ae9204027a4e920a047bc04409027ce9800004488e90110440bc30050640b05c09))))))
def vVal (i : Nat) := (vValA (i/102) >>> (10*(i % 102))) &&& 0x3ff
def act (s i t : Nat) : Nat :=
  let j := off s+i
  let p := oa j
  let q := ov j
  let a := oa (j+1)-p
  let b := ov (j+1)-q
  vVal (q + ((t/a + aVal (p + t % a))%b))
def opTab (i : Nat) := (if i<1 then ([(6,0x7f),(13,0x3f80),(20,0x1fc000),(43,0xc0000000000),(45,0x300000000000),(47,0xc00000000000),(49,0x3000000000000),(51,0xc000000000000),(52,0x10000000000000),(54,0x6000000fe00000),(55,0x80000000000000),(57,0x3000007f0000000),(59,0xc0003f800000000),(102,0x40810204081000000000000000),(104,0x101020408102000000000000000),(106,0x482040810204000000000000000),(107,0xa04081020408000000000000000),(110,0x5008102040810000000000000000),(112,0x18010204081020000000000000000),(113,0x20000000000000000000000000000),(115,0x82020408102040000000000000000),(116,0x100000000000000000000000000000),(118,0x440000000000000000000000000000),(119,0xa00000000000000000000000000000)] : List (Nat × Nat)) else ([(6,0x7f),(13,0x1fc000),(20,0x3f80),(43,0x300000000000),(45,0xc0000000000),(47,0xc00000000000),(49,0xc000000000000),(51,0x3000000000000),(52,0x80000000000000),(54,0x3000007f0000000),(55,0x10000000000000),(57,0x6000000fe00000),(59,0xc0003f800000000),(102,0x101020408102000000000000000),(104,0x40810204081000000000000000),(106,0xa04081020408000000000000000),(107,0x482040810204000000000000000),(110,0x5008102040810000000000000000),(112,0x82020408102040000000000000000),(113,0x100000000000000000000000000000),(115,0x18010204081020000000000000000),(116,0x20000000000000000000000000000),(118,0xa00000000000000000000000000000),(119,0x440000000000000000000000000000)] : List (Nat × Nat)))
def rot (g : Nat) (w : List Nat) := if g = 0 then w else w.map (spr (opTab (g % 2)))
theorem rokok (g : Nat) {s ws} (h : NatRun (mask 60) (goal 60) s ws) :
    NatRun (mask 60) (goal 60) s (rot g ws) := by
  unfold rot
  split
  · exact h
  · apply sprRun h
    exact (by decide +kernel : ∀ j : Fin 2, sprOK (opTab j) (mask 60) (goal 60) = true) ⟨_,Nat.mod_lt _ (by decide)⟩
def tickA (i : Nat) := (if i<3 then (if i<1 then 0x34330186e19870342d018681986b343b050731a07018140d8761b868ac0d0ec6b1d866d80d0ec771d866ac0d0ec701d866342f0d8761c06b180d0e4701d066ac0d0ec771d866180d0e4771d066180d0e4701a066182d0346b1986818140d8761c468ac14018681986aac0d0ec771a866180d0e4771a066182b0506a1a066 else (if i<2 then 0x18140d8761c06850310186e1a073503b0e4771d06aac2f0346b1986a50390ec771d868502d0ec771d868502d0ec771cc68502f0e4771cc6ad8390ec771d86e342f0d8761c46b18140d8731b868180d0e4701b8661831050731a06e1833034701986e180d0e4771b866180d0e46b1d06618140d8731c468b42f0506a1a06b else 0xac0d0ec701cc66ac0d0ec701a86650060d8711d868342d0186a1986b180d0e4701cc6650060d8771d868502b0186b1a06ae42f0506a1a06b182f0506a1a06b502f0186b1a06acc340506a1a066b42f0506a1a066180d0e4771cc6618360506a1a06618140d86a1c46818140d87619868343b0d8761c46bc4330ec701cc6e)) else (if i<5 then (if i<4 then 0x182b0506a1ac66ac0d0506b1a86618390346b19868180d0e46b1a0661831050731a066182d0347719868182b050761a06634060e46e1c066182b0506a1b866ac0d0ec771cc66d80d0ec6b1cc66ac060506b1a866ac14018681c06ae4340506a1a070b40d0186a1a06b18140d8731c068c4330ec771d866ac2d0ec771d866 else 0xac0d0bc6b1a866502f0e4771cc6634060e4741c066182b0506a1d06618310506a1a066182b050731a066182d0346b1b868182f0506a1a066180d0cc701b866502d0ec6b1cc68343b0d8731c06b342f0d8731c06bac0d0ec6b1a866ac14018731986a18140d86a1c068502d0ec6b1d86818140d87319868343b0d8761c06b) else (if i<6 then 0xd80d0ec771cc7150060d86e1cc681836050761ac71ac2d0346b1986ad80d0ec6b1d8661836050731a0661836050761a0661836050761a06ec406050681cc6e180d0b46b1a06634140d8761c468180d0506b1a06634140d8761b8681836050761a071ac06050681a86618360506a1b866d80d0ec771cc66ac140186b1986a else 0x503b0e4771a06a5039034771a87434140d8731c06b342b0506a1ac66503b0e4771cc6a503b034771a8743439018731a877500d0e4771d06a500d0e4771b8661831050761a06e180d0e4701b86bac0d050681cc66)))
def tick (i : Nat) := (tickA (i/18) >>> (56*(i % 18))) &&& 0xffffffffffffff
def Z := scorebarrier 60 2 state ct act tick rot
theorem h0_0 : span (Z 0) 1 0 = true := by decide +kernel
theorem z0 : span (Z 0) 1 0 = true := h0_0
theorem h1_0 : span (Z 1) 1 0 = true := by decide +kernel
theorem z1 : span (Z 1) 1 0 = true := h1_0
theorem h2_0 : span (Z 2) 1 0 = true := by decide +kernel
theorem z2 : span (Z 2) 1 0 = true := h2_0
theorem h3_0 : span (Z 3) 1 0 = true := by decide +kernel
theorem z3 : span (Z 3) 1 0 = true := h3_0
theorem h4_0 : span (Z 4) 4 0 = true := by decide +kernel
theorem z4 : span (Z 4) 4 0 = true := h4_0
theorem h5_0 : span (Z 5) 12 0 = true := by decide +kernel
theorem h5_12 : span (Z 5) 12 12 = true := by decide +kernel
theorem h5_24 : span (Z 5) 12 24 = true := by decide +kernel
theorem h5_36 : span (Z 5) 12 36 = true := by decide +kernel
theorem h5_48 : span (Z 5) 12 48 = true := by decide +kernel
theorem h5_60 : span (Z 5) 12 60 = true := by decide +kernel
theorem h5_72 : span (Z 5) 12 72 = true := by decide +kernel
theorem h5_84 : span (Z 5) 12 84 = true := by decide +kernel
theorem h5_96 : span (Z 5) 12 96 = true := by decide +kernel
theorem h5_108 : span (Z 5) 12 108 = true := by decide +kernel
theorem h5_120 : span (Z 5) 12 120 = true := by decide +kernel
theorem h5_132 : span (Z 5) 5 132 = true := by decide +kernel
theorem z5 : span (Z 5) 137 0 = true := (@span_join (Z 5) 96 0 41 (@span_join (Z 5) 48 0 48 (@span_join (Z 5) 24 0 24 (@span_join (Z 5) 12 0 12 h5_0 h5_12) (@span_join (Z 5) 12 24 12 h5_24 h5_36)) (@span_join (Z 5) 24 48 24 (@span_join (Z 5) 12 48 12 h5_48 h5_60) (@span_join (Z 5) 12 72 12 h5_72 h5_84))) (@span_join (Z 5) 24 96 17 (@span_join (Z 5) 12 96 12 h5_96 h5_108) (@span_join (Z 5) 12 120 5 h5_120 h5_132)))
theorem h6_0 : span (Z 6) 12 0 = true := by decide +kernel
theorem h6_12 : span (Z 6) 12 12 = true := by decide +kernel
theorem h6_24 : span (Z 6) 12 24 = true := by decide +kernel
theorem h6_36 : span (Z 6) 12 36 = true := by decide +kernel
theorem h6_48 : span (Z 6) 12 48 = true := by decide +kernel
theorem h6_60 : span (Z 6) 12 60 = true := by decide +kernel
theorem h6_72 : span (Z 6) 12 72 = true := by decide +kernel
theorem h6_84 : span (Z 6) 12 84 = true := by decide +kernel
theorem h6_96 : span (Z 6) 12 96 = true := by decide +kernel
theorem h6_108 : span (Z 6) 12 108 = true := by decide +kernel
theorem h6_120 : span (Z 6) 12 120 = true := by decide +kernel
theorem h6_132 : span (Z 6) 12 132 = true := by decide +kernel
theorem h6_144 : span (Z 6) 12 144 = true := by decide +kernel
theorem h6_156 : span (Z 6) 12 156 = true := by decide +kernel
theorem h6_168 : span (Z 6) 12 168 = true := by decide +kernel
theorem h6_180 : span (Z 6) 12 180 = true := by decide +kernel
theorem h6_192 : span (Z 6) 12 192 = true := by decide +kernel
theorem h6_204 : span (Z 6) 12 204 = true := by decide +kernel
theorem h6_216 : span (Z 6) 12 216 = true := by decide +kernel
theorem h6_228 : span (Z 6) 12 228 = true := by decide +kernel
theorem h6_240 : span (Z 6) 4 240 = true := by decide +kernel
theorem z6 : span (Z 6) 244 0 = true := (@span_join (Z 6) 192 0 52 (@span_join (Z 6) 96 0 96 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 12 0 12 h6_0 h6_12) (@span_join (Z 6) 12 24 12 h6_24 h6_36)) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 12 48 12 h6_48 h6_60) (@span_join (Z 6) 12 72 12 h6_72 h6_84))) (@span_join (Z 6) 48 96 48 (@span_join (Z 6) 24 96 24 (@span_join (Z 6) 12 96 12 h6_96 h6_108) (@span_join (Z 6) 12 120 12 h6_120 h6_132)) (@span_join (Z 6) 24 144 24 (@span_join (Z 6) 12 144 12 h6_144 h6_156) (@span_join (Z 6) 12 168 12 h6_168 h6_180)))) (@span_join (Z 6) 48 192 4 (@span_join (Z 6) 24 192 24 (@span_join (Z 6) 12 192 12 h6_192 h6_204) (@span_join (Z 6) 12 216 12 h6_216 h6_228)) h6_240))
theorem h7_0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7_12 : span (Z 7) 10 12 = true := by decide +kernel
theorem z7 : span (Z 7) 22 0 = true := (@span_join (Z 7) 12 0 10 h7_0 h7_12)
theorem h8_0 : span (Z 8) 1 0 = true := by decide +kernel
theorem z8 : span (Z 8) 1 0 = true := h8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < ct s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
def rs : List Nat := [3, 3, 3, 3, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 9, 9, 9, 9, 9, 9, 9, 21, 21, 21, 21, 21, 21, 21, 26, 26, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 5, 5, 10, 10, 12, 12, 17, 17, 18, 18, 20, 21, 21, 24, 26, 26, 28, 28, 7, 11, 13, 14, 19, 22, 25, 7, 11, 13, 14, 19, 22, 25, 7, 11, 13, 14, 19, 22, 25, 7, 11, 13, 14, 19, 22, 25, 7, 11, 13, 14, 19, 22, 25, 7, 11, 13, 14, 19, 22, 25, 7, 13, 11, 14, 13, 14, 19, 25, 19, 22, 22, 23, 29, 25, 27, 30, 29, 30]
def xs : List Nat := [0x5e75ebd7af5ebd70630c000fffc07f,0xb3db5dbb76eddbb30c3007f0003fff,0xe78ed6ad5ab56adc70cff80fe03f80,0xfc2fa74e9d3a74ef80f3fff01fc000,0xfff03870e1c3870fff03ffffe00000]
end ceac8e880
open ceac8e880 in
theorem lower_eac8e880 : bound 0xeac8e880 9 := by
  apply mkBound 0xeac8e880 8 60 rs xs (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro s hs h
  have hh : NatRun (mask 60) (goal 60) 8 xs := extend_run h hs
  have hp : xs.Perm (state 8 0) := by decide +kernel
  exact scorebarrier_all rokok checked 8 (by decide) 0 (by decide) (Run.perm hp hh)
end PQ1425Lower

namespace PQ1425Upper

open PEqualNP.CircuitLowerBounds

abbrev FanIn (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

abbrev OneNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j

abbrev HasNot (gs : List Gate) : Prop :=
  ∃ g ∈ gs, g.op = GateOp.not

abbrev Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

abbrev Evaluates (T : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∀ x : Fin 5 → Bool,
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

abbrev LowerBound (T m : ℕ) : Prop :=
  ∀ (gs : List Gate) (o : ℕ), FanIn gs → OneNot gs → Evaluates T gs o →
    HasNot gs → m ≤ gs.length

abbrev Witness (T m : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), Mono gs ∧ gs.length ≤ m ∧ Evaluates T gs o

private theorem allRows (P : (Fin 5 → Bool) → Prop)
    (h : ∀ a b c d e : Bool, P ![a, b, c, d, e]) : ∀ x, P x := by
  intro x
  have E : ![x 0, x 1, x 2, x 3, x 4] = x := by
    funext i
    fin_cases i <;> rfl
  exact E ▸ h (x 0) (x 1) (x 2) (x 3) (x 4)

private theorem finish {T m : ℕ} (lb : LowerBound T m) (w : Witness T m)
    (gs : List Gate) (o : ℕ) (hOk : FanIn gs)
    (hOne : OneNot gs) (hEval : Evaluates T gs o) : Witness T gs.length := by
  classical
  by_cases hn : HasNot gs
  · obtain ⟨us, p, hu, hlen, hev⟩ := w
    exact ⟨us, p, hu, hlen.trans (lb gs o hOk hOne hEval hn), hev⟩
  · refine ⟨gs, o, ?_, Nat.le_refl _, hEval⟩
    intro g hg
    obtain ⟨hop, harity⟩ := hOk g hg
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun hn' => hn ⟨g, hg, hn'⟩)),
      harity⟩

private def gates_e8a8a8a8 : List Gate :=
  [⟨.and, [0, 1]⟩,
   ⟨.and, [3, 4]⟩,
   ⟨.and, [1, 6]⟩,
   ⟨.or, [0, 7]⟩,
   ⟨.and, [2, 8]⟩,
   ⟨.or, [5, 9]⟩]

theorem upper_e8a8a8a8 : Witness 0xe8a8a8a8 6 := by
  refine ⟨gates_e8a8a8a8, 10, ?_, by decide, ?_⟩
  · simp [gates_e8a8a8a8, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_e8a8e888 : List Gate :=
  [⟨.and, [0, 1]⟩,
   ⟨.or, [0, 1]⟩,
   ⟨.and, [0, 4]⟩,
   ⟨.or, [3, 7]⟩,
   ⟨.and, [6, 8]⟩,
   ⟨.and, [2, 9]⟩,
   ⟨.or, [5, 10]⟩]

theorem upper_e8a8e888 : Witness 0xe8a8e888 7 := by
  refine ⟨gates_e8a8e888, 11, ?_, by decide, ?_⟩
  · simp [gates_e8a8e888, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_e8e8e880 : List Gate :=
  [⟨.or, [0, 1]⟩,
   ⟨.and, [0, 1]⟩,
   ⟨.and, [2, 6]⟩,
   ⟨.or, [2, 6]⟩,
   ⟨.or, [3, 4]⟩,
   ⟨.and, [8, 9]⟩,
   ⟨.or, [7, 10]⟩,
   ⟨.and, [5, 11]⟩]

theorem upper_e8e8e880 : Witness 0xe8e8e880 8 := by
  refine ⟨gates_e8e8e880, 12, ?_, by decide, ?_⟩
  · simp [gates_e8e8e880, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eaa8a888 : List Gate :=
  [⟨.and, [1, 2]⟩,
   ⟨.or, [0, 5]⟩,
   ⟨.and, [3, 4]⟩,
   ⟨.or, [3, 4]⟩,
   ⟨.and, [2, 8]⟩,
   ⟨.or, [1, 9]⟩,
   ⟨.and, [0, 10]⟩,
   ⟨.or, [7, 11]⟩,
   ⟨.and, [6, 12]⟩]

theorem upper_eaa8a888 : Witness 0xeaa8a888 9 := by
  refine ⟨gates_eaa8a888, 13, ?_, by decide, ?_⟩
  · simp [gates_eaa8a888, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eaa8c888 : List Gate :=
  [⟨.and, [2, 3]⟩,
   ⟨.or, [0, 5]⟩,
   ⟨.or, [2, 3]⟩,
   ⟨.and, [4, 7]⟩,
   ⟨.and, [0, 8]⟩,
   ⟨.or, [1, 9]⟩,
   ⟨.and, [6, 10]⟩]

theorem upper_eaa8c888 : Witness 0xeaa8c888 7 := by
  refine ⟨gates_eaa8c888, 11, ?_, by decide, ?_⟩
  · simp [gates_eaa8c888, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eaa8e880 : List Gate :=
  [⟨.or, [1, 2]⟩,
   ⟨.and, [0, 5]⟩,
   ⟨.or, [3, 6]⟩,
   ⟨.and, [1, 2]⟩,
   ⟨.and, [3, 5]⟩,
   ⟨.or, [4, 9]⟩,
   ⟨.and, [0, 10]⟩,
   ⟨.or, [8, 11]⟩,
   ⟨.and, [7, 12]⟩]

theorem upper_eaa8e880 : Witness 0xeaa8e880 9 := by
  refine ⟨gates_eaa8e880, 13, ?_, by decide, ?_⟩
  · simp [gates_eaa8e880, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eaaac880 : List Gate :=
  [⟨.or, [0, 2]⟩,
   ⟨.and, [0, 4]⟩,
   ⟨.and, [0, 2]⟩,
   ⟨.or, [3, 7]⟩,
   ⟨.and, [1, 8]⟩,
   ⟨.or, [6, 9]⟩,
   ⟨.and, [5, 10]⟩]

theorem upper_eaaac880 : Witness 0xeaaac880 7 := by
  refine ⟨gates_eaaac880, 11, ?_, by decide, ?_⟩
  · simp [gates_eaaac880, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eac0e8c0 : List Gate :=
  [⟨.and, [1, 2]⟩,
   ⟨.or, [2, 4]⟩,
   ⟨.or, [1, 6]⟩,
   ⟨.and, [3, 7]⟩,
   ⟨.and, [0, 8]⟩,
   ⟨.or, [5, 9]⟩]

theorem upper_eac0e8c0 : Witness 0xeac0e8c0 6 := by
  refine ⟨gates_eac0e8c0, 10, ?_, by decide, ?_⟩
  · simp [gates_eac0e8c0, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eac8e0c0 : List Gate :=
  [⟨.and, [0, 3]⟩,
   ⟨.or, [1, 5]⟩,
   ⟨.and, [0, 4]⟩,
   ⟨.or, [2, 7]⟩,
   ⟨.and, [6, 8]⟩]

theorem upper_eac8e0c0 : Witness 0xeac8e0c0 5 := by
  refine ⟨gates_eac8e0c0, 9, ?_, by decide, ?_⟩
  · simp [gates_eac8e0c0, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private def gates_eac8e880 : List Gate :=
  [⟨.or, [0, 2]⟩,
   ⟨.and, [1, 3]⟩,
   ⟨.and, [0, 3]⟩,
   ⟨.or, [1, 7]⟩,
   ⟨.and, [0, 2]⟩,
   ⟨.or, [4, 9]⟩,
   ⟨.and, [8, 10]⟩,
   ⟨.or, [6, 11]⟩,
   ⟨.and, [5, 12]⟩]

theorem upper_eac8e880 : Witness 0xeac8e880 9 := by
  refine ⟨gates_eac8e880, 13, ?_, by decide, ?_⟩
  · simp [gates_eac8e880, List.forall_mem_cons]
  · apply allRows
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

/-- Supply lower bounds only for lists containing a NOT. Already monotone lists
are returned unchanged. -/
theorem wrap
    (lb_e8a8a8a8 : LowerBound 0xe8a8a8a8 6)
    (lb_e8a8e888 : LowerBound 0xe8a8e888 7)
    (lb_e8e8e880 : LowerBound 0xe8e8e880 8)
    (lb_eaa8a888 : LowerBound 0xeaa8a888 9)
    (lb_eaa8c888 : LowerBound 0xeaa8c888 7)
    (lb_eaa8e880 : LowerBound 0xeaa8e880 9)
    (lb_eaaac880 : LowerBound 0xeaaac880 7)
    (lb_eac0e8c0 : LowerBound 0xeac0e8c0 6)
    (lb_eac8e0c0 : LowerBound 0xeac8e0c0 5)
    (lb_eac8e880 : LowerBound 0xeac8e880 9) :
    ∀ T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset ℕ),
      ∀ (gs : List Gate) (o : ℕ), FanIn gs → OneNot gs → Evaluates T gs o →
        Witness T gs.length := by
  intro T hT gs o hOk hOne hEval
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact finish lb_e8a8a8a8 upper_e8a8a8a8 gs o hOk hOne hEval
  · exact finish lb_e8a8e888 upper_e8a8e888 gs o hOk hOne hEval
  · exact finish lb_e8e8e880 upper_e8e8e880 gs o hOk hOne hEval
  · exact finish lb_eaa8a888 upper_eaa8a888 gs o hOk hOne hEval
  · exact finish lb_eaa8c888 upper_eaa8c888 gs o hOk hOne hEval
  · exact finish lb_eaa8e880 upper_eaa8e880 gs o hOk hOne hEval
  · exact finish lb_eaaac880 upper_eaaac880 gs o hOk hOne hEval
  · exact finish lb_eac0e8c0 upper_eac0e8c0 gs o hOk hOne hEval
  · exact finish lb_eac8e0c0 upper_eac8e0c0 gs o hOk hOne hEval
  · exact finish lb_eac8e880 upper_eac8e880 gs o hOk hOne hEval

end PQ1425Upper

end PEqualNP.Outside.L_meta_1425

open PEqualNP.Outside.L_meta_1425 in
theorem PEqualNP.Outside.L_meta_1425 : ∀ T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PQ1425Upper.wrap
    PQ1425Lower.lower_e8a8a8a8
    PQ1425Lower.lower_e8a8e888
    PQ1425Lower.lower_e8e8e880
    PQ1425Lower.lower_eaa8a888
    PQ1425Lower.lower_eaa8c888
    PQ1425Lower.lower_eaa8e880
    PQ1425Lower.lower_eaaac880
    PQ1425Lower.lower_eac0e8c0
    PQ1425Lower.lower_eac8e0c0
    PQ1425Lower.lower_eac8e880
