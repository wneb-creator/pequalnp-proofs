import Mathlib
import PEqualNP.Defs

-- The circuit machinery and the small-graph lower bounds are copied from the merged file
-- lean/PEqualNP/Outside/L_meta_927.lean of this repository (L-meta-927, pull request 1992, by sanchan),
-- with the namespace renamed; only the final relabelling for L-meta-4795 is new.

namespace PEqualNP.Outside.L_meta_4795_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
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

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
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

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
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

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
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
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
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
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
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

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
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

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
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

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
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

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
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

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
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
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
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

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
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

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
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

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
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

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
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

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
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

/-! Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

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

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

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
  induction h using Run.fold with
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

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
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
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
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
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

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
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
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
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

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
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
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
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

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
  induction h using Run.fold with
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
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
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
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

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
  induction h using Run.fold with
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
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
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
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

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
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 18 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 10 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)

/-! Section 3: Verified barrier certificates for the 7 base cases -/

-- Base case K3 (n=3, cap=3, k=9, states=1, pool=1)
def f_K3 : BFn 3 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
def rows_K3 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 3, 5, 6, 3, 5, 6, 3, 5, 6]
def xs_K3 : List ℕ := [0x1b607, 0x2da38, 0x36dc0]
def pool_K3 : List ℕ := [0xc000180b02809]
def NN_K3 : ℕ → ℕ
  | 3 => 1
  | _ => 0
def HT_K3 : ℕ → ℕ
  | 3 => 0xc03a13c3
  | _ => 0
def PT_K3 : ℕ → ℕ
  | _ => 0
def Z_K3 (s : ℕ) := bar 9 (Sgen 9 3 xs_K3 PT_K3) NN_K3 (idxGen NN_K3 HT_K3) id pool_K3 s
theorem z_K3_0 : span (Z_K3 0) 0 0 = true := rfl
theorem z_K3_1 : span (Z_K3 1) 0 0 = true := rfl
theorem z_K3_2 : span (Z_K3 2) 0 0 = true := rfl
theorem h_K3_3_0 : span (Z_K3 3) 1 0 = true := by decide +kernel
theorem z_K3_3 : span (Z_K3 3) 1 0 = true := h_K3_3_0
theorem base_K3 : ∀ s : ℕ, HasCircuitSize 3 f_K3 s → 4 ≤ s := by
  refine prove_base 3 9 3 f_K3 rows_K3 xs_K3 pool_K3 NN_K3 HT_K3 PT_K3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_K3_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3_3 i (Nat.zero_le i) hi
    )

-- Base case C5 (n=5, cap=6, k=50, states=7, pool=5)
def f_C5 : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)
def rows_C5 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 3, 5, 3, 10, 5, 20, 3, 5, 7, 10, 14, 20, 22, 24, 10, 24, 3, 5, 10, 11, 13, 20, 24, 25, 3, 5, 10, 13, 14, 20, 24, 28, 20, 24, 3, 5, 10, 19, 20, 21, 24, 25, 3, 5, 10, 19, 20, 22, 24, 26]
def xs_C5 : List ℕ := [0xbab02e6c075c03fc00ff0003, 0xad0d054355d37fc0000003fcc, 0x32326e8c876c80000ff003ff0, 0xc4c4b737398200000ffffc000, 0xf8f8f8382e083ffff00000000]
def pool_C5 : List ℕ := [0x18000a8370c833, 0x38020883f0c835, 0x80040403f0cc37, 0x800060350cc32, 0x800e018370d43f]
def NN_C5 : ℕ → ℕ
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT_C5 : ℕ → ℕ
  | 5 => 0xc6e3b2e569d2916d684aef2d399569702839ea7a276164fc
  | 6 => 0x2839ea7a
  | _ => 0
def PT_C5 : ℕ → ℕ
  | 5 => 0x40c0104004040100000000102
  | _ => 0
def Z_C5 (s : ℕ) := bar 50 (Sgen 50 6 xs_C5 PT_C5) NN_C5 (idxGen NN_C5 HT_C5) id pool_C5 s
theorem z_C5_0 : span (Z_C5 0) 0 0 = true := rfl
theorem z_C5_1 : span (Z_C5 1) 0 0 = true := rfl
theorem z_C5_2 : span (Z_C5 2) 0 0 = true := rfl
theorem z_C5_3 : span (Z_C5 3) 0 0 = true := rfl
theorem z_C5_4 : span (Z_C5 4) 0 0 = true := rfl
theorem h_C5_5_0 : span (Z_C5 5) 6 0 = true := by decide +kernel
theorem z_C5_5 : span (Z_C5 5) 6 0 = true := h_C5_5_0
theorem h_C5_6_0 : span (Z_C5 6) 1 0 = true := by decide +kernel
theorem z_C5_6 : span (Z_C5 6) 1 0 = true := h_C5_6_0
theorem base_C5 : ∀ s : ℕ, HasCircuitSize 5 f_C5 s → 7 ≤ s := by
  refine prove_base 5 50 6 f_C5 rows_C5 xs_C5 pool_C5 NN_C5 HT_C5 PT_C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C5_6 i (Nat.zero_le i) hi
    )

-- Base case BOWTIE (n=5, cap=7, k=50, states=79, pool=10)
def f_BOWTIE : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)
def rows_BOWTIE : List ℕ := [1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 5, 6, 9, 17, 24, 3, 6, 5, 6, 9, 24, 3, 5, 6, 9, 11, 14, 17, 24, 26, 3, 5, 6, 9, 13, 14, 17, 24, 28, 17, 24, 3, 5, 6, 9, 17, 19, 22, 24, 26, 3, 5, 6, 9, 17, 21, 22, 24, 28]
def xs_BOWTIE : List ℕ := [0x1d8ed2d96d56c00000000003f, 0x22d9412cd4b1401ff001ff0c0, 0xb31189b098e1bfe003fe00300, 0xc4622dc6e30a000003ffffc00, 0xf87c3e07020c3ffffc0000000]
def pool_BOWTIE : List ℕ := [0x80000a4340cc32, 0x780a000360d437, 0x5400030340c833, 0x8000030370c836, 0x3000080370c835, 0x54000a4370cc35, 0xa400054370cc36, 0xa400080340c833, 0x3000054340cc32, 0x2006000330c834]
def NN_BOWTIE : ℕ → ℕ
  | 4 => 2
  | 5 => 40
  | 6 => 36
  | 7 => 1
  | _ => 0
def HT_BOWTIE : ℕ → ℕ
  | 4 => 0xe69f9bc42160bc5f
  | 5 => 0xf742a3d0f3d6a6caf2c4f573e8b66066e180f3e4dc87be0edbeab3c2d93b4845d6c8153bd3b86897cf20682cc92e1222c36e694fc2da43cfb73fc6f7b64bf507b61f6228b3b81b1bb2c6c34ba8357aafa51ea19ca01014059f6d175f992962fa933e75078d7ecc3487246ed6697d7a4456dfe4dc558d03dd549ad51f4869b93243677bab3e0dcfd73c0e3e7f28b49293203432401c85f03b16c64768158068a1
  | 6 => 0xf8103679f7ee878cf2c4f573f084fb7be4e1031be2a67339d9ce2dd4d311441ec7bfd293c7633531c6b10786bd88bbf8b2c6c34bae58d960ad239bdb9f6d175f99876a0897388465933e7507917398168d7ecc348aee859b83a2b2267f1563cf7cb80320792278b673133ce4697d7a4463f740d054f0553f4b2540302c47248c231776e01a45f6430cea2d5a081c1522
  | 7 => 0x697d7a44
  | _ => 0
def PT_BOWTIE : ℕ → ℕ
  | 4 => 0xc847302
  | 5 => 0x70d40420520409410188cc1110170d0003213c406234000d4111023c409f3033c410a3406cd0152032040052306ccc1b35020404034020410810364940031028d42235028cc1c33030885f3055c40941027cc1111033c40c0303
  | 6 => 0x38c80e100040804040390c0f41010000e3003900050103cc00503004000f3203c8001010100c0e420041004010040c0e31010080f4303c840e2003cc40000039040f4203c400f40014000504014080e21
  | _ => 0
def Z_BOWTIE (s : ℕ) := bar 50 (Sgen 50 7 xs_BOWTIE PT_BOWTIE) NN_BOWTIE (idxGen NN_BOWTIE HT_BOWTIE) id pool_BOWTIE s
theorem z_BOWTIE_0 : span (Z_BOWTIE 0) 0 0 = true := rfl
theorem z_BOWTIE_1 : span (Z_BOWTIE 1) 0 0 = true := rfl
theorem z_BOWTIE_2 : span (Z_BOWTIE 2) 0 0 = true := rfl
theorem z_BOWTIE_3 : span (Z_BOWTIE 3) 0 0 = true := rfl
theorem h_BOWTIE_4_0 : span (Z_BOWTIE 4) 2 0 = true := by decide +kernel
theorem z_BOWTIE_4 : span (Z_BOWTIE 4) 2 0 = true := h_BOWTIE_4_0
theorem h_BOWTIE_5_0 : span (Z_BOWTIE 5) 12 0 = true := by decide +kernel
theorem h_BOWTIE_5_12 : span (Z_BOWTIE 5) 12 12 = true := by decide +kernel
theorem h_BOWTIE_5_24 : span (Z_BOWTIE 5) 12 24 = true := by decide +kernel
theorem h_BOWTIE_5_36 : span (Z_BOWTIE 5) 4 36 = true := by decide +kernel
theorem z_BOWTIE_5 : span (Z_BOWTIE 5) 40 0 = true := (@span_join (Z_BOWTIE 5) 24 0 16 (@span_join (Z_BOWTIE 5) 12 0 12 h_BOWTIE_5_0 h_BOWTIE_5_12) (@span_join (Z_BOWTIE 5) 12 24 4 h_BOWTIE_5_24 h_BOWTIE_5_36))
theorem h_BOWTIE_6_0 : span (Z_BOWTIE 6) 12 0 = true := by decide +kernel
theorem h_BOWTIE_6_12 : span (Z_BOWTIE 6) 12 12 = true := by decide +kernel
theorem h_BOWTIE_6_24 : span (Z_BOWTIE 6) 12 24 = true := by decide +kernel
theorem z_BOWTIE_6 : span (Z_BOWTIE 6) 36 0 = true := (@span_join (Z_BOWTIE 6) 12 0 24 h_BOWTIE_6_0 (@span_join (Z_BOWTIE 6) 12 12 12 h_BOWTIE_6_12 h_BOWTIE_6_24))
theorem h_BOWTIE_7_0 : span (Z_BOWTIE 7) 1 0 = true := by decide +kernel
theorem z_BOWTIE_7 : span (Z_BOWTIE 7) 1 0 = true := h_BOWTIE_7_0
theorem base_BOWTIE : ∀ s : ℕ, HasCircuitSize 5 f_BOWTIE s → 8 ≤ s := by
  refine prove_base 5 50 7 f_BOWTIE rows_BOWTIE xs_BOWTIE pool_BOWTIE NN_BOWTIE HT_BOWTIE PT_BOWTIE
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_BOWTIE_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_BOWTIE_7 i (Nat.zero_le i) hi
    )

-- Base case NET (n=6, cap=7, k=72, states=26, pool=9)
def f_NET : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)
def rows_NET : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 10, 10, 10, 12, 12, 12, 16, 17, 17, 17, 20, 20, 20, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 33, 33, 33, 34, 34, 34, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 3, 5, 9, 3, 6, 18, 5, 6, 36, 9, 11, 14, 26, 13, 14, 44, 18, 19, 21, 25, 21, 22, 52, 25, 26, 3, 5, 6, 9, 18, 29, 30, 36, 60, 36, 35, 37, 41, 35, 38, 50, 41, 44, 3, 5, 6, 9, 18, 36, 43, 46, 58, 50, 52, 3, 5, 6, 9, 18, 36, 51, 53, 57, 3, 5, 6, 9, 18, 36, 57, 58, 60]
def xs_NET : List ℕ := [0x25f2c25a78569e264f007fc00038000e0007, 0x4a955ea9c8ab235cb900000ff9c000001c38, 0x9329a53497cc74e9d20000000003fe70e1c0, 0xe4420e4622d188fe04ff800ffe03ff80fe00, 0xe874388102e1ff1020fffff00003ffff0000, 0xf0783f07ff00408100fffffffffc00000000]
def pool_NET : List ℕ := [0x1803000491204c, 0xd8060fc5012849, 0xac000fc4d12848, 0x64030fc501344c, 0x180000c4c12049, 0xc000184c12448, 0x64000fc5012849, 0xd8030fc4d12848, 0xac060fc501344c]
def NN_NET : ℕ → ℕ
  | 5 => 6
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT_NET : ℕ → ℕ
  | 5 => 0xaf88224b70c6766557b62238571865263d1fc77a23def86d
  | 6 => 0xd5d2024bd11ae5e5cb9323a0bf32673cb6491b83b504a249b064ad26b04415efab09f6778f29c79884d9c66f80263ad760b07a3441b4b838403ba3af3ce49e4c2fdc23a307fae6c603fe551b
  | 7 => 0x80263ad7
  | _ => 0
def PT_NET : ℕ → ℕ
  | 5 => 0x14c0c530248c08f32048cc0f330
  | 6 => 0x64103c840f20018c0073101d0007320041401040040407500000001020194801000040c075103c400742
  | _ => 0
def Z_NET (s : ℕ) := bar 72 (Sgen 72 7 xs_NET PT_NET) NN_NET (idxGen NN_NET HT_NET) id pool_NET s
theorem z_NET_0 : span (Z_NET 0) 0 0 = true := rfl
theorem z_NET_1 : span (Z_NET 1) 0 0 = true := rfl
theorem z_NET_2 : span (Z_NET 2) 0 0 = true := rfl
theorem z_NET_3 : span (Z_NET 3) 0 0 = true := rfl
theorem z_NET_4 : span (Z_NET 4) 0 0 = true := rfl
theorem h_NET_5_0 : span (Z_NET 5) 6 0 = true := by decide +kernel
theorem z_NET_5 : span (Z_NET 5) 6 0 = true := h_NET_5_0
theorem h_NET_6_0 : span (Z_NET 6) 12 0 = true := by decide +kernel
theorem h_NET_6_12 : span (Z_NET 6) 7 12 = true := by decide +kernel
theorem z_NET_6 : span (Z_NET 6) 19 0 = true := (@span_join (Z_NET 6) 12 0 7 h_NET_6_0 h_NET_6_12)
theorem h_NET_7_0 : span (Z_NET 7) 1 0 = true := by decide +kernel
theorem z_NET_7 : span (Z_NET 7) 1 0 = true := h_NET_7_0
theorem base_NET : ∀ s : ℕ, HasCircuitSize 6 f_NET s → 8 ≤ s := by
  refine prove_base 6 72 7 f_NET rows_NET xs_NET pool_NET NN_NET HT_NET PT_NET
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_NET_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_NET_7 i (Nat.zero_le i) hi
    )

-- Base case C6 (n=6, cap=7, k=78, states=8, pool=5)
def f_C6 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_C6 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 38, 38, 3, 5, 3, 10, 5, 20, 7, 14, 22, 10, 40, 11, 13, 41, 3, 5, 10, 13, 14, 20, 28, 40, 44, 48, 20, 48, 19, 21, 49, 3, 5, 10, 19, 20, 22, 26, 40, 48, 50, 26, 28, 56, 3, 5, 10, 20, 27, 29, 40, 48, 57, 40, 48, 3, 5, 10, 20, 35, 37, 40, 41, 48, 49, 35, 42, 50, 37, 44, 52, 3, 5, 10, 20, 39, 40, 46, 48, 54]
def xs_C6 : List ℕ := [0x99359933005f00be15c0007fe7fc001c003803, 0xaa8e0a81533690152f37fe38000007fe00001cc, 0xad701502a419257a47cbffc0000000000ffc1f0, 0x322462374e6201dcfa200000007ff8000fffe00, 0xc449845b8fbc7e6004800000007ffffff000000, 0xf87ff87c09c04b809003ffffff8000000000000]
def pool_C6 : List ℕ := [0x24020d45813851, 0x1000074531384f, 0x60040d46513c53, 0x8000385113c4e, 0xcc090746514458]
def NN_C6 : ℕ → ℕ
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT_C6 : ℕ → ℕ
  | 6 => 0xf44a7c96734fb6dc691bff606195314356426bf32c44989c2aa6f5bd
  | 7 => 0xf44a7c96
  | _ => 0
def PT_C6 : ℕ → ℕ
  | 6 => 0x41401000040c0102004100101
  | _ => 0
def Z_C6 (s : ℕ) := bar 78 (Sgen 78 7 xs_C6 PT_C6) NN_C6 (idxGen NN_C6 HT_C6) id pool_C6 s
theorem z_C6_0 : span (Z_C6 0) 0 0 = true := rfl
theorem z_C6_1 : span (Z_C6 1) 0 0 = true := rfl
theorem z_C6_2 : span (Z_C6 2) 0 0 = true := rfl
theorem z_C6_3 : span (Z_C6 3) 0 0 = true := rfl
theorem z_C6_4 : span (Z_C6 4) 0 0 = true := rfl
theorem z_C6_5 : span (Z_C6 5) 0 0 = true := rfl
theorem h_C6_6_0 : span (Z_C6 6) 7 0 = true := by decide +kernel
theorem z_C6_6 : span (Z_C6 6) 7 0 = true := h_C6_6_0
theorem h_C6_7_0 : span (Z_C6 7) 1 0 = true := by decide +kernel
theorem z_C6_7 : span (Z_C6 7) 1 0 = true := h_C6_7_0
theorem base_C6 : ∀ s : ℕ, HasCircuitSize 6 f_C6 s → 8 ≤ s := by
  refine prove_base 6 78 7 f_C6 rows_C6 xs_C6 pool_C6 NN_C6 HT_C6 PT_C6
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_C6_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_C6_7 i (Nat.zero_le i) hi
    )

-- Base case TwoK3 (n=6, cap=8, k=102, states=122, pool=5)
def f_TwoK3 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_TwoK3 : List ℕ := [1, 1, 2, 2, 4, 4, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 3, 6, 5, 6, 24, 40, 3, 5, 6, 11, 13, 24, 25, 40, 41, 48, 3, 5, 6, 11, 14, 24, 26, 40, 42, 48, 3, 5, 6, 13, 14, 24, 28, 40, 44, 48, 24, 48, 3, 5, 6, 19, 21, 24, 25, 40, 48, 49, 3, 5, 6, 19, 22, 24, 26, 40, 48, 50, 3, 5, 6, 21, 22, 24, 28, 40, 48, 52, 40, 48, 3, 5, 6, 24, 35, 37, 40, 41, 48, 49, 3, 5, 6, 24, 35, 38, 40, 42, 48, 50, 3, 5, 6, 24, 37, 38, 40, 44, 48, 52]
def xs_TwoK3 : List ℕ := [0x4c13acc02c0b96c02c0b56c5c00003ff000003ff000003ff03, 0x96b50540565d0340555d034b400ffc00000ffc00000ffc000c, 0xad8260989781605857816058ebff000003ff000003ff0000030, 0x320c8321380e03817e1f87e3000000000000000003fffffffc0, 0xc2308c22de378de3982609810000000003fffffffc000000000, 0xfc3f0fc3e0380e02e0380e0203fffffffc00000000000000000]
def pool_TwoK3 : List ℕ := [0xc8280f06919c66, 0x9806118771b46c, 0x48080706919c66, 0x10020006719869, 0x10000086919867]
def NN_TwoK3 : ℕ → ℕ
  | 4 => 2
  | 5 => 12
  | 6 => 58
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_TwoK3 : ℕ → ℕ
  | 4 => 0x4d8c177f15c49257
  | 5 => 0xf0e5633ee7484b31a8d065f8979d3f4793f63bc08671bd54863d7f2181afece53dbda1882359e6cf198b67e50853723f
  | 6 => 0xfff2feb1fbb42ec1f805c600f741e864f4956378f1569e11edfc6b6de33c240fde836f10ddbefff4d6536b5ed4908d11cfe8ef31cdab9dedccacded6cbc2310ec568bed5ba4ccae7ba49c705b387ff19b114f671ae607e3ca911d87ca7a10ad8a32309d196921a7d95b4c51295798f3993292937929c19388caa887f8a7b658488976d8f868eb994859c9f8d807d69288041d1617e30b21078e2632b77386d21729f95276e1d55396b13cd37690c11976636a31c53d68f2d49c3ea2044353bb331b2062a31897ba42cb2ed7d28204f2e24d3f01c20c002c41f2967b51d792b3f1c8bb31a0e1442b5
  | 7 => 0xf805c600f35b4616e5e0c18ae59fd215e4eeedf8ddbefff4da55ffa0cddc75e9cbb17652ca742a1bc87d2041c780807ac4cd528ec4852d77c0d065f9b72faa58b33f4aeba911d87ca32712718b7dca57859c9f8d83d6d5dc839707388036fa067963bc88788c92f66f6896bd6edcc4e06e513d8b6cfc2284600dbbaa4eac3ae54ab8d6c54a3175144723967344353bb343db4bcc39a4161334e138ec345fccb131897ba42eb8073529c048df29a9ef5c26bc3c25229404c81f2967b5108017bc05304534
  | 8 => 0xa911d87c
  | _ => 0
def PT_TwoK3 : ℕ → ℕ
  | 4 => 0xc404301
  | 5 => 0x38885422160d441321c8c86f32148885820504880f32164c499202
  | 6 => 0x6480c21057c404e32130c84e350a8d00c30630c15f10438d81c10200d00335020406a36078d802101704143303a8d42020600c40210300d40336078d40e34034405a22130c0de3040cc85e32170000810200cc1d20634411a20378c0c2102a8cc1626020410210438cc0d000048c08000ac408c3040cd00d10508000036000c848105
  | 7 => 0x101039080e5003d440f40004100e20038c00f5203cc40f3001404050003d4005020140c0f53000000e5303d500105039440f2003c840f23010040f43039040504039480e23039000402010140e43004000e54010100f42038c401030100c0f4101000050503884010203c400e10
  | _ => 0
def Z_TwoK3 (s : ℕ) := bar 102 (Sgen 102 8 xs_TwoK3 PT_TwoK3) NN_TwoK3 (idxGen NN_TwoK3 HT_TwoK3) id pool_TwoK3 s
theorem z_TwoK3_0 : span (Z_TwoK3 0) 0 0 = true := rfl
theorem z_TwoK3_1 : span (Z_TwoK3 1) 0 0 = true := rfl
theorem z_TwoK3_2 : span (Z_TwoK3 2) 0 0 = true := rfl
theorem z_TwoK3_3 : span (Z_TwoK3 3) 0 0 = true := rfl
theorem h_TwoK3_4_0 : span (Z_TwoK3 4) 2 0 = true := by decide +kernel
theorem z_TwoK3_4 : span (Z_TwoK3 4) 2 0 = true := h_TwoK3_4_0
theorem h_TwoK3_5_0 : span (Z_TwoK3 5) 12 0 = true := by decide +kernel
theorem z_TwoK3_5 : span (Z_TwoK3 5) 12 0 = true := h_TwoK3_5_0
theorem h_TwoK3_6_0 : span (Z_TwoK3 6) 12 0 = true := by decide +kernel
theorem h_TwoK3_6_12 : span (Z_TwoK3 6) 12 12 = true := by decide +kernel
theorem h_TwoK3_6_24 : span (Z_TwoK3 6) 12 24 = true := by decide +kernel
theorem h_TwoK3_6_36 : span (Z_TwoK3 6) 12 36 = true := by decide +kernel
theorem h_TwoK3_6_48 : span (Z_TwoK3 6) 10 48 = true := by decide +kernel
theorem z_TwoK3_6 : span (Z_TwoK3 6) 58 0 = true := (@span_join (Z_TwoK3 6) 24 0 34 (@span_join (Z_TwoK3 6) 12 0 12 h_TwoK3_6_0 h_TwoK3_6_12) (@span_join (Z_TwoK3 6) 12 24 22 h_TwoK3_6_24 (@span_join (Z_TwoK3 6) 12 36 10 h_TwoK3_6_36 h_TwoK3_6_48)))
theorem h_TwoK3_7_0 : span (Z_TwoK3 7) 12 0 = true := by decide +kernel
theorem h_TwoK3_7_12 : span (Z_TwoK3 7) 12 12 = true := by decide +kernel
theorem h_TwoK3_7_24 : span (Z_TwoK3 7) 12 24 = true := by decide +kernel
theorem h_TwoK3_7_36 : span (Z_TwoK3 7) 12 36 = true := by decide +kernel
theorem h_TwoK3_7_48 : span (Z_TwoK3 7) 1 48 = true := by decide +kernel
theorem z_TwoK3_7 : span (Z_TwoK3 7) 49 0 = true := (@span_join (Z_TwoK3 7) 24 0 25 (@span_join (Z_TwoK3 7) 12 0 12 h_TwoK3_7_0 h_TwoK3_7_12) (@span_join (Z_TwoK3 7) 12 24 13 h_TwoK3_7_24 (@span_join (Z_TwoK3 7) 12 36 1 h_TwoK3_7_36 h_TwoK3_7_48)))
theorem h_TwoK3_8_0 : span (Z_TwoK3 8) 1 0 = true := by decide +kernel
theorem z_TwoK3_8 : span (Z_TwoK3 8) 1 0 = true := h_TwoK3_8_0
theorem base_TwoK3 : ∀ s : ℕ, HasCircuitSize 6 f_TwoK3 s → 9 ≤ s := by
  refine prove_base 6 102 8 f_TwoK3 rows_TwoK3 xs_TwoK3 pool_TwoK3 NN_TwoK3 HT_TwoK3 PT_TwoK3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_TwoK3_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_TwoK3_8 i (Nat.zero_le i) hi
    )

-- Base case K3C5 (n=6, cap=8, k=88, states=111, pool=5)
def f_K3C5 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_K3C5 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 3, 5, 6, 9, 11, 14, 18, 26, 40, 42, 48, 13, 14, 44, 18, 48, 3, 5, 6, 9, 18, 19, 21, 25, 40, 48, 49, 21, 22, 52, 25, 26, 56, 3, 5, 6, 9, 18, 29, 30, 40, 48, 60, 40, 48, 3, 5, 6, 9, 18, 35, 37, 40, 41, 48, 49, 3, 5, 6, 9, 18, 35, 38, 40, 42, 48, 50, 3, 5, 6, 9, 18, 37, 38, 40, 44, 48, 52]
def xs_K3C5 : List ℕ := [0x560aeb5815933ac206d4f000003ff80001ffc000007, 0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38, 0xacc118231330e118e098d2ffe000001ff8e000e000c0, 0x310620c437470620eee304000000001fff0000ffff00, 0xc21843085b87fbc3130020000000001fffffff000000, 0xfc1f83f07c049c029c0200ffffffffe0000000000000]
def pool_K3C5 : List ℕ := [0x108371345c16458, 0xd418028611746c, 0xd4080686c16861, 0x1803000591605c, 0x180000c5c16059]
def NN_K3C5 : ℕ → ℕ
  | 5 => 2
  | 6 => 59
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_K3C5 : ℕ → ℕ
  | 5 => 0xaf7f705075df09eb
  | 6 => 0xff05e072f727b177f3068765eaa33932db11b933d8cc5b6dcd35058ccc15227dca2f76a5c83ad31bc7250273c15a0367b4a0336cb10a8789afa7431baca18245a8900a13a2695142a1496e339ff66ae49c594e299b4c90679920e7e69912aafc9669f83595b74714954a15269059f51c8b53f7cd85bd41f47c32030e752ab69a72c697296f78934d6d024dd56a88734369689034692b5d8d653017b36252b02e43fac3934359dbb44239f8a53d49d89b37e19f5a2dcc7be728df8ae4233bb3a41f61f4541e1edb431b5f2e0917711a07161b410c15acbf2f11a788f510e7b25a08bdd900062edfb000979a5e
  | 7 => 0xfad5aba9f2eecca3e97ae7ace6bcb686e3778b7fe03ffe4fd963b263d4da459cd3c109c0d32c8367cea5d07ecbb58782cb9bad62c03ecc65bd3d402baec4164fab8da282aa9335c4a77738ef9ff66ae49a72143c980ef4d38d5b9238853ae9e8813088c1801c66e67c90fda2795c361d752ab69a692b5d8d652373366061f0715bb0fd5d57c5b116504f73f14825eea6435ca5264359dbb44239f8a53d49d89b38731eb53663a28d345f23502a623341161b410c13fb51330a946a4a0112919d00f8fd3a
  | 8 => 0x161b410c
  | _ => 0
def PT_K3C5 : ℕ → ℕ
  | 5 => 0x1cc848302
  | 6 => 0x141013cd413101bcc0d533040d80b10128406f3604c410910144c12c23054d01130554d42e3402c410a10510400910444c181321a8814b10384818a10324409634070d41635010411536028411a3052440c910510409035058d82e3031040c410510404135004d01033040d02f30404d80c22104cc01310b8d81130358cc2f35064982e350
  | 7 => 0xe510394c0e210100c0f10014100f50010140e40014080501038c40f54014000f4103d440f4003cc00401004000e2303cc40e4203d0c0404010080e10039040104004080e50039500e300390c0f53039480f210040c0105004040f20010000f4203d4800000140c0f23038800505
  | _ => 0
def Z_K3C5 (s : ℕ) := bar 88 (Sgen 88 8 xs_K3C5 PT_K3C5) NN_K3C5 (idxGen NN_K3C5 HT_K3C5) id pool_K3C5 s
theorem z_K3C5_0 : span (Z_K3C5 0) 0 0 = true := rfl
theorem z_K3C5_1 : span (Z_K3C5 1) 0 0 = true := rfl
theorem z_K3C5_2 : span (Z_K3C5 2) 0 0 = true := rfl
theorem z_K3C5_3 : span (Z_K3C5 3) 0 0 = true := rfl
theorem z_K3C5_4 : span (Z_K3C5 4) 0 0 = true := rfl
theorem h_K3C5_5_0 : span (Z_K3C5 5) 2 0 = true := by decide +kernel
theorem z_K3C5_5 : span (Z_K3C5 5) 2 0 = true := h_K3C5_5_0
theorem h_K3C5_6_0 : span (Z_K3C5 6) 12 0 = true := by decide +kernel
theorem h_K3C5_6_12 : span (Z_K3C5 6) 12 12 = true := by decide +kernel
theorem h_K3C5_6_24 : span (Z_K3C5 6) 12 24 = true := by decide +kernel
theorem h_K3C5_6_36 : span (Z_K3C5 6) 12 36 = true := by decide +kernel
theorem h_K3C5_6_48 : span (Z_K3C5 6) 11 48 = true := by decide +kernel
theorem z_K3C5_6 : span (Z_K3C5 6) 59 0 = true := (@span_join (Z_K3C5 6) 24 0 35 (@span_join (Z_K3C5 6) 12 0 12 h_K3C5_6_0 h_K3C5_6_12) (@span_join (Z_K3C5 6) 12 24 23 h_K3C5_6_24 (@span_join (Z_K3C5 6) 12 36 11 h_K3C5_6_36 h_K3C5_6_48)))
theorem h_K3C5_7_0 : span (Z_K3C5 7) 12 0 = true := by decide +kernel
theorem h_K3C5_7_12 : span (Z_K3C5 7) 12 12 = true := by decide +kernel
theorem h_K3C5_7_24 : span (Z_K3C5 7) 12 24 = true := by decide +kernel
theorem h_K3C5_7_36 : span (Z_K3C5 7) 12 36 = true := by decide +kernel
theorem h_K3C5_7_48 : span (Z_K3C5 7) 1 48 = true := by decide +kernel
theorem z_K3C5_7 : span (Z_K3C5 7) 49 0 = true := (@span_join (Z_K3C5 7) 24 0 25 (@span_join (Z_K3C5 7) 12 0 12 h_K3C5_7_0 h_K3C5_7_12) (@span_join (Z_K3C5 7) 12 24 13 h_K3C5_7_24 (@span_join (Z_K3C5 7) 12 36 1 h_K3C5_7_36 h_K3C5_7_48)))
theorem h_K3C5_8_0 : span (Z_K3C5 8) 1 0 = true := by decide +kernel
theorem z_K3C5_8 : span (Z_K3C5 8) 1 0 = true := h_K3C5_8_0
theorem base_K3C5 : ∀ s : ℕ, HasCircuitSize 6 f_K3C5 s → 9 ≤ s := by
  refine prove_base 6 88 8 f_K3C5 rows_K3C5 xs_K3C5 pool_K3C5 NN_K3C5 HT_K3C5 PT_K3C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok z_K3C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok z_K3C5_8 i (Nat.zero_le i) hi
    )


/-! Section 4: Generic graph-edge-function reductions for all 85 graphs -/

def gfn {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) : BFn n :=
  fun x => A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

def Eb_K3 : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,2)]
def Eb_C5 : List (Fin 5 × Fin 5) := [(0,1),(0,2),(1,3),(2,4),(3,4)]
def Eb_BOWTIE : List (Fin 5 × Fin 5) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
def Eb_NET : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5)]
def Eb_C6 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(1,3),(2,4),(3,5),(4,5)]
def Eb_TwoK3 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
def Eb_K3C5 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]

theorem base_K3_gfn : ∀ s, HasCircuitSize 3 (gfn [] Eb_K3) s → 4 ≤ s := by
  have : gfn [] Eb_K3 = f_K3 := by funext x; simp [gfn, Eb_K3, f_K3, Bool.or_assoc]
  rw [this]; exact base_K3

theorem base_C5_gfn : ∀ s, HasCircuitSize 5 (gfn [] Eb_C5) s → 7 ≤ s := by
  have : gfn [] Eb_C5 = f_C5 := by funext x; simp [gfn, Eb_C5, f_C5, Bool.or_assoc]
  rw [this]; exact base_C5

theorem base_BOWTIE_gfn : ∀ s, HasCircuitSize 5 (gfn [] Eb_BOWTIE) s → 8 ≤ s := by
  have : gfn [] Eb_BOWTIE = f_BOWTIE := by funext x; simp [gfn, Eb_BOWTIE, f_BOWTIE, Bool.or_assoc]
  rw [this]; exact base_BOWTIE

theorem base_NET_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_NET) s → 8 ≤ s := by
  have : gfn [] Eb_NET = f_NET := by funext x; simp [gfn, Eb_NET, f_NET, Bool.or_assoc]
  rw [this]; exact base_NET

theorem base_C6_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_C6) s → 8 ≤ s := by
  have : gfn [] Eb_C6 = f_C6 := by funext x; simp [gfn, Eb_C6, f_C6, Bool.or_assoc]
  rw [this]; exact base_C6

theorem base_TwoK3_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_TwoK3) s → 9 ≤ s := by
  have : gfn [] Eb_TwoK3 = f_TwoK3 := by funext x; simp [gfn, Eb_TwoK3, f_TwoK3, Bool.or_assoc]
  rw [this]; exact base_TwoK3

theorem base_K3C5_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_K3C5) s → 9 ≤ s := by
  have : gfn [] Eb_K3C5 = f_K3C5 := by funext x; simp [gfn, Eb_K3C5, f_K3C5, Bool.or_assoc]
  rw [this]; exact base_K3C5

def dedupAux {α : Type} [BEq α] : List α → List α → List α
  | [], acc => acc.reverse
  | a :: t, acc => if acc.contains a then dedupAux t acc else dedupAux t (a :: acc)

def dedup {α : Type} [BEq α] (l : List α) : List α := dedupAux l []

theorem mem_dedupAux {α : Type} [DecidableEq α] : ∀ (l acc : List α) (x : α),
    x ∈ dedupAux l acc ↔ x ∈ l ∨ x ∈ acc
  | [], acc, x => by simp [dedupAux]
  | a :: t, acc, x => by
    simp only [dedupAux]
    by_cases h : acc.contains a = true
    · simp only [h, ↓reduceIte, mem_dedupAux, List.mem_cons]
      have ha : a ∈ acc := by simpa using h
      constructor
      · rintro (ht | hacc)
        · exact Or.inl (Or.inr ht)
        · exact Or.inr hacc
      · rintro ((rfl | ht) | hacc)
        · exact Or.inr ha
        · exact Or.inl ht
        · exact Or.inr hacc
    · simp only [h, Bool.false_eq_true, ↓reduceIte, mem_dedupAux, List.mem_cons]
      tauto

theorem mem_dedup {α : Type} [DecidableEq α] (l : List α) (x : α) :
    x ∈ dedup l ↔ x ∈ l := by
  simpa [dedup] using mem_dedupAux l [] x

def fix0A {n : ℕ} (A : List (Fin n)) (p : Fin n) : List (Fin n) :=
  A.filter (· != p)

def fix0E {n : ℕ} (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n × Fin n) :=
  E.filter (fun e => e.1 != p && e.2 != p)

def nbrs {n : ℕ} (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n) :=
  E.filterMap (fun e => if e.1 == p then some e.2 else if e.2 == p then some e.1 else none)

def fix1A {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n) :=
  dedup (A ++ nbrs E p)

def fix1E {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n × Fin n) :=
  let A1 := fix1A A E p
  E.filter (fun e => e.1 != p && e.2 != p && !A1.contains e.1 && !A1.contains e.2)

def depCheck {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : Bool :=
  A.contains p ||
    (E.all (fun e => e.1 != e.2) &&
      E.any (fun e => (e.1 == p && !A.contains e.2) || (e.2 == p && !A.contains e.1)))

def isoCheck {n k : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k)) (π : Fin n → Fin k) : Bool :=
  E.all (fun e => Eb.any (fun e' => (π e.1 == e'.1 && π e.2 == e'.2) || (π e.1 == e'.2 && π e.2 == e'.1))) &&
  Eb.all (fun e' => E.any (fun e => (π e.1 == e'.1 && π e.2 == e'.2) || (π e.1 == e'.2 && π e.2 == e'.1)))

theorem gfn_le {n val1 val2 : ℕ} {f : BFn n} (hle : val1 ≤ val2)
    (h : ∀ s, HasCircuitSize n f s → val2 ≤ s) : ∀ s, HasCircuitSize n f s → val1 ≤ s :=
  fun s hs => le_trans hle (h s hs)

theorem gfn_empty {n : ℕ} (A : List (Fin n)) (hnd : A.Nodup) :
    ∀ s : ℕ, HasCircuitSize n (gfn A []) s → A.length - 1 ≤ s := by
  intro s h
  have hd := dep_lower_set n (gfn A []) A.toFinset (by
    intro i hi
    have hiA : i ∈ A := List.mem_toFinset.1 hi
    refine ⟨fun _ => false, ?_⟩
    have h0 : gfn A [] (fun _ => false) = false := by simp [gfn]
    have h1 : gfn A [] (Function.update (fun _ => false) i true) = true := by
      simp only [gfn, List.any_nil, Bool.or_false, List.any_eq_true]
      exact ⟨i, hiA, by simp⟩
    simpa [h0, h1]) s h
  rw [List.toFinset_card_of_nodup hnd] at hd
  omega

theorem gfn_nc {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n))
    (h : (!A.isEmpty || !E.isEmpty) = true) :
    ∃ x y : Fin n → Bool, gfn A E x ≠ gfn A E y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : gfn A E (fun _ => false) = false := by simp [gfn]
  have h1 : gfn A E (fun _ => true) = true := by
    cases A with
    | cons a t => simp [gfn]
    | nil =>
      cases E with
      | nil => simp at h
      | cons e t => simp [gfn]
  rw [h0, h1]; decide

theorem gfn_dep {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n)
    (h : depCheck A E p = true) :
    ∃ x : Fin n → Bool, gfn A E (Function.update x p (!x p)) ≠ gfn A E x := by
  simp only [depCheck, Bool.or_eq_true, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, bne_iff_ne, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h with hpA | ⟨hloop, ⟨e, heE, ⟨rfl, hqA⟩ | ⟨rfl, hqA⟩⟩⟩
  · refine ⟨fun _ => false, ?_⟩
    have h0 : gfn A E (fun _ => false) = false := by simp [gfn]
    have h1 : gfn A E (Function.update (fun _ => false) p true) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true]
      exact Or.inl ⟨p, hpA, by simp⟩
    simpa [h0, h1]
  · have hne : e.1 ≠ e.2 := hloop e heE
    refine ⟨fun i => decide (i = e.2), ?_⟩
    have h0 : gfn A E (fun i => decide (i = e.2)) = false := by
      simp only [gfn, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨fun a ha hEq => hqA (hEq ▸ ha), fun e' he' => ?_⟩
      intro ⟨h1, h2⟩
      exact hloop e' he' (h1.trans h2.symm)
    have h1 : gfn A E (Function.update (fun i => decide (i = e.2)) e.1 (!decide (e.1 = e.2))) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨e, heE, ?_, ?_⟩
      · simp [hne]
      · simp [Function.update_of_ne (Ne.symm hne)]
    rw [h0, h1]; decide
  · have hne : e.1 ≠ e.2 := hloop e heE
    refine ⟨fun i => decide (i = e.1), ?_⟩
    have h0 : gfn A E (fun i => decide (i = e.1)) = false := by
      simp only [gfn, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨fun a ha hEq => hqA (hEq ▸ ha), fun e' he' => ?_⟩
      intro ⟨h1, h2⟩
      exact hloop e' he' (h1.trans h2.symm)
    have h1 : gfn A E (Function.update (fun i => decide (i = e.1)) e.2 (!decide (e.2 = e.1))) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨e, heE, ?_, ?_⟩
      · simp [Function.update_of_ne hne]
      · simp [Ne.symm hne]
    rw [h0, h1]; decide

theorem gfn_restrict_false {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) :
    (fun x => gfn A E (Function.update x p false)) = gfn (fix0A A p) (fix0E E p) := by
  funext x
  apply Bool.eq_iff_iff.2
  simp only [gfn, fix0A, fix0E, Bool.or_eq_true, List.any_eq_true, List.mem_filter,
    Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨e, he, h1, h2⟩)
    · by_cases hap : a = p
      · subst hap; simp at hxa
      · exact Or.inl ⟨a, ⟨ha, hap⟩, by simpa [Function.update_of_ne hap] using hxa⟩
    · by_cases h1p : e.1 = p
      · rw [h1p, Function.update_self] at h1; cases h1
      · by_cases h2p : e.2 = p
        · rw [h2p, Function.update_self] at h2; cases h2
        · exact Or.inr ⟨e, ⟨he, h1p, h2p⟩,
            by simpa [Function.update_of_ne h1p] using h1,
            by simpa [Function.update_of_ne h2p] using h2⟩
  · rintro (⟨a, ⟨ha, hap⟩, hxa⟩ | ⟨e, ⟨he, h1p, h2p⟩, h1, h2⟩)
    · exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne hap] using hxa⟩
    · exact Or.inr ⟨e, he,
        by simpa [Function.update_of_ne h1p] using h1,
        by simpa [Function.update_of_ne h2p] using h2⟩

theorem mem_nbrs {n : ℕ} (E : List (Fin n × Fin n)) (p q : Fin n) :
    q ∈ nbrs E p ↔ ∃ e ∈ E, (e.1 = p ∧ e.2 = q) ∨ (e.1 ≠ p ∧ e.2 = p ∧ e.1 = q) := by
  simp only [nbrs, List.mem_filterMap, beq_iff_eq]
  constructor
  · rintro ⟨e, he, h⟩
    split_ifs at h with h1 h2
    · cases h; exact ⟨e, he, Or.inl ⟨h1, rfl⟩⟩
    · cases h; exact ⟨e, he, Or.inr ⟨h1, h2, rfl⟩⟩
  · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2, h3⟩⟩
    · exact ⟨e, he, by rw [if_pos h1, h2]⟩
    · exact ⟨e, he, by rw [if_neg h1, if_pos h2, h3]⟩

theorem gfn_restrict_true {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true) :
    (fun x => gfn A E (Function.update x p true)) = gfn (fix1A A E p) (fix1E A E p) := by
  have hpnot : p ∉ A := by simpa [List.contains_eq_mem] using hpA
  have hne : ∀ e ∈ E, e.1 ≠ e.2 := by simpa [List.all_eq_true, bne_iff_ne] using hloop
  funext x
  apply Bool.eq_iff_iff.2
  simp only [gfn, fix1E, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.mem_filter,
    bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨e, he, h1, h2⟩)
    · have hap : a ≠ p := fun h => hpnot (h ▸ ha)
      refine Or.inl ⟨a, ?_, by simpa [Function.update_of_ne hap] using hxa⟩
      rw [fix1A, mem_dedup]; exact List.mem_append_left _ ha
    · by_cases h1p : e.1 = p
      · have h2p : e.2 ≠ p := fun h => hne e he (h1p.trans h.symm)
        refine Or.inl ⟨e.2, ?_, by simpa [Function.update_of_ne h2p] using h2⟩
        rw [fix1A, mem_dedup]; exact List.mem_append_right _ ((mem_nbrs E p e.2).2 ⟨e, he, Or.inl ⟨h1p, rfl⟩⟩)
      · by_cases h2p : e.2 = p
        · refine Or.inl ⟨e.1, ?_, by simpa [Function.update_of_ne h1p] using h1⟩
          rw [fix1A, mem_dedup]; exact List.mem_append_right _ ((mem_nbrs E p e.1).2 ⟨e, he, Or.inr ⟨h1p, h2p, rfl⟩⟩)
        · have hx1 : x e.1 = true := by simpa [Function.update_of_ne h1p] using h1
          have hx2 : x e.2 = true := by simpa [Function.update_of_ne h2p] using h2
          by_cases m1 : e.1 ∈ fix1A A E p
          · exact Or.inl ⟨e.1, m1, hx1⟩
          · by_cases m2 : e.2 ∈ fix1A A E p
            · exact Or.inl ⟨e.2, m2, hx2⟩
            · exact Or.inr ⟨e, ⟨he, ⟨⟨h1p, h2p⟩, m1⟩, m2⟩, hx1, hx2⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨e, ⟨he, ⟨⟨h1p, h2p⟩, _⟩, _⟩, hx1, hx2⟩)
    · rw [fix1A, mem_dedup, List.mem_append] at ha
      rcases ha with haA | han
      · have hap : a ≠ p := fun h => hpnot (h ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne hap] using hxa⟩
      · obtain ⟨e, he, ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩⟩ := (mem_nbrs E p a).1 han
        · have h2p : e.2 ≠ p := fun h => hne e he (h1.trans h.symm)
          exact Or.inr ⟨e, he, by simp [h1], by simpa [Function.update_of_ne h2p] using hxa⟩
        · exact Or.inr ⟨e, he, by simpa [Function.update_of_ne h1] using hxa, by simp [h2]⟩
    · exact Or.inr ⟨e, he,
        by simpa [Function.update_of_ne h1p] using hx1,
        by simpa [Function.update_of_ne h2p] using hx2⟩

theorem gfn_fix0 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1)) (A' : List (Fin (n + 1))) (E' : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hA : A' = fix0A A p) (hE : E' = fix0E E p)
    (hnc : (!A'.isEmpty || !E'.isEmpty) = true)
    (ih : ∀ s, HasCircuitSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
  intro s h
  have hres : (fun x => gfn A E (Function.update x p false)) = gfn A' E' := by
    rw [hA, hE]; exact gfn_restrict_false A E p
  have hnc' : ∃ x y, gfn A E (Function.update x p false) ≠ gfn A E (Function.update y p false) := by
    obtain ⟨x, y, hxy⟩ := gfn_nc A' E' hnc
    exact ⟨x, y, by simpa [congrFun hres] using hxy⟩
  obtain ⟨s', hs', h'⟩ := one_gate_at n (gfn A E) p false s (gfn_dep A E p hdep) hnc' h
  rw [hres] at h'
  have := ih s' h'
  omega

theorem gfn_fix1 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1)) (A' : List (Fin (n + 1))) (E' : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true)
    (hA : A' = fix1A A E p) (hE : E' = fix1E A E p)
    (hnc : (!A'.isEmpty || !E'.isEmpty) = true)
    (ih : ∀ s, HasCircuitSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
  intro s h
  have hres : (fun x => gfn A E (Function.update x p true)) = gfn A' E' := by
    rw [hA, hE]; exact gfn_restrict_true A E p hpA hloop
  have hnc' : ∃ x y, gfn A E (Function.update x p true) ≠ gfn A E (Function.update y p true) := by
    obtain ⟨x, y, hxy⟩ := gfn_nc A' E' hnc
    exact ⟨x, y, by simpa [congrFun hres] using hxy⟩
  obtain ⟨s', hs', h'⟩ := one_gate_at n (gfn A E) p true s (gfn_dep A E p hdep) hnc' h
  rw [hres] at h'
  have := ih s' h'
  omega

theorem gfn_branch2 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1))
    (A0 : List (Fin (n + 1))) (E0 : List (Fin (n + 1) × Fin (n + 1)))
    (A1 : List (Fin (n + 1))) (E1 : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true)
    (hA0 : A0 = fix0A A p) (hE0 : E0 = fix0E E p)
    (hA1 : A1 = fix1A A E p) (hE1 : E1 = fix1E A E p)
    (hnc0 : (!A0.isEmpty || !E0.isEmpty) = true)
    (hnc1 : (!A1.isEmpty || !E1.isEmpty) = true)
    (ih0 : ∀ s, HasCircuitSize (n + 1) (gfn A0 E0) s → k ≤ s)
    (ih1 : ∀ s, HasCircuitSize (n + 1) (gfn A1 E1) s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 2 ≤ s := by
  intro s h
  have hres0 : (fun x => gfn A E (Function.update x p false)) = gfn A0 E0 := by
    rw [hA0, hE0]; exact gfn_restrict_false A E p
  have hres1 : (fun x => gfn A E (Function.update x p true)) = gfn A1 E1 := by
    rw [hA1, hE1]; exact gfn_restrict_true A E p hpA hloop
  have hnc : ∀ b : Bool, ∃ x y, gfn A E (Function.update x p b) ≠ gfn A E (Function.update y p b) := by
    intro b
    cases b with
    | false =>
      obtain ⟨x, y, hxy⟩ := gfn_nc A0 E0 hnc0
      exact ⟨x, y, by simpa [congrFun hres0] using hxy⟩
    | true =>
      obtain ⟨x, y, hxy⟩ := gfn_nc A1 E1 hnc1
      exact ⟨x, y, by simpa [congrFun hres1] using hxy⟩
  obtain ⟨b, s', hs', h'⟩ := gate_elim_at n (gfn A E) p s (gfn_dep A E p hdep) hnc h
  cases b with
  | false => rw [hres0] at h'; have := ih0 s' h'; omega
  | true => rw [hres1] at h'; have := ih1 s' h'; omega

theorem gfn_iso {n k : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (hiso : isoCheck E Eb π = true) :
    (fun y : Fin k → Bool => gfn [] E (y ∘ π)) = gfn [] Eb := by
  simp only [isoCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq] at hiso
  obtain ⟨h1, h2⟩ := hiso
  funext y
  apply Bool.eq_iff_iff.2
  simp only [gfn, List.any_nil, Bool.false_or, List.any_eq_true, Bool.and_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨e, he, hy1, hy2⟩
    obtain ⟨e', he', ⟨a, b⟩ | ⟨a, b⟩⟩ := h1 e he
    · exact ⟨e', he', a ▸ hy1, b ▸ hy2⟩
    · exact ⟨e', he', b ▸ hy2, a ▸ hy1⟩
  · rintro ⟨e', he', hy1, hy2⟩
    obtain ⟨e, he, ⟨a, b⟩ | ⟨a, b⟩⟩ := h2 e' he'
    · exact ⟨e, he, a.symm ▸ hy1, b.symm ▸ hy2⟩
    · exact ⟨e, he, a.symm ▸ hy2, b.symm ▸ hy1⟩

theorem gfn_base {n k val : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (hiso : isoCheck E Eb π = true)
    (hb : ∀ s : ℕ, HasCircuitSize k (gfn [] Eb) s → val ≤ s) :
    ∀ s : ℕ, HasCircuitSize n (gfn [] E) s → val ≤ s := by
  intro s h
  have h' := relabel_size π (gfn [] E) s h
  rw [gfn_iso E Eb π hiso] at h'
  exact hb s h'

theorem conj_0 : ∀ t : ℕ, HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) t → 1 ≤ t := by
  have heq : (fun x : Fin 2 → Bool => (x 0 && x 1)) = gfn (n := 2) [] [(0, 1)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1)]) (p := (0 : Fin 2)) (A' := [1]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [1] (by decide))

theorem conj_1 : ∀ t : ℕ, HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) t → 2 ≤ t := by
  have heq : (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) = gfn (n := 3) [] [(0, 1), (0, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2)]) (p := (1 : Fin 3)) (A' := []) (E' := [(0, 2)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 2)]) (p := (0 : Fin 3)) (A' := [2]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [2] (by decide)))

theorem conj_2 : ∀ t : ℕ, HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) t → 4 ≤ t := by
  have heq : (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) = gfn (n := 3) [] [(0, 1), (0, 2), (1, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 3 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn

theorem conj_3 : ∀ t : ℕ, HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) t → 3 ≤ t := by
  have heq : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) = gfn (n := 4) [] [(0, 1), (2, 3)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (2, 3)]) (p := (0 : Fin 4)) (A' := [1]) (E' := [(2, 3)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [1]) (E := [(2, 3)]) (p := (1 : Fin 4)) (A' := []) (E' := [(2, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 3)]) (p := (2 : Fin 4)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide))))

theorem conj_4 : ∀ t : ℕ, HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) t → 3 ≤ t := by
  have heq : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) = gfn (n := 4) [] [(0, 1), (0, 2), (0, 3)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3)]) (p := (1 : Fin 4)) (A' := []) (E' := [(0, 2), (0, 3)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3)]) (p := (2 : Fin 4)) (A' := []) (E' := [(0, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 3)]) (p := (0 : Fin 4)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide))))

theorem conj_5 : ∀ t : ℕ, HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) t → 4 ≤ t := by
  have heq : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) = gfn (n := 4) [] [(0, 1), (0, 2), (1, 3)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 3)]) (p := (2 : Fin 4)) (A0 := []) (E0 := [(0, 1), (1, 3)]) (A1 := [0]) (E1 := [(1, 3)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 3)]) (p := (0 : Fin 4)) (A' := []) (E' := [(1, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 3)]) (p := (1 : Fin 4)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 3)]) (p := (0 : Fin 4)) (A' := []) (E' := [(1, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 3)]) (p := (1 : Fin 4)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide))))

theorem conj_6 : ∀ t : ℕ, HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) t → 5 ≤ t := by
  have heq : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) = gfn (n := 4) [] [(0, 1), (0, 2), (0, 3), (1, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 4)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 4 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)

theorem conj_7 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) t → 4 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (3, 4)]) (p := (1 : Fin 5)) (A' := []) (E' := [(0, 2), (3, 4)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 2), (3, 4)]) (p := (0 : Fin 5)) (A' := [2]) (E' := [(3, 4)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [2]) (E := [(3, 4)]) (p := (2 : Fin 5)) (A' := []) (E' := [(3, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 4)]) (p := (3 : Fin 5)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))))

theorem conj_8 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) t → 4 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4)]) (p := (1 : Fin 5)) (A' := []) (E' := [(0, 2), (0, 3), (0, 4)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (0, 4)]) (p := (2 : Fin 5)) (A' := []) (E' := [(0, 3), (0, 4)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (0, 4)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 4)]) (p := (0 : Fin 5)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))))

theorem conj_9 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) t → 5 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4)]) (p := (2 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 3), (1, 4)]) (p := (3 : Fin 5)) (A0 := []) (E0 := [(0, 1), (1, 4)]) (A1 := [0]) (E1 := [(1, 4)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 4)]) (p := (0 : Fin 5)) (A' := []) (E' := [(1, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 4)]) (p := (1 : Fin 5)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 4)]) (p := (0 : Fin 5)) (A' := []) (E' := [(1, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 4)]) (p := (1 : Fin 5)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))))

theorem conj_10 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) t → 6 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (3, 4)]) (p := (3 : Fin 5)) (A' := [4]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [4]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (4 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))

theorem conj_11 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) t → 5 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (1, 3), (2, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 3), (2, 4)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (2, 4)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (2, 4)]) (p := (1 : Fin 5)) (A0 := []) (E0 := [(0, 2), (2, 4)]) (A1 := [0]) (E1 := [(2, 4)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 4)]) (p := (0 : Fin 5)) (A' := []) (E' := [(2, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 4)]) (p := (2 : Fin 5)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 4)]) (p := (0 : Fin 5)) (A' := []) (E' := [(2, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 4)]) (p := (2 : Fin 5)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))))

theorem conj_12 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) t → 6 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 2)]) (p := (4 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))

theorem conj_13 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) t → 6 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 4)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 4)]) (p := (4 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))

theorem conj_14 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) t → 7 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 5)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 5)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))

theorem conj_15 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) t → 7 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (Eb := Eb_C5) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn

theorem conj_16 : ∀ t : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) t → 8 ≤ t := by
  have heq : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := Eb_BOWTIE) (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_BOWTIE_gfn

theorem conj_17 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) t → 5 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (2, 3), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (2, 3), (4, 5)]) (p := (0 : Fin 6)) (A' := [1]) (E' := [(2, 3), (4, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [1]) (E := [(2, 3), (4, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(2, 3), (4, 5)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 3), (4, 5)]) (p := (2 : Fin 6)) (A' := [3]) (E' := [(4, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [3]) (E := [(4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(4, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 5)]) (p := (4 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_18 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) t → 5 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (4, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(0, 2), (0, 3), (4, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (4, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 3), (4, 5)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 3), (4, 5)]) (p := (0 : Fin 6)) (A' := [3]) (E' := [(4, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [3]) (E := [(4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(4, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 5)]) (p := (4 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_19 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) t → 6 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 3), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 3), (4, 5)]) (p := (4 : Fin 6)) (A' := [5]) (E' := [(0, 1), (0, 2), (1, 3)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (1, 3)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 3)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 3)]) (p := (2 : Fin 6)) (A0 := []) (E0 := [(0, 1), (1, 3)]) (A1 := [0]) (E1 := [(1, 3)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 3)]) (p := (0 : Fin 6)) (A' := []) (E' := [(1, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 3)]) (p := (1 : Fin 6)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 3)]) (p := (0 : Fin 6)) (A' := []) (E' := [(1, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 3)]) (p := (1 : Fin 6)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide))))))

theorem conj_20 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) t → 5 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (3, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (3, 4), (3, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(0, 2), (3, 4), (3, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (3, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 2), (3, 5)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 2), (3, 5)]) (p := (0 : Fin 6)) (A' := [2]) (E' := [(3, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [2]) (E := [(3, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(3, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 5)]) (p := (3 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_21 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) t → 5 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(0, 2), (0, 3), (0, 4), (0, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (0, 4), (0, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 3), (0, 4), (0, 5)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (0, 4), (0, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 4), (0, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 4), (0, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 5)]) (p := (0 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_22 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) t → 6 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (1, 5)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (0, 4), (1, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 4), (1, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 4), (1, 5)]) (p := (4 : Fin 6)) (A0 := []) (E0 := [(0, 1), (1, 5)]) (A1 := [0]) (E1 := [(1, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(1, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 5)]) (p := (1 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(1, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 5)]) (p := (1 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_23 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) t → 7 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 5)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (4, 5)]) (p := (4 : Fin 6)) (A' := [5]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_24 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) t → 6 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4), (1, 5)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (1, 4), (1, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 3), (1, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 3), (1, 5)]) (p := (3 : Fin 6)) (A0 := []) (E0 := [(0, 1), (1, 5)]) (A1 := [0]) (E1 := [(1, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(1, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 5)]) (p := (1 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(1, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 5)]) (p := (1 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_25 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) t → 7 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5)]) (p := (4 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (2, 5)]) (A1 := [1]) (E1 := [(0, 2), (0, 3), (2, 5)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (2, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(0, 2), (0, 3), (2, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 3), (2, 5)]) (p := (3 : Fin 6)) (A0 := []) (E0 := [(0, 2), (2, 5)]) (A1 := [0]) (E1 := [(2, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(2, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 5)]) (p := (2 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(2, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 5)]) (p := (2 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))))) (gfn_fix0 (A := [1]) (E := [(0, 2), (0, 3), (2, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(0, 2), (0, 3), (2, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 3), (2, 5)]) (p := (3 : Fin 6)) (A0 := []) (E0 := [(0, 2), (2, 5)]) (A1 := [0]) (E1 := [(2, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(2, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 5)]) (p := (2 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 5)]) (p := (0 : Fin 6)) (A' := []) (E' := [(2, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 5)]) (p := (2 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_26 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) t → 6 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4), (4, 5)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (1, 4), (4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (1, 4), (4, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 4), (4, 5)]) (p := (0 : Fin 6)) (A0 := []) (E0 := [(1, 4), (4, 5)]) (A1 := [1]) (E1 := [(4, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 4), (4, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(4, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 5)]) (p := (4 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [1]) (E := [(4, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(4, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 5)]) (p := (4 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_27 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) t → 7 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (3, 5)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (3, 5)]) (p := (3 : Fin 6)) (A' := [5]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_28 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) t → 7 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5)]) (p := (4 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (1, 3), (3, 5)]) (A1 := [2]) (E1 := [(0, 1), (1, 3), (3, 5)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 3), (3, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 1), (1, 3), (3, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 3), (3, 5)]) (p := (0 : Fin 6)) (A0 := []) (E0 := [(1, 3), (3, 5)]) (A1 := [1]) (E1 := [(3, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 3), (3, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(3, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 5)]) (p := (3 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [1]) (E := [(3, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(3, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 5)]) (p := (3 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))))) (gfn_fix0 (A := [2]) (E := [(0, 1), (1, 3), (3, 5)]) (p := (2 : Fin 6)) (A' := []) (E' := [(0, 1), (1, 3), (3, 5)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 3), (3, 5)]) (p := (0 : Fin 6)) (A0 := []) (E0 := [(1, 3), (3, 5)]) (A1 := [1]) (E1 := [(3, 5)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 3), (3, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(3, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 5)]) (p := (3 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide)))) (gfn_fix0 (A := [1]) (E := [(3, 5)]) (p := (1 : Fin 6)) (A' := []) (E' := [(3, 5)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 5)]) (p := (3 : Fin 6)) (A' := [5]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [5] (by decide))))))

theorem conj_29 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) t → 7 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 5), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 5), (1, 2)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_30 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) t → 7 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 5)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 5)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_31 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_32 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)]) (Eb := Eb_NET) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_NET_gfn

theorem conj_33 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_34 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_35 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 6)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))

theorem conj_36 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (Eb := Eb_C5) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (0 : Fin 5) | 4 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn)

theorem conj_37 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) (Eb := Eb_TwoK3) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_TwoK3_gfn

theorem conj_38 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 8 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5)]) (Eb := Eb_C6) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_C6_gfn

theorem conj_39 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := Eb_BOWTIE) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | 5 => (0 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_BOWTIE_gfn)

theorem conj_40 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (p := (5 : Fin 6)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) (Eb := Eb_BOWTIE) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | 5 => (0 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_BOWTIE_gfn)

theorem conj_41 : ∀ t : ℕ, HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 9 ≤ t := by
  have heq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (Eb := Eb_K3C5) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_K3C5_gfn

theorem conj_42 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 6 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (3, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (3, 4), (5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (3, 4), (5, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 2), (3, 4), (5, 6)]) (p := (0 : Fin 7)) (A' := [2]) (E' := [(3, 4), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [2]) (E := [(3, 4), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(3, 4), (5, 6)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 4), (5, 6)]) (p := (3 : Fin 7)) (A' := [4]) (E' := [(5, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [4]) (E := [(5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_43 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) t → 6 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (0, 4), (5, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (0, 4), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 3), (0, 4), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (0, 4), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 4), (5, 6)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 4), (5, 6)]) (p := (0 : Fin 7)) (A' := [4]) (E' := [(5, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [4]) (E := [(5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_44 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 3), (1, 4), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 3), (1, 4)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 3), (1, 4)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 3), (1, 4)]) (p := (3 : Fin 7)) (A0 := []) (E0 := [(0, 1), (1, 4)]) (A1 := [0]) (E1 := [(1, 4)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 4)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 4)]) (p := (1 : Fin 7)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 4)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 4)]) (p := (1 : Fin 7)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))))))

theorem conj_45 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) t → 6 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (4, 5), (4, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (4, 5), (4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 3), (4, 5), (4, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (4, 5), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 3), (4, 6)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 3), (4, 6)]) (p := (0 : Fin 7)) (A' := [3]) (E' := [(4, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [3]) (E := [(4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_46 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 2), (3, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (3, 4), (5, 6)]) (p := (3 : Fin 7)) (A' := [4]) (E' := [(0, 1), (0, 2), (1, 2), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [4]) (E := [(0, 1), (0, 2), (1, 2), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_47 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 3), (2, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 3), (2, 4), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (2, 4), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (2, 4), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (2, 4)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (2, 4)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (2, 4)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (2, 4)]) (p := (1 : Fin 7)) (A0 := []) (E0 := [(0, 2), (2, 4)]) (A1 := [0]) (E1 := [(2, 4)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 4)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 4)]) (p := (2 : Fin 7)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 4)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 4)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 4)]) (p := (2 : Fin 7)) (A' := [4]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [4] (by decide)))))))

theorem conj_48 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 3), (4, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 3), (4, 5), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 3), (4, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 3), (4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 3)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 3)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 3)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 3)]) (p := (2 : Fin 7)) (A0 := []) (E0 := [(0, 1), (1, 3)]) (A1 := [0]) (E1 := [(1, 3)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 3)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 3)]) (p := (1 : Fin 7)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 3)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 3)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 3)]) (p := (1 : Fin 7)) (A' := [3]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [3] (by decide)))))))

theorem conj_49 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) t → 6 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 3), (0, 4), (0, 5), (0, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (0, 4), (0, 5), (0, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 4), (0, 5), (0, 6)]) (k := 3) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 4), (0, 5), (0, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 5), (0, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 5), (0, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 6)]) (p := (0 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_50 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (0, 5), (1, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (0, 4), (0, 5), (1, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 4), (0, 5), (1, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 4), (0, 5), (1, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 5), (1, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 5), (1, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (1, 6)]) (A1 := [0]) (E1 := [(1, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 6)]) (p := (1 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 6)]) (p := (1 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_51 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 2), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_52 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (1, 5), (1, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (0, 4), (1, 5), (1, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 4), (1, 5), (1, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 4), (1, 5), (1, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 4), (1, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 4), (1, 6)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 1), (1, 6)]) (A1 := [0]) (E1 := [(1, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 6)]) (p := (1 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(1, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(1, 6)]) (p := (1 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_53 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 5), (2, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 5), (2, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 4), (2, 6)]) (A1 := [1]) (E1 := [(0, 2), (0, 4), (2, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (2, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 4), (2, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 4), (2, 6)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 2), (2, 6)]) (A1 := [0]) (E1 := [(2, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))) (gfn_fix0 (A := [1]) (E := [(0, 2), (0, 4), (2, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 4), (2, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 4), (2, 6)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 2), (2, 6)]) (A1 := [0]) (E1 := [(2, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_54 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (1, 5), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (0, 4), (1, 5), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 4), (1, 5), (5, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 4), (1, 5), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (1, 5), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 5), (5, 6)]) (p := (0 : Fin 7)) (A0 := []) (E0 := [(1, 5), (5, 6)]) (A1 := [1]) (E1 := [(5, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 5), (5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [1]) (E := [(5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_55 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 4), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 4), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_56 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_57 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_58 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 5), (2, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 5), (2, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (2, 6)]) (A1 := [1]) (E1 := [(0, 2), (0, 3), (2, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (2, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (2, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 3), (2, 6)]) (p := (3 : Fin 7)) (A0 := []) (E0 := [(0, 2), (2, 6)]) (A1 := [0]) (E1 := [(2, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))) (gfn_fix0 (A := [1]) (E := [(0, 2), (0, 3), (2, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (2, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 3), (2, 6)]) (p := (3 : Fin 7)) (A0 := []) (E0 := [(0, 2), (2, 6)]) (A1 := [0]) (E1 := [(2, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(2, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(2, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(2, 6)]) (p := (2 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_59 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (2, 5), (3, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (2, 5), (3, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (3, 6)]) (A1 := [2]) (E1 := [(0, 1), (0, 3), (3, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (3, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (3, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (0, 3), (3, 6)]) (p := (2 : Fin 7)) (A0 := []) (E0 := [(0, 3), (3, 6)]) (A1 := [0]) (E1 := [(3, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (3, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(3, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 6)]) (p := (3 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(3, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(3, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 6)]) (p := (3 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))) (gfn_fix0 (A := [2]) (E := [(0, 1), (0, 3), (3, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (3, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 3), (3, 6)]) (p := (1 : Fin 7)) (A0 := []) (E0 := [(0, 3), (3, 6)]) (A1 := [0]) (E1 := [(3, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 3), (3, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(3, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 6)]) (p := (3 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [0]) (E := [(3, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(3, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(3, 6)]) (p := (3 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_60 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (1, 4), (4, 6)]) (A1 := [2]) (E1 := [(0, 1), (1, 4), (4, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 4), (4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (1, 4), (4, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 4), (4, 6)]) (p := (0 : Fin 7)) (A0 := []) (E0 := [(1, 4), (4, 6)]) (A1 := [1]) (E1 := [(4, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 4), (4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [1]) (E := [(4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))) (gfn_fix0 (A := [2]) (E := [(0, 1), (1, 4), (4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (1, 4), (4, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 4), (4, 6)]) (p := (0 : Fin 7)) (A0 := []) (E0 := [(1, 4), (4, 6)]) (A1 := [1]) (E1 := [(4, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 4), (4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [1]) (E := [(4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_61 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) t → 7 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4), (4, 5), (4, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (1, 4), (4, 5), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (1, 4), (4, 5), (4, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 4), (4, 5), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (1, 4), (4, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (1, 4), (4, 6)]) (p := (0 : Fin 7)) (A0 := []) (E0 := [(1, 4), (4, 6)]) (A1 := [1]) (E1 := [(4, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(1, 4), (4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [1]) (E := [(4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_62 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (1, 4), (4, 5), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 3), (1, 4), (4, 5), (5, 6)]) (p := (3 : Fin 7)) (A0 := []) (E0 := [(0, 1), (1, 4), (4, 5), (5, 6)]) (A1 := [0]) (E1 := [(1, 4), (4, 5), (5, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 4), (4, 5), (5, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 4), (4, 5), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(1, 4), (4, 5), (5, 6)]) (p := (1 : Fin 7)) (A0 := []) (E0 := [(4, 5), (5, 6)]) (A1 := [4]) (E1 := [(5, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(4, 5), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [4]) (E := [(5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))) (gfn_fix0 (A := [0]) (E := [(1, 4), (4, 5), (5, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 4), (4, 5), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(1, 4), (4, 5), (5, 6)]) (p := (1 : Fin 7)) (A0 := []) (E0 := [(4, 5), (5, 6)]) (A1 := [4]) (E1 := [(5, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(4, 5), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [4]) (E := [(5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(5, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_63 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6), (5, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (0, 3), (4, 5), (4, 6), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 2), (0, 3), (4, 5), (4, 6), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 3), (4, 5), (4, 6), (5, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 3), (4, 5), (4, 6), (5, 6)]) (p := (0 : Fin 7)) (A' := [3]) (E' := [(4, 5), (4, 6), (5, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [3]) (E := [(4, 5), (4, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(4, 5), (4, 6), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(4, 5), (4, 6), (5, 6)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (0 : Fin 3) | 2 => (0 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (1 : Fin 3) | 6 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_64 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (1, 2), (3, 4), (4, 6)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (3, 4), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)))) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 2), (4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_65 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := [6]) (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (Eb := Eb_C5) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | 5 => (0 : Fin 5) | 6 => (0 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn))

theorem conj_66 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 3), (2, 4), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 3), (2, 4), (4, 6)]) (p := (3 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (2, 4), (4, 6)]) (A1 := [1]) (E1 := [(0, 2), (2, 4), (4, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (2, 4), (4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (2, 4), (4, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (2, 4), (4, 6)]) (p := (0 : Fin 7)) (A0 := []) (E0 := [(2, 4), (4, 6)]) (A1 := [2]) (E1 := [(4, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(2, 4), (4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [2]) (E := [(4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))) (gfn_fix0 (A := [1]) (E := [(0, 2), (2, 4), (4, 6)]) (p := (1 : Fin 7)) (A' := []) (E' := [(0, 2), (2, 4), (4, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 2), (2, 4), (4, 6)]) (p := (0 : Fin 7)) (A0 := []) (E0 := [(2, 4), (4, 6)]) (A1 := [2]) (E1 := [(4, 6)]) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(2, 4), (4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))) (gfn_fix0 (A := [2]) (E := [(4, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(4, 6)]) (k := 1) (by decide) (by decide) (by decide) (by decide) (gfn_fix1 (A := []) (E := [(4, 6)]) (p := (4 : Fin 7)) (A' := [6]) (E' := []) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_empty [6] (by decide)))))))

theorem conj_67 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 2)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 2)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 5), (0, 6), (1, 2)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 5), (0, 6), (1, 2)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 6), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 6), (1, 2)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_68 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 5), (1, 2), (1, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 5), (1, 2), (1, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_69 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (3, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_70 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) t → 8 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (1, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (1, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 5), (1, 6)]) (k := 6) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 5), (1, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_71 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 6)]) (Eb := Eb_NET) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (0 : Fin 6) | 4 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_NET_gfn)

theorem conj_72 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_73 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (1, 5), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 5), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (1, 2), (1, 5)]) (A1 := [5]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 2), (1, 5)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [5]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_74 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_75 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (5, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_76 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (5, 6)]) (p := (2 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 3), (0, 4), (1, 5), (1, 6), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 3), (0, 4), (1, 5), (1, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 4), (1, 5), (1, 6), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 4), (1, 5), (1, 6), (5, 6)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 1), (1, 5), (1, 6), (5, 6)]) (A1 := [0]) (E1 := [(1, 5), (1, 6), (5, 6)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (1, 5), (1, 6), (5, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 5), (1, 6), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(1, 5), (1, 6), (5, 6)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (0 : Fin 3) | 2 => (0 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (1 : Fin 3) | 6 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [0]) (E := [(1, 5), (1, 6), (5, 6)]) (p := (0 : Fin 7)) (A' := []) (E' := [(1, 5), (1, 6), (5, 6)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(1, 5), (1, 6), (5, 6)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (0 : Fin 3) | 2 => (0 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (1 : Fin 3) | 6 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_77 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 4), (1, 5), (2, 6), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 4), (1, 5), (2, 6), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 5), (2, 6), (5, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 5), (2, 6), (5, 6)]) (Eb := Eb_C5) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (0 : Fin 5) | 4 => (0 : Fin 5) | 5 => (3 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn))

theorem conj_78 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (2, 5), (3, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (2, 5), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_79 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_80 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (5, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_81 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (p := (4 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2)]) (A1 := [3]) (E1 := [(0, 1), (0, 2), (1, 2)]) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := [(0, 1), (0, 2), (1, 2)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2)]) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2)]) (Eb := Eb_K3) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | 6 => (0 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn))))

theorem conj_82 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (1, 5), (2, 6), (4, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 4), (1, 5), (2, 6), (4, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 6), (4, 6)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 4), (2, 6), (4, 6)]) (Eb := Eb_C5) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (0 : Fin 5) | 4 => (3 : Fin 5) | 5 => (0 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn))

theorem conj_83 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5), (4, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5), (4, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5), (4, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5), (4, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) (Eb := Eb_C5) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (0 : Fin 5) | 4 => (3 : Fin 5) | 5 => (4 : Fin 5) | 6 => (0 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn))

theorem conj_84 : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 9 ≤ t := by
  have heq : (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (5, 6)] := by
    funext x; simp [gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 6), (5, 6)]) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 6), (5, 6)]) (Eb := Eb_C6) (fun i : Fin 7 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (0 : Fin 6) | 4 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base_C6_gfn)


-- L-meta-4795: the six-cycle 0-1-4-2-5-3-0, relabelled onto the graph of conj_38
def fS (x : Fin 6 → Bool) : Bool := x (0 : Fin (6 : ℕ)) && x (1 : Fin (6 : ℕ)) || x (0 : Fin (6 : ℕ)) && x (3 : Fin (6 : ℕ)) || x (1 : Fin (6 : ℕ)) && x (4 : Fin (6 : ℕ)) || x (2 : Fin (6 : ℕ)) && x (4 : Fin (6 : ℕ)) || x (3 : Fin (6 : ℕ)) && x (5 : Fin (6 : ℕ)) || x (2 : Fin (6 : ℕ)) && x (5 : Fin (6 : ℕ))

def piR : Fin 6 → Fin 6 := ![0, 1, 5, 2, 3, 4]

theorem main4795 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
    (∀ (x : Fin 6 → Bool), C.eval (List.ofFn x) = fS x) → 8 ≤ C.size := by
  intro C hC hev
  have h0 : HasCircuitSize 6 fS C.size := ⟨C, hC, le_rfl, hev⟩
  have h1 := relabel_size piR fS C.size h0
  have heq : (fun y : Fin 6 → Bool => fS (y ∘ piR)) =
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
        (x 3 && x 5) || (x 4 && x 5)) := by
    funext y
    revert y
    decide
  rw [heq] at h1
  exact conj_38 C.size h1

end PEqualNP.Outside.L_meta_4795_aux

theorem PEqualNP.Outside.L_meta_4795 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (6 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (6 : ℕ)) && x3 (1 : Fin (6 : ℕ)) || x3 (0 : Fin (6 : ℕ)) && x3 (3 : Fin (6 : ℕ)) || x3 (1 : Fin (6 : ℕ)) && x3 (4 : Fin (6 : ℕ)) || x3 (2 : Fin (6 : ℕ)) && x3 (4 : Fin (6 : ℕ)) || x3 (3 : Fin (6 : ℕ)) && x3 (5 : Fin (6 : ℕ)) || x3 (2 : Fin (6 : ℕ)) && x3 (5 : Fin (6 : ℕ)))) → (8 : ℕ) ≤ x1.size :=
  PEqualNP.Outside.L_meta_4795_aux.main4795
