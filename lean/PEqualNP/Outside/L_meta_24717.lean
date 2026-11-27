import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24717_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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


abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
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
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega



lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj



def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
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
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
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

lemma helper8_restriction
    (h5 : ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 8 ∧
      ∀ i j : Fin 5, D.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (4443 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  rintro ⟨C, hfan, hsize, heval⟩
  let f : (Fin 6 → Bool) → Bool := fun x => C.eval (List.ofFn x)
  have hdep : ∃ x : Fin 6 → Bool,
      f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ f x := by
    refine ⟨fun k : Fin 6 => decide (k = 0 ∨ k = 0), ?_⟩
    have hx : Function.update (fun k : Fin 6 => decide (k = 0 ∨ k = 0))
        (Fin.last 5) (!(decide (Fin.last 5 = (0 : Fin 6) ∨ Fin.last 5 = (0 : Fin 6)))) =
        (fun k : Fin 6 => decide (k = 0 ∨ k = 5)) := by decide +kernel
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [hx, heval 0 5, heval 0 0]
    decide
  have hnc : ∃ y y' : Fin 5 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y' false) := by
    refine ⟨fun k : Fin 5 => decide (k = 0 ∨ k = 0),
      fun k : Fin 5 => decide (k = 3 ∨ k = 3), ?_⟩
    have hx0 : (Fin.snoc (fun k : Fin 5 => decide (k = 0 ∨ k = 0)) false : Fin 6 → Bool) =
        (fun k : Fin 6 => decide (k = 0 ∨ k = 0)) := by decide +kernel
    have hx3 : (Fin.snoc (fun k : Fin 5 => decide (k = 3 ∨ k = 3)) false : Fin 6 → Bool) =
        (fun k : Fin 6 => decide (k = 3 ∨ k = 3)) := by decide +kernel
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [hx0, hx3, heval 0 0, heval 3 3]
    decide
  have hC : HasCircuitSize 6 f 9 := ⟨C, hfan, hsize, fun _ => rfl⟩
  obtain ⟨D, hDfan, hDsize, hDeval⟩ :=
    gate_elim 5 f false 8 hdep hnc hC
  apply h5
  refine ⟨D, hDfan, hDsize, ?_⟩
  intro i j
  rw [hDeval]
  change C.eval (List.ofFn (Fin.snoc (fun k : Fin 5 => decide (k = i ∨ k = j)) false)) = _
  have hin : ∀ i j : Fin 5,
      (Fin.snoc (fun k : Fin 5 => decide (k = i ∨ k = j)) false : Fin 6 → Bool) =
        (fun k : Fin 6 => decide (k = i.castSucc ∨ k = j.castSucc)) := by decide +kernel
  rw [hin i j, heval]
  have hbits : ∀ i j : Fin 5,
      (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) =
        (4443 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel
  exact hbits i j

end PEqualNP.Outside.L_meta_24717_aux

namespace PEqualNP.Outside.L_meta_24717_aux.Circ

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

section Live

variable {α : Type} [DecidableEq α] (bop : α → α → Finset α) (uop : α → Finset α) (goal : α)

def build : ℕ → Finset α → Prop
  | 0, av => goal ∈ av
  | k + 1, av => build k av ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ bop a b, build k (insert z av)) ∨
      (∃ a ∈ av, ∃ z ∈ uop a, build k (insert z av))

def live : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live k s ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ bop a b, z ∉ s ∧
        ∃ rest : Finset α, s = insert a (insert b rest) ∧ live k (insert z rest)) ∨
      (∃ a ∈ s, ∃ z ∈ uop a, z ∉ s ∧
        ∃ rest : Finset α, s = insert a rest ∧ live k (insert z rest))

variable {bop uop goal}

lemma compress {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∃ s ⊆ av, live bop uop goal k s := by
  induction k generalizing av with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩ | ⟨a, ha, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr (Or.inl ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨s, hs, Or.inr (Or.inr ⟨a, by simp [s], z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

lemma live_separates (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b) (hun : ∀ a, ∀ z ∈ uop a, D z → D a)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, hun a w hz hD⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma live_tight (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) (hc : s.card = k + 1) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · have := live_card skip
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      have hc' : (insert z rest).card = k + 1 := by
        rw [Finset.card_insert_of_notMem hzrest]; omega
      obtain ⟨w, hw, hD⟩ := ih tail hc'
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

lemma build_mono {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∀ j, k ≤ j → build bop uop goal j av := by
  intro j hj
  induction hj with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Live

section Lists

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

lemma recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

lemma recover_kept1 {ws r : List ℕ} {a : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : (v ∈ insert a r.toFinset) ↔ v ∈ insert a needed := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

lemma singleton_list {ws : List ℕ} {goal : ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

lemma all_of_chunks {β : Type} (L : List β) (f : β → Bool) (B n : ℕ) (hlen : L.length ≤ B * n)
    (h : ∀ i < n, ((L.drop (B * i)).take B).all f = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; rw [Nat.zero_mul] at hlen; omega
    · exact h0
  have hi : j / B < n := by
    rw [Nat.div_lt_iff_lt_mul hB]; rw [Nat.mul_comm] at hlen; omega
  have hmod := Nat.mod_lt j hB
  have hdm := Nat.div_add_mod j B
  have hc := List.all_eq_true.mp (h (j / B) hi)
  apply hc
  rw [List.mem_iff_getElem]
  refine ⟨j % B, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    all_goals omega

end Lists

section Search

def enc : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * enc l

lemma testBit_enc (l : List Bool) (i : ℕ) : (enc l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [enc]
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [enc, Nat.testBit_zero, List.getD_cons_zero]
      cases b <;> simp <;> omega
    | succ i =>
      rw [Nat.testBit_add_one, List.getD_cons_succ, ← ih i]
      congr 1
      simp only [enc]
      cases b <;> simp <;> omega

def maskN (N : ℕ) : ℕ := enc (List.replicate N true)

lemma maskN_testBit (N r : ℕ) : (maskN N).testBit r = decide (r < N) := by
  rw [maskN, testBit_enc]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : r < N <;> simp [h]

variable (goal mask : ℕ) (prs : List (ℕ × ℕ)) (N J : ℕ)

def prsOf : List (ℕ × ℕ) := (List.range J).map (fun j => (N + j, N + J + j))

def sepF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) ^^^ (w >>> (N + J)))) 0 &&& maskN J) == maskN J

def monF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) &&& (maskN J ^^^ (w >>> (N + J))))) 0 &&& maskN J)
    == maskN J

lemma foldr_or_testBit (f : ℕ → ℕ) (ws : List ℕ) (i : ℕ) :
    (ws.foldr (fun w acc => acc ||| f w) 0).testBit i = ws.any (fun w => (f w).testBit i) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]
    exact Bool.or_comm _ _

def bop (a b : ℕ) : Finset ℕ := {a &&& b, a ||| b}
def uop (a : ℕ) : Finset ℕ := {mask ^^^ a}

def sepOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 != w.testBit pq.2))

def monOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 && !w.testBit pq.2))

lemma sepF_of {ws : List ℕ} (h : sepOK (prsOf N J) ws = true) : sepF N J ws = true := by
  simp only [sepOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, bne_iff_ne] at h
  simp only [sepF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    revert hd
    cases w.testBit (N + i) <;> cases w.testBit (N + J + i) <;> simp
  · simp [hi]

lemma monF_of {ws : List ℕ} (h : monOK (prsOf N J) ws = true) : monF N J ws = true := by
  simp only [monOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp only [monF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd1, hd2⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      maskN_testBit, hd1, hd2]
    simp [hi]
  · simp [hi]

variable (nt : Bool)

def uopN (a : ℕ) : Finset ℕ := if nt then {mask ^^^ a} else ∅

def chk (k : ℕ) (ws : List ℕ) : Bool :=
  decide (ws.length ≤ k + 2) && sepF N J ws && ((nt && ws.length != k + 2) || monF N J ws)

def LS : ℕ → List ℕ → Bool
  | 0, ws => ws == [goal]
  | k + 1, ws => ws == [goal] ||
      (chk N J nt k ws &&
        ((pairs ws).any (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].any (fun z =>
            !ws.contains z && (keepChoices t.1 t.2.1 t.2.2).any (fun kept => LS k (z :: kept)))) ||
         (nt && (singles ws).any (fun t => !ws.contains (mask ^^^ t.1) &&
            [t.2, t.1 :: t.2].any (fun kept => LS k ((mask ^^^ t.1) :: kept))))))

lemma chk_mono {k : ℕ} {ws : List ℕ} (h : chk N J nt k ws = true) : chk N J nt (k + 1) ws = true := by
  simp only [chk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by omega, h2⟩, ?_⟩
  rcases h3 with ⟨hn, hl⟩ | h
  · exact Or.inl ⟨hn, by omega⟩
  · exact Or.inr h

lemma LS_mono : ∀ k ws, LS goal mask N J nt k ws = true → LS goal mask N J nt (k + 1) ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws h
    simp only [LS] at h ⊢
    simp [h]
  | succ k ih =>
    intro ws h
    rw [LS] at h
    rw [LS]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨hc, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨chk_mono N J nt hc, ?_⟩
      rcases h with ⟨t, ht, z, hz, hc, kept, hk, hr⟩ | ⟨hnt, t, ht, hc, kept, hk, hr⟩
      · exact Or.inl ⟨t, ht, z, hz, hc, kept, hk, ih _ hr⟩
      · exact Or.inr ⟨hnt, t, ht, hc, kept, hk, ih _ hr⟩

lemma bop_comm (a b : ℕ) : bop a b = bop b a := by
  simp [bop, Nat.land_comm, Nat.lor_comm, Finset.pair_comm]

def Dpq (pq : ℕ × ℕ) (w : ℕ) : Prop := w.testBit pq.1 ≠ w.testBit pq.2

lemma bop_D (pq : ℕ × ℕ) (a b z : ℕ) (hz : z ∈ bop a b) (hdz : Dpq pq z) : Dpq pq a ∨ Dpq pq b := by
  simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
  unfold Dpq at hdz ⊢
  rcases hz with rfl | rfl <;> revert hdz <;>
    simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
    cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp

lemma bop_O (pq : ℕ × ℕ) (a b z : ℕ) (hz : z ∈ bop a b)
    (hdz : z.testBit pq.1 = true ∧ z.testBit pq.2 = false) :
    (a.testBit pq.1 = true ∧ a.testBit pq.2 = false) ∨
      (b.testBit pq.1 = true ∧ b.testBit pq.2 = false) := by
  simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> revert hdz <;>
    simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
    cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp

lemma sep_of_live (hD : ∀ pq ∈ prs, Dpq pq goal)
    (hM : ∀ pq ∈ prs, mask.testBit pq.1 = mask.testBit pq.2)
    {k : ℕ} {ws : List ℕ} (h : live bop (uopN mask nt) goal k ws.toFinset) :
    sepOK prs ws = true := by
  simp only [sepOK, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro pq hpq
  obtain ⟨w, hw, hd⟩ := live_separates (Dpq pq) (hD pq hpq) (bop_D pq)
    (by
      intro a z hz hdz
      unfold uopN at hz
      split at hz
      · simp only [Finset.mem_singleton] at hz
        subst hz
        unfold Dpq at hdz ⊢
        have hm := hM pq hpq
        revert hdz
        simp only [Nat.testBit_xor, hm]
        cases mask.testBit pq.2 <;> cases a.testBit pq.1 <;> cases a.testBit pq.2 <;> simp
      · simp at hz) h
  exact ⟨w, List.mem_toFinset.mp hw, hd⟩

lemma mon_of_live (hO : ∀ pq ∈ prs, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup) (h : live bop (uopN mask nt) goal k ws.toFinset)
    (hc : nt = false ∨ ws.length = k + 1) : monOK prs ws = true := by
  simp only [monOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  intro pq hpq
  rcases hc with hnt | hc
  · obtain ⟨w, hw, hd⟩ := live_separates (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
      (hO pq hpq) (bop_O pq) (by intro a z hz; simp [uopN, hnt] at hz) h
    exact ⟨w, List.mem_toFinset.mp hw, hd⟩
  · obtain ⟨w, hw, hd⟩ := live_tight (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
      (hO pq hpq) (bop_O pq) h (by rw [List.toFinset_card_of_nodup hn, hc])
    exact ⟨w, List.mem_toFinset.mp hw, hd⟩

lemma chk_of_live (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup)
    (h : live bop (uopN mask nt) goal (k + 1) ws.toFinset) : chk N J nt k ws = true := by
  have hcard := live_card h
  rw [List.toFinset_card_of_nodup hn] at hcard
  have hsep := sepF_of N J (sep_of_live goal mask (prsOf N J) nt hD hM h)
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne]
  refine ⟨⟨hcard, hsep⟩, ?_⟩
  by_cases hnt : nt = true
  · by_cases hl : ws.length = k + 2
    · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) nt hO hn h (Or.inr hl)))
    · exact Or.inl ⟨hnt, hl⟩
  · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) nt hO hn h
      (Or.inl (by simpa using hnt))))

lemma LS_complete (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) :
    ∀ k (ws : List ℕ), ws.Nodup → live bop (uopN mask nt) goal k ws.toFinset →
      LS goal mask N J nt k ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    simp [LS, singleton_list hn h]
  | succ k ih =>
    intro ws hn h
    have hchk := chk_of_live goal mask N J nt hD hM hO hn h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩ |
        ⟨a, ha, z, hz, hout, needed, hs, tail⟩
    · exact LS_mono goal mask N J nt k ws (ih ws hn skip)
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have hzc : ws.contains z = false := by
        simpa using fun hh => hout (List.mem_toFinset.mpr hh)
      have go {a b : ℕ} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ bop a b) :
          [a &&& b, a ||| b].any (fun z =>
            !ws.contains z && (keepChoices a b r).any (fun kept => LS goal mask N J nt k (z :: kept)))
            = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uopN mask nt) goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨z, ?_, hzc, kept, hk, hrec⟩
        simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hop
        rcases hop with rfl | rfl <;> simp
      simp only [LS, Bool.or_eq_true, Bool.and_eq_true]
      right
      refine ⟨hchk, Or.inl ?_⟩
      simp only [List.any_eq_true]
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, by simpa using go hp hs hz⟩
      · exact ⟨(b, a, r), swap, by
          simpa using go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
            (bop_comm a b ▸ hz)⟩
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      by_cases hnt : nt = true
      · simp only [uopN, hnt, if_true, Finset.mem_singleton] at hz
        subst hz
        have hzc : ws.contains (mask ^^^ a) = false := by
          simpa using fun hh => hout (List.mem_toFinset.mpr hh)
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
        have hznew : (mask ^^^ a) ∉ kept := by
          intro hu
          apply hout
          rw [hs]
          exact Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu))
        have hnd : ((mask ^^^ a) :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uopN mask nt) goal k ((mask ^^^ a) :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [LS, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hchk, Or.inr ⟨hnt, ?_⟩⟩
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨(a, r), hm, hzc, kept, hk, hrec⟩
      · simp [uopN, hnt] at hz

def kidsN (ws : List ℕ) : List (List ℕ) :=
  (pairs ws).flatMap (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].flatMap (fun z =>
      if ws.contains z then [] else (keepChoices t.1 t.2.1 t.2.2).map (fun kept => z :: kept))) ++
  (if nt then (singles ws).flatMap (fun t =>
      if ws.contains (mask ^^^ t.1) then [] else
        [t.2, t.1 :: t.2].map (fun kept => (mask ^^^ t.1) :: kept)) else [])

def expand (k : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  L.flatMap (fun ws => if chk N J nt k ws then kidsN mask nt ws else [])

lemma LS_split {k : ℕ} {ws : List ℕ} (h : LS goal mask N J nt (k + 1) ws = true) :
    ws = [goal] ∨ ∃ c ∈ kidsN mask nt ws, chk N J nt k ws = true ∧ LS goal mask N J nt k c = true := by
  rw [LS] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨hc, ⟨t, ht, z, hz, hzc, kept, hk, hr⟩ | ⟨hnt, t, ht, hzc, kept, hk, hr⟩⟩
  · exact Or.inl h
  · right
    refine ⟨z :: kept, ?_, hc, hr⟩
    unfold kidsN
    apply List.mem_append_left
    rw [List.mem_flatMap]
    refine ⟨t, ht, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨z, hz, ?_⟩
    rw [hzc]
    exact List.mem_map.mpr ⟨kept, hk, rfl⟩
  · right
    refine ⟨(mask ^^^ t.1) :: kept, ?_, hc, hr⟩
    unfold kidsN
    apply List.mem_append_right
    rw [hnt, if_pos rfl, List.mem_flatMap]
    refine ⟨t, ht, ?_⟩
    rw [hzc]
    exact List.mem_map.mpr ⟨kept, hk, rfl⟩

lemma split_all (k : ℕ) (L : List (List ℕ)) (h1 : L.all (fun ws => !(ws == [goal])) = true)
    (h2 : (expand mask N J nt k L).all (fun c => !LS goal mask N J nt k c) = true) :
    L.all (fun ws => !LS goal mask N J nt (k + 1) ws) = true := by
  rw [List.all_eq_true]
  intro ws hws
  cases e : LS goal mask N J nt (k + 1) ws
  · rfl
  · exfalso
    rcases LS_split goal mask N J nt e with hg | ⟨c, hc, hck, hl⟩
    · have := List.all_eq_true.mp h1 ws hws
      simp [hg] at this
    · have hmem : c ∈ expand mask N J nt k L := by
        unfold expand
        rw [List.mem_flatMap]
        exact ⟨ws, hws, by rw [hck, if_pos rfl]; exact hc⟩
      have := List.all_eq_true.mp h2 c hmem
      simp [hl] at this

end Search

section Circ

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def beh (W : List (List Bool)) (i : ℕ) : ℕ := enc (W.map fun w => w.getD i false)

lemma getD_map_row (W : List (List Bool)) (i r : ℕ) :
    (W.map fun w => w.getD i false).getD r false = (W.getD r []).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[r]? <;> simp

lemma beh_testBit (W : List (List Bool)) (i r : ℕ) :
    (beh W i).testBit r = (W.getD r []).getD i false := by
  rw [beh, testBit_enc, getD_map_row]

lemma row_of_lt {W : List (List Bool)} {r : ℕ} (h : r < W.length) :
    W.getD r [] ∈ W := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

lemma row_of_ge {W : List (List Bool)} {r : ℕ} (h : W.length ≤ r) : W.getD r [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_step_ne {w : List Bool} {g : Gate} {i : ℕ} (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma getD_step_eq {w : List Bool} {g : Gate} :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

lemma mapstep_row (W : List (List Bool)) (g : Gate) (r : ℕ) :
    (W.map (fun w => step w g)).getD r [] =
      if r < W.length then step (W.getD r []) g else [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : r < W.length
  · simp [h, List.getElem?_eq_getElem h]
  · simp [h, List.getElem?_eq_none (Nat.le_of_not_lt h)]

lemma beh_old {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) (g : Gate) {i : ℕ}
    (hi : i ≠ L) : beh (W.map (fun w => step w g)) i = beh W i := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    rw [getD_step_ne (by rw [hl _ (row_of_lt h)]; exact hi)]
  · simp only [h, ↓reduceIte]
    rw [row_of_ge (Nat.le_of_not_lt h)]

lemma beh_beyond {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) {i : ℕ}
    (hi : L ≤ i) : beh W i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, Nat.zero_testBit]
  by_cases h : r < W.length
  · have h2 : (W.getD r []).length ≤ i := by rw [hl _ (row_of_lt h)]; exact hi
    exact List.getD_eq_default _ _ h2
  · rw [row_of_ge (Nat.le_of_not_lt h)]
    rfl

def okGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma beh_new {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (g : Gate) (z : ℕ)
    (hz : ∀ r, (r < N → z.testBit r =
        g.op.eval (g.inputs.map fun i => (W.getD r []).getD i false)) ∧
      (N ≤ r → z.testBit r = false)) :
    beh (W.map (fun w => step w g)) L = z := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    have hm := row_of_lt h
    have := getD_step_eq (w := W.getD r []) (g := g)
    rw [hl _ hm] at this
    rw [this, (hz r).1 (hN ▸ h)]
  · simp only [h, ↓reduceIte]
    rw [(hz r).2 (by omega)]
    rfl

lemma gate_step {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (av : Finset ℕ) (hmask : maskN N ∈ av) (hinv : ∀ i, beh W i ∈ av)
    (g : Gate) (hg : okGate g) :
    ∃ z, (z ∈ av ∨ (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ z ∈ bop a b) ∨
        (g.op = GateOp.not ∧ ∃ a ∈ av, z ∈ uop (maskN N) a)) ∧
      beh (W.map (fun w => step w g)) L = z := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  have hbeyond := beh_beyond hl (le_refl L)
  have hi : ∀ i r, N ≤ r → (beh W i).testBit r = false := by
    intro i r hr
    rw [beh_testBit, row_of_ge (by omega)]
    rfl
  have hmk : ∀ r, N ≤ r → (maskN N).testBit r = false := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  have hmk' : ∀ r, r < N → (maskN N).testBit r = true := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  match inputs, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
    · refine ⟨0, Or.inl (hbeyond ▸ hinv L), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [GateOp.eval], fun _ => by simp⟩
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨rfl, beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i &&& beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.and_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_and, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_and, hi i r hr]⟩
    · refine ⟨beh W i ||| beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.or_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_or, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_or, hi i r hr, hi j r hr]⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨rfl, beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | _ :: _ :: _ :: _, h => simp at h

def stepAll (gs : List Gate) (W : List (List Bool)) : List (List Bool) :=
  gs.foldl (fun W g => W.map (fun w => step w g)) W

lemma stepAll_eq (gs : List Gate) :
    ∀ W, stepAll gs W = W.map (fun w => gs.foldl step w) := by
  induction gs with
  | nil => intro W; simp [stepAll]
  | cons g gs ih =>
    intro W
    show stepAll gs (W.map (fun w => step w g)) = _
    rw [ih, List.map_map]
    rfl

def okN (nt : Bool) (g : Gate) : Prop := okGate g ∧ (nt = false → g.op ≠ GateOp.not)

lemma to_buildN (nt : Bool) (N goal : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, okN nt g) :
    ∀ (L : ℕ) (W : List (List Bool)) (av : Finset ℕ), (∀ w ∈ W, w.length = L) → W.length = N →
      maskN N ∈ av → (∀ i, beh W i ∈ av) → ∀ o, beh (stepAll gs W) o = goal →
      build bop (uopN (maskN N) nt) goal gs.length av := by
  induction gs with
  | nil =>
    intro L W av _ _ _ hinv o ho
    exact ho ▸ hinv o
  | cons g gs ih =>
    intro L W av hl hN hm hinv o ho
    obtain ⟨z, hz, hbz⟩ := gate_step hl hN av hm hinv g (hg g (by simp)).1
    have hl' : ∀ w ∈ W.map (fun w => step w g), w.length = L + 1 := by
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
      simp [step, hl w0 hw0]
    have hN' : (W.map (fun w => step w g)).length = N := by simp [hN]
    have hinv' : ∀ i, beh (W.map (fun w => step w g)) i ∈ insert z av := by
      intro i
      by_cases hi : i = L
      · subst hi; rw [hbz]; exact Finset.mem_insert_self _ _
      · rw [beh_old hl g hi]; exact Finset.mem_insert_of_mem (hinv i)
    have hrec := ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) (L + 1) _ (insert z av)
      hl' hN' (Finset.mem_insert_of_mem hm) hinv' o ho
    rw [List.length_cons]
    rcases hz with hz | ⟨a, ha, b, hb, hab, hz⟩ | ⟨hop, a, ha, hz⟩
    · rw [Finset.insert_eq_of_mem hz] at hrec; exact Or.inl hrec
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, hab, z, hz, hrec⟩)
    · by_cases hnt : nt = true
      · refine Or.inr (Or.inr ⟨a, ha, z, ?_, hrec⟩)
        simp only [uop, Finset.mem_singleton] at hz
        simp [uopN, hnt, hz]
      · exact absurd hop ((hg g (by simp)).2 (by simpa using hnt))

def rowsOf (n m : ℕ) (ex : List (Fin n × Fin m)) : List (List Bool) :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => oneEach u v) ++
    ex.map (fun p => oneEach p.1 p.2)

def goalOf {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) : List Bool :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => A u v) ++
    ex.map (fun p => A p.1 p.2)

lemma rows_len (n m : ℕ) (ex : List (Fin n × Fin m)) :
    ∀ w ∈ rowsOf n m ex, w.length = n + m := by
  intro w hw
  simp only [rowsOf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and] at hw
  rcases hw with ⟨u, v, rfl⟩ | ⟨p, _, rfl⟩ <;> simp [oneEach]

lemma core (X : List (List Bool)) (L : ℕ) (hX : ∀ x ∈ X, x.length = L) (tl : List Bool)
    (nt : Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (hN : X.length = Nt) (hgoal : enc tl = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range L).all (fun i => init.contains (beh X i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J nt K l) = true)
    (C : Circuit) (hF : ∀ g ∈ C.gates, okN nt g) (hs : C.size ≤ K)
    (hev : X.map (fun x => C.eval x) = tl) : False := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_range] at hinit
  obtain ⟨⟨hinp, h0⟩, hm⟩ := hinit
  have hinv : ∀ i, beh X i ∈ init.toFinset := by
    intro i
    rw [List.mem_toFinset]
    by_cases h : i < L
    · exact hinp i h
    · rw [beh_beyond hX (Nat.le_of_not_lt h)]; exact h0
  have hfin : beh (stepAll C.gates X) C.output = goal := by
    rw [← hgoal, ← hev, beh, stepAll_eq, List.map_map]
    rfl
  have hb := to_buildN nt Nt goal C.gates hF L X init.toFinset hX hN
    (by rw [hmask]; exact List.mem_toFinset.mpr hm) hinv C.output hfin
  rw [hmask] at hb
  have hb' := build_mono hb K hs
  obtain ⟨S, hS, hlive⟩ := compress hb'
  have hall : ∀ pq ∈ prsOf Nb J, (goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) ∧
      mask.testBit pq.1 = mask.testBit pq.2 := by
    intro pq hpq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpq
    have := List.all_eq_true.mp hprs j hj
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    exact this
  have hO : ∀ pq ∈ prsOf Nb J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false :=
    fun pq hpq => (hall pq hpq).1
  have hD : ∀ pq ∈ prsOf Nb J, Dpq pq goal := by
    intro pq hpq
    have := hO pq hpq
    unfold Dpq
    rw [this.1, this.2]
    simp
  have hM : ∀ pq ∈ prsOf Nb J, mask.testBit pq.1 = mask.testBit pq.2 :=
    fun pq hpq => (hall pq hpq).2
  let l := init.filter (fun x => decide (x ∈ S))
  have hl_sub : l ∈ init.sublists := List.mem_sublists.mpr List.filter_sublist
  have hl_nd : l.Nodup := hnd.filter _
  have hl_fs : l.toFinset = S := by
    ext x
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hS h), h⟩⟩
  have hc := LS_complete goal mask Nb J nt hD hM hO K l hl_nd (hl_fs ▸ hlive)
  have hf := List.all_eq_true.mp hsearch l hl_sub
  rw [hc] at hf
  exact Bool.noConfusion hf

def twoRow (p : Fin 5 × Fin 5) : List Bool := List.ofFn fun k : Fin 5 => decide (k = p.1 ∨ k = p.2)

def twoGoal (M : ℕ) (p : Fin 5 × Fin 5) : Bool :=
  M.testBit (5 * min p.1.val p.2.val + max p.1.val p.2.val)

lemma refuteT (M K Nb J Nt goal mask : ℕ) (init : List ℕ) (ex : List (Fin 5 × Fin 5))
    (hN : (ex.map twoRow).length = Nt) (hgoal : enc (ex.map (twoGoal M)) = goal)
    (hmask : maskN Nt = mask)
    (hinit : ((List.range 5).all (fun i => init.contains (beh (ex.map twoRow) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J true K l) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧ ∀ i j : Fin 5,
      C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        M.testBit (5 * min i.val j.val + max i.val j.val) := by
  rintro ⟨C, hC, hs, hr⟩
  refine core (ex.map twoRow) 5 ?_ (ex.map (twoGoal M)) true K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C (fun g hg => ⟨hC g hg, by simp⟩) hs ?_
  · intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    simp [twoRow]
  · rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact hr p.1 p.2

end Circ

def G : ℕ := 2147483647
def MK : ℕ := 4611686018427387903
def I : List ℕ := [72058734351810559, 151299491574513678, 1092293522884657152, 1504810168065458672, 2924371712051052032, 0, 4611686018427387903]
def E : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 1), (0, 1), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (1, 1), (1, 1), (1, 1), (1, 1), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (0, 2), (0, 2), (1, 2), (1, 4), (0, 2), (1, 4), (2, 3), (3, 3), (3, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 4), (4, 4), (1, 2), (1, 4), (3, 3), (4, 4), (1, 2), (1, 4), (2, 3), (3, 3), (3, 4), (0, 2), (1, 2), (2, 3), (2, 4), (3, 3), (4, 4)]

def R0 : List (List ℕ) := I.sublists

def R1 : List (List ℕ) := expand MK 0 31 true 7 R0

def Q (k : ℕ) (L : List (List ℕ)) : Bool := L.all (fun c => !LS G MK 0 31 true k c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T0 : Q 7 ((R1.drop 0).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T1 : Q 7 ((R1.drop 1).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T2 : Q 7 ((R1.drop 2).take 1) = true := by decide +kernel

def Z3 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 3).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_0 : Q 6 ((Z3.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_1 : Q 6 ((Z3.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_2 : Q 6 ((Z3.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_3 : Q 6 ((Z3.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_4 : Q 6 ((Z3.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_5 : Q 6 ((Z3.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_6 : Q 6 ((Z3.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_7 : Q 6 ((Z3.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_8 : Q 6 ((Z3.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_9 : Q 6 ((Z3.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_10 : Q 6 ((Z3.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_11 : Q 6 ((Z3.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_12 : Q 6 ((Z3.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C3_13 : Q 6 ((Z3.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S3 : Q 6 Z3 = true := by
  refine all_of_chunks Z3 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C3_0
  · exact C3_1
  · exact C3_2
  · exact C3_3
  · exact C3_4
  · exact C3_5
  · exact C3_6
  · exact C3_7
  · exact C3_8
  · exact C3_9
  · exact C3_10
  · exact C3_11
  · exact C3_12
  · exact C3_13

def T3 : Q 7 ((R1.drop 3).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 3).take 1) (by decide +kernel) S3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T4 : Q 7 ((R1.drop 4).take 1) = true := by decide +kernel

def Z5 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 5).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_0 : Q 6 ((Z5.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_1 : Q 6 ((Z5.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_2 : Q 6 ((Z5.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_3 : Q 6 ((Z5.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_4 : Q 6 ((Z5.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_5 : Q 6 ((Z5.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_6 : Q 6 ((Z5.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_7 : Q 6 ((Z5.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_8 : Q 6 ((Z5.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_9 : Q 6 ((Z5.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_10 : Q 6 ((Z5.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_11 : Q 6 ((Z5.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_12 : Q 6 ((Z5.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_13 : Q 6 ((Z5.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_14 : Q 6 ((Z5.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_15 : Q 6 ((Z5.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_16 : Q 6 ((Z5.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_17 : Q 6 ((Z5.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_18 : Q 6 ((Z5.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_19 : Q 6 ((Z5.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_20 : Q 6 ((Z5.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_21 : Q 6 ((Z5.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_22 : Q 6 ((Z5.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_23 : Q 6 ((Z5.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_24 : Q 6 ((Z5.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_25 : Q 6 ((Z5.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_26 : Q 6 ((Z5.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_27 : Q 6 ((Z5.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_28 : Q 6 ((Z5.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_29 : Q 6 ((Z5.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_30 : Q 6 ((Z5.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_31 : Q 6 ((Z5.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_32 : Q 6 ((Z5.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_33 : Q 6 ((Z5.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_34 : Q 6 ((Z5.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_35 : Q 6 ((Z5.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_36 : Q 6 ((Z5.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_37 : Q 6 ((Z5.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_38 : Q 6 ((Z5.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_39 : Q 6 ((Z5.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C5_40 : Q 6 ((Z5.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S5 : Q 6 Z5 = true := by
  refine all_of_chunks Z5 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C5_0
  · exact C5_1
  · exact C5_2
  · exact C5_3
  · exact C5_4
  · exact C5_5
  · exact C5_6
  · exact C5_7
  · exact C5_8
  · exact C5_9
  · exact C5_10
  · exact C5_11
  · exact C5_12
  · exact C5_13
  · exact C5_14
  · exact C5_15
  · exact C5_16
  · exact C5_17
  · exact C5_18
  · exact C5_19
  · exact C5_20
  · exact C5_21
  · exact C5_22
  · exact C5_23
  · exact C5_24
  · exact C5_25
  · exact C5_26
  · exact C5_27
  · exact C5_28
  · exact C5_29
  · exact C5_30
  · exact C5_31
  · exact C5_32
  · exact C5_33
  · exact C5_34
  · exact C5_35
  · exact C5_36
  · exact C5_37
  · exact C5_38
  · exact C5_39
  · exact C5_40

def T5 : Q 7 ((R1.drop 5).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 5).take 1) (by decide +kernel) S5

def Z6 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 6).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_0 : Q 6 ((Z6.drop 0).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_1 : Q 6 ((Z6.drop 4).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_2 : Q 6 ((Z6.drop 8).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_3 : Q 6 ((Z6.drop 12).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_4 : Q 6 ((Z6.drop 16).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_5 : Q 6 ((Z6.drop 20).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_6 : Q 6 ((Z6.drop 24).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_7 : Q 6 ((Z6.drop 28).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_8 : Q 6 ((Z6.drop 32).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_9 : Q 6 ((Z6.drop 36).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_10 : Q 6 ((Z6.drop 40).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_11 : Q 6 ((Z6.drop 44).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_12 : Q 6 ((Z6.drop 48).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_13 : Q 6 ((Z6.drop 52).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_14 : Q 6 ((Z6.drop 56).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_15 : Q 6 ((Z6.drop 60).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_16 : Q 6 ((Z6.drop 64).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_17 : Q 6 ((Z6.drop 68).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_18 : Q 6 ((Z6.drop 72).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_19 : Q 6 ((Z6.drop 76).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C6_20 : Q 6 ((Z6.drop 80).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S6 : Q 6 Z6 = true := by
  refine all_of_chunks Z6 (fun c => !LS G MK 0 31 true 6 c) 4 21 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C6_0
  · exact C6_1
  · exact C6_2
  · exact C6_3
  · exact C6_4
  · exact C6_5
  · exact C6_6
  · exact C6_7
  · exact C6_8
  · exact C6_9
  · exact C6_10
  · exact C6_11
  · exact C6_12
  · exact C6_13
  · exact C6_14
  · exact C6_15
  · exact C6_16
  · exact C6_17
  · exact C6_18
  · exact C6_19
  · exact C6_20

def T6 : Q 7 ((R1.drop 6).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 6).take 1) (by decide +kernel) S6

def Z7 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 7).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_0 : Q 6 ((Z7.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_1 : Q 6 ((Z7.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_2 : Q 6 ((Z7.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_3 : Q 6 ((Z7.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_4 : Q 6 ((Z7.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_5 : Q 6 ((Z7.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_6 : Q 6 ((Z7.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_7 : Q 6 ((Z7.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_8 : Q 6 ((Z7.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_9 : Q 6 ((Z7.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_10 : Q 6 ((Z7.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_11 : Q 6 ((Z7.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_12 : Q 6 ((Z7.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C7_13 : Q 6 ((Z7.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S7 : Q 6 Z7 = true := by
  refine all_of_chunks Z7 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C7_0
  · exact C7_1
  · exact C7_2
  · exact C7_3
  · exact C7_4
  · exact C7_5
  · exact C7_6
  · exact C7_7
  · exact C7_8
  · exact C7_9
  · exact C7_10
  · exact C7_11
  · exact C7_12
  · exact C7_13

def T7 : Q 7 ((R1.drop 7).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 7).take 1) (by decide +kernel) S7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T8 : Q 7 ((R1.drop 8).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T9 : Q 7 ((R1.drop 9).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T10 : Q 7 ((R1.drop 10).take 1) = true := by decide +kernel

def Z11 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 11).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_0 : Q 6 ((Z11.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_1 : Q 6 ((Z11.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_2 : Q 6 ((Z11.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_3 : Q 6 ((Z11.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_4 : Q 6 ((Z11.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_5 : Q 6 ((Z11.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_6 : Q 6 ((Z11.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_7 : Q 6 ((Z11.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_8 : Q 6 ((Z11.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_9 : Q 6 ((Z11.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_10 : Q 6 ((Z11.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_11 : Q 6 ((Z11.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_12 : Q 6 ((Z11.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C11_13 : Q 6 ((Z11.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S11 : Q 6 Z11 = true := by
  refine all_of_chunks Z11 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C11_0
  · exact C11_1
  · exact C11_2
  · exact C11_3
  · exact C11_4
  · exact C11_5
  · exact C11_6
  · exact C11_7
  · exact C11_8
  · exact C11_9
  · exact C11_10
  · exact C11_11
  · exact C11_12
  · exact C11_13

def T11 : Q 7 ((R1.drop 11).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 11).take 1) (by decide +kernel) S11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T12 : Q 7 ((R1.drop 12).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T13 : Q 7 ((R1.drop 13).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T14 : Q 7 ((R1.drop 14).take 1) = true := by decide +kernel

def Z15 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 15).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_0 : Q 6 ((Z15.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_1 : Q 6 ((Z15.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_2 : Q 6 ((Z15.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_3 : Q 6 ((Z15.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_4 : Q 6 ((Z15.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_5 : Q 6 ((Z15.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_6 : Q 6 ((Z15.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_7 : Q 6 ((Z15.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_8 : Q 6 ((Z15.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_9 : Q 6 ((Z15.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_10 : Q 6 ((Z15.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_11 : Q 6 ((Z15.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_12 : Q 6 ((Z15.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C15_13 : Q 6 ((Z15.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S15 : Q 6 Z15 = true := by
  refine all_of_chunks Z15 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C15_0
  · exact C15_1
  · exact C15_2
  · exact C15_3
  · exact C15_4
  · exact C15_5
  · exact C15_6
  · exact C15_7
  · exact C15_8
  · exact C15_9
  · exact C15_10
  · exact C15_11
  · exact C15_12
  · exact C15_13

def T15 : Q 7 ((R1.drop 15).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 15).take 1) (by decide +kernel) S15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T16 : Q 7 ((R1.drop 16).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T17 : Q 7 ((R1.drop 17).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T18 : Q 7 ((R1.drop 18).take 1) = true := by decide +kernel

def Z19 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 19).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_0 : Q 6 ((Z19.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_1 : Q 6 ((Z19.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_2 : Q 6 ((Z19.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_3 : Q 6 ((Z19.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_4 : Q 6 ((Z19.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_5 : Q 6 ((Z19.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_6 : Q 6 ((Z19.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_7 : Q 6 ((Z19.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_8 : Q 6 ((Z19.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_9 : Q 6 ((Z19.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_10 : Q 6 ((Z19.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_11 : Q 6 ((Z19.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_12 : Q 6 ((Z19.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C19_13 : Q 6 ((Z19.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S19 : Q 6 Z19 = true := by
  refine all_of_chunks Z19 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C19_0
  · exact C19_1
  · exact C19_2
  · exact C19_3
  · exact C19_4
  · exact C19_5
  · exact C19_6
  · exact C19_7
  · exact C19_8
  · exact C19_9
  · exact C19_10
  · exact C19_11
  · exact C19_12
  · exact C19_13

def T19 : Q 7 ((R1.drop 19).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 19).take 1) (by decide +kernel) S19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T20 : Q 7 ((R1.drop 20).take 1) = true := by decide +kernel

def Z21 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 21).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_0 : Q 6 ((Z21.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_1 : Q 6 ((Z21.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_2 : Q 6 ((Z21.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_3 : Q 6 ((Z21.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_4 : Q 6 ((Z21.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_5 : Q 6 ((Z21.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_6 : Q 6 ((Z21.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_7 : Q 6 ((Z21.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_8 : Q 6 ((Z21.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_9 : Q 6 ((Z21.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_10 : Q 6 ((Z21.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_11 : Q 6 ((Z21.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_12 : Q 6 ((Z21.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_13 : Q 6 ((Z21.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_14 : Q 6 ((Z21.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_15 : Q 6 ((Z21.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_16 : Q 6 ((Z21.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_17 : Q 6 ((Z21.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_18 : Q 6 ((Z21.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_19 : Q 6 ((Z21.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_20 : Q 6 ((Z21.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_21 : Q 6 ((Z21.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_22 : Q 6 ((Z21.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_23 : Q 6 ((Z21.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_24 : Q 6 ((Z21.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_25 : Q 6 ((Z21.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_26 : Q 6 ((Z21.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_27 : Q 6 ((Z21.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_28 : Q 6 ((Z21.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_29 : Q 6 ((Z21.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_30 : Q 6 ((Z21.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_31 : Q 6 ((Z21.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_32 : Q 6 ((Z21.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_33 : Q 6 ((Z21.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_34 : Q 6 ((Z21.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_35 : Q 6 ((Z21.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_36 : Q 6 ((Z21.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_37 : Q 6 ((Z21.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_38 : Q 6 ((Z21.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_39 : Q 6 ((Z21.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C21_40 : Q 6 ((Z21.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S21 : Q 6 Z21 = true := by
  refine all_of_chunks Z21 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C21_0
  · exact C21_1
  · exact C21_2
  · exact C21_3
  · exact C21_4
  · exact C21_5
  · exact C21_6
  · exact C21_7
  · exact C21_8
  · exact C21_9
  · exact C21_10
  · exact C21_11
  · exact C21_12
  · exact C21_13
  · exact C21_14
  · exact C21_15
  · exact C21_16
  · exact C21_17
  · exact C21_18
  · exact C21_19
  · exact C21_20
  · exact C21_21
  · exact C21_22
  · exact C21_23
  · exact C21_24
  · exact C21_25
  · exact C21_26
  · exact C21_27
  · exact C21_28
  · exact C21_29
  · exact C21_30
  · exact C21_31
  · exact C21_32
  · exact C21_33
  · exact C21_34
  · exact C21_35
  · exact C21_36
  · exact C21_37
  · exact C21_38
  · exact C21_39
  · exact C21_40

def T21 : Q 7 ((R1.drop 21).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 21).take 1) (by decide +kernel) S21

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T22 : Q 7 ((R1.drop 22).take 1) = true := by decide +kernel

def Z23 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 23).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_0 : Q 6 ((Z23.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_1 : Q 6 ((Z23.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_2 : Q 6 ((Z23.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_3 : Q 6 ((Z23.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_4 : Q 6 ((Z23.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_5 : Q 6 ((Z23.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_6 : Q 6 ((Z23.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_7 : Q 6 ((Z23.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_8 : Q 6 ((Z23.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_9 : Q 6 ((Z23.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_10 : Q 6 ((Z23.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_11 : Q 6 ((Z23.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_12 : Q 6 ((Z23.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C23_13 : Q 6 ((Z23.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S23 : Q 6 Z23 = true := by
  refine all_of_chunks Z23 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C23_0
  · exact C23_1
  · exact C23_2
  · exact C23_3
  · exact C23_4
  · exact C23_5
  · exact C23_6
  · exact C23_7
  · exact C23_8
  · exact C23_9
  · exact C23_10
  · exact C23_11
  · exact C23_12
  · exact C23_13

def T23 : Q 7 ((R1.drop 23).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 23).take 1) (by decide +kernel) S23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T24 : Q 7 ((R1.drop 24).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T25 : Q 7 ((R1.drop 25).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T26 : Q 7 ((R1.drop 26).take 1) = true := by decide +kernel

def Z27 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 27).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_0 : Q 6 ((Z27.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_1 : Q 6 ((Z27.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_2 : Q 6 ((Z27.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_3 : Q 6 ((Z27.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_4 : Q 6 ((Z27.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_5 : Q 6 ((Z27.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_6 : Q 6 ((Z27.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_7 : Q 6 ((Z27.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_8 : Q 6 ((Z27.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_9 : Q 6 ((Z27.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_10 : Q 6 ((Z27.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_11 : Q 6 ((Z27.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_12 : Q 6 ((Z27.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C27_13 : Q 6 ((Z27.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S27 : Q 6 Z27 = true := by
  refine all_of_chunks Z27 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C27_0
  · exact C27_1
  · exact C27_2
  · exact C27_3
  · exact C27_4
  · exact C27_5
  · exact C27_6
  · exact C27_7
  · exact C27_8
  · exact C27_9
  · exact C27_10
  · exact C27_11
  · exact C27_12
  · exact C27_13

def T27 : Q 7 ((R1.drop 27).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 27).take 1) (by decide +kernel) S27

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T28 : Q 7 ((R1.drop 28).take 1) = true := by decide +kernel

def Z29 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 29).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_0 : Q 6 ((Z29.drop 0).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_1 : Q 6 ((Z29.drop 4).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_2 : Q 6 ((Z29.drop 8).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_3 : Q 6 ((Z29.drop 12).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_4 : Q 6 ((Z29.drop 16).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_5 : Q 6 ((Z29.drop 20).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_6 : Q 6 ((Z29.drop 24).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_7 : Q 6 ((Z29.drop 28).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_8 : Q 6 ((Z29.drop 32).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_9 : Q 6 ((Z29.drop 36).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_10 : Q 6 ((Z29.drop 40).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_11 : Q 6 ((Z29.drop 44).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_12 : Q 6 ((Z29.drop 48).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_13 : Q 6 ((Z29.drop 52).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_14 : Q 6 ((Z29.drop 56).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_15 : Q 6 ((Z29.drop 60).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_16 : Q 6 ((Z29.drop 64).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_17 : Q 6 ((Z29.drop 68).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_18 : Q 6 ((Z29.drop 72).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_19 : Q 6 ((Z29.drop 76).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C29_20 : Q 6 ((Z29.drop 80).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S29 : Q 6 Z29 = true := by
  refine all_of_chunks Z29 (fun c => !LS G MK 0 31 true 6 c) 4 21 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C29_0
  · exact C29_1
  · exact C29_2
  · exact C29_3
  · exact C29_4
  · exact C29_5
  · exact C29_6
  · exact C29_7
  · exact C29_8
  · exact C29_9
  · exact C29_10
  · exact C29_11
  · exact C29_12
  · exact C29_13
  · exact C29_14
  · exact C29_15
  · exact C29_16
  · exact C29_17
  · exact C29_18
  · exact C29_19
  · exact C29_20

def T29 : Q 7 ((R1.drop 29).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 29).take 1) (by decide +kernel) S29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T30 : Q 7 ((R1.drop 30).take 1) = true := by decide +kernel

def Z31 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 31).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_0 : Q 6 ((Z31.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_1 : Q 6 ((Z31.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_2 : Q 6 ((Z31.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_3 : Q 6 ((Z31.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_4 : Q 6 ((Z31.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_5 : Q 6 ((Z31.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_6 : Q 6 ((Z31.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_7 : Q 6 ((Z31.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_8 : Q 6 ((Z31.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_9 : Q 6 ((Z31.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_10 : Q 6 ((Z31.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_11 : Q 6 ((Z31.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_12 : Q 6 ((Z31.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C31_13 : Q 6 ((Z31.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S31 : Q 6 Z31 = true := by
  refine all_of_chunks Z31 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C31_0
  · exact C31_1
  · exact C31_2
  · exact C31_3
  · exact C31_4
  · exact C31_5
  · exact C31_6
  · exact C31_7
  · exact C31_8
  · exact C31_9
  · exact C31_10
  · exact C31_11
  · exact C31_12
  · exact C31_13

def T31 : Q 7 ((R1.drop 31).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 31).take 1) (by decide +kernel) S31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T32 : Q 7 ((R1.drop 32).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T33 : Q 7 ((R1.drop 33).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T34 : Q 7 ((R1.drop 34).take 1) = true := by decide +kernel

def Z35 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 35).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_0 : Q 6 ((Z35.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_1 : Q 6 ((Z35.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_2 : Q 6 ((Z35.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_3 : Q 6 ((Z35.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_4 : Q 6 ((Z35.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_5 : Q 6 ((Z35.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_6 : Q 6 ((Z35.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_7 : Q 6 ((Z35.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_8 : Q 6 ((Z35.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_9 : Q 6 ((Z35.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_10 : Q 6 ((Z35.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_11 : Q 6 ((Z35.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_12 : Q 6 ((Z35.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C35_13 : Q 6 ((Z35.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S35 : Q 6 Z35 = true := by
  refine all_of_chunks Z35 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C35_0
  · exact C35_1
  · exact C35_2
  · exact C35_3
  · exact C35_4
  · exact C35_5
  · exact C35_6
  · exact C35_7
  · exact C35_8
  · exact C35_9
  · exact C35_10
  · exact C35_11
  · exact C35_12
  · exact C35_13

def T35 : Q 7 ((R1.drop 35).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 35).take 1) (by decide +kernel) S35

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T36 : Q 7 ((R1.drop 36).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T37 : Q 7 ((R1.drop 37).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T38 : Q 7 ((R1.drop 38).take 1) = true := by decide +kernel

def Z39 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 39).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_0 : Q 6 ((Z39.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_1 : Q 6 ((Z39.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_2 : Q 6 ((Z39.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_3 : Q 6 ((Z39.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_4 : Q 6 ((Z39.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_5 : Q 6 ((Z39.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_6 : Q 6 ((Z39.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_7 : Q 6 ((Z39.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_8 : Q 6 ((Z39.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_9 : Q 6 ((Z39.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_10 : Q 6 ((Z39.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_11 : Q 6 ((Z39.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_12 : Q 6 ((Z39.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C39_13 : Q 6 ((Z39.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S39 : Q 6 Z39 = true := by
  refine all_of_chunks Z39 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C39_0
  · exact C39_1
  · exact C39_2
  · exact C39_3
  · exact C39_4
  · exact C39_5
  · exact C39_6
  · exact C39_7
  · exact C39_8
  · exact C39_9
  · exact C39_10
  · exact C39_11
  · exact C39_12
  · exact C39_13

def T39 : Q 7 ((R1.drop 39).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 39).take 1) (by decide +kernel) S39

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T40 : Q 7 ((R1.drop 40).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T41 : Q 7 ((R1.drop 41).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T42 : Q 7 ((R1.drop 42).take 1) = true := by decide +kernel

def Z43 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 43).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_0 : Q 6 ((Z43.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_1 : Q 6 ((Z43.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_2 : Q 6 ((Z43.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_3 : Q 6 ((Z43.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_4 : Q 6 ((Z43.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_5 : Q 6 ((Z43.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_6 : Q 6 ((Z43.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_7 : Q 6 ((Z43.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_8 : Q 6 ((Z43.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_9 : Q 6 ((Z43.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_10 : Q 6 ((Z43.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_11 : Q 6 ((Z43.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_12 : Q 6 ((Z43.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C43_13 : Q 6 ((Z43.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S43 : Q 6 Z43 = true := by
  refine all_of_chunks Z43 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C43_0
  · exact C43_1
  · exact C43_2
  · exact C43_3
  · exact C43_4
  · exact C43_5
  · exact C43_6
  · exact C43_7
  · exact C43_8
  · exact C43_9
  · exact C43_10
  · exact C43_11
  · exact C43_12
  · exact C43_13

def T43 : Q 7 ((R1.drop 43).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 43).take 1) (by decide +kernel) S43

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T44 : Q 7 ((R1.drop 44).take 1) = true := by decide +kernel

def Z45 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 45).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_0 : Q 6 ((Z45.drop 0).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_1 : Q 6 ((Z45.drop 4).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_2 : Q 6 ((Z45.drop 8).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_3 : Q 6 ((Z45.drop 12).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_4 : Q 6 ((Z45.drop 16).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_5 : Q 6 ((Z45.drop 20).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_6 : Q 6 ((Z45.drop 24).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_7 : Q 6 ((Z45.drop 28).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_8 : Q 6 ((Z45.drop 32).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_9 : Q 6 ((Z45.drop 36).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_10 : Q 6 ((Z45.drop 40).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_11 : Q 6 ((Z45.drop 44).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_12 : Q 6 ((Z45.drop 48).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_13 : Q 6 ((Z45.drop 52).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_14 : Q 6 ((Z45.drop 56).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_15 : Q 6 ((Z45.drop 60).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_16 : Q 6 ((Z45.drop 64).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_17 : Q 6 ((Z45.drop 68).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_18 : Q 6 ((Z45.drop 72).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_19 : Q 6 ((Z45.drop 76).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C45_20 : Q 6 ((Z45.drop 80).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S45 : Q 6 Z45 = true := by
  refine all_of_chunks Z45 (fun c => !LS G MK 0 31 true 6 c) 4 21 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C45_0
  · exact C45_1
  · exact C45_2
  · exact C45_3
  · exact C45_4
  · exact C45_5
  · exact C45_6
  · exact C45_7
  · exact C45_8
  · exact C45_9
  · exact C45_10
  · exact C45_11
  · exact C45_12
  · exact C45_13
  · exact C45_14
  · exact C45_15
  · exact C45_16
  · exact C45_17
  · exact C45_18
  · exact C45_19
  · exact C45_20

def T45 : Q 7 ((R1.drop 45).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 45).take 1) (by decide +kernel) S45

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T46 : Q 7 ((R1.drop 46).take 1) = true := by decide +kernel

def Z47 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 47).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_0 : Q 6 ((Z47.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_1 : Q 6 ((Z47.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_2 : Q 6 ((Z47.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_3 : Q 6 ((Z47.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_4 : Q 6 ((Z47.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_5 : Q 6 ((Z47.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_6 : Q 6 ((Z47.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_7 : Q 6 ((Z47.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_8 : Q 6 ((Z47.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_9 : Q 6 ((Z47.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_10 : Q 6 ((Z47.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_11 : Q 6 ((Z47.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_12 : Q 6 ((Z47.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C47_13 : Q 6 ((Z47.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S47 : Q 6 Z47 = true := by
  refine all_of_chunks Z47 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C47_0
  · exact C47_1
  · exact C47_2
  · exact C47_3
  · exact C47_4
  · exact C47_5
  · exact C47_6
  · exact C47_7
  · exact C47_8
  · exact C47_9
  · exact C47_10
  · exact C47_11
  · exact C47_12
  · exact C47_13

def T47 : Q 7 ((R1.drop 47).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 47).take 1) (by decide +kernel) S47

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T48 : Q 7 ((R1.drop 48).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T49 : Q 7 ((R1.drop 49).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T50 : Q 7 ((R1.drop 50).take 1) = true := by decide +kernel

def Z51 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 51).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_0 : Q 6 ((Z51.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_1 : Q 6 ((Z51.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_2 : Q 6 ((Z51.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_3 : Q 6 ((Z51.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_4 : Q 6 ((Z51.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_5 : Q 6 ((Z51.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_6 : Q 6 ((Z51.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_7 : Q 6 ((Z51.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_8 : Q 6 ((Z51.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_9 : Q 6 ((Z51.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_10 : Q 6 ((Z51.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_11 : Q 6 ((Z51.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_12 : Q 6 ((Z51.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_13 : Q 6 ((Z51.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_14 : Q 6 ((Z51.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_15 : Q 6 ((Z51.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_16 : Q 6 ((Z51.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_17 : Q 6 ((Z51.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_18 : Q 6 ((Z51.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_19 : Q 6 ((Z51.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_20 : Q 6 ((Z51.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_21 : Q 6 ((Z51.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_22 : Q 6 ((Z51.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_23 : Q 6 ((Z51.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_24 : Q 6 ((Z51.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_25 : Q 6 ((Z51.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_26 : Q 6 ((Z51.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_27 : Q 6 ((Z51.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_28 : Q 6 ((Z51.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_29 : Q 6 ((Z51.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_30 : Q 6 ((Z51.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_31 : Q 6 ((Z51.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_32 : Q 6 ((Z51.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_33 : Q 6 ((Z51.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_34 : Q 6 ((Z51.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_35 : Q 6 ((Z51.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_36 : Q 6 ((Z51.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_37 : Q 6 ((Z51.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_38 : Q 6 ((Z51.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_39 : Q 6 ((Z51.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_40 : Q 6 ((Z51.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_41 : Q 6 ((Z51.drop 82).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_42 : Q 6 ((Z51.drop 84).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_43 : Q 6 ((Z51.drop 86).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_44 : Q 6 ((Z51.drop 88).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_45 : Q 6 ((Z51.drop 90).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_46 : Q 6 ((Z51.drop 92).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_47 : Q 6 ((Z51.drop 94).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_48 : Q 6 ((Z51.drop 96).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_49 : Q 6 ((Z51.drop 98).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_50 : Q 6 ((Z51.drop 100).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_51 : Q 6 ((Z51.drop 102).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_52 : Q 6 ((Z51.drop 104).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_53 : Q 6 ((Z51.drop 106).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_54 : Q 6 ((Z51.drop 108).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C51_55 : Q 6 ((Z51.drop 110).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S51 : Q 6 Z51 = true := by
  refine all_of_chunks Z51 (fun c => !LS G MK 0 31 true 6 c) 2 56 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C51_0
  · exact C51_1
  · exact C51_2
  · exact C51_3
  · exact C51_4
  · exact C51_5
  · exact C51_6
  · exact C51_7
  · exact C51_8
  · exact C51_9
  · exact C51_10
  · exact C51_11
  · exact C51_12
  · exact C51_13
  · exact C51_14
  · exact C51_15
  · exact C51_16
  · exact C51_17
  · exact C51_18
  · exact C51_19
  · exact C51_20
  · exact C51_21
  · exact C51_22
  · exact C51_23
  · exact C51_24
  · exact C51_25
  · exact C51_26
  · exact C51_27
  · exact C51_28
  · exact C51_29
  · exact C51_30
  · exact C51_31
  · exact C51_32
  · exact C51_33
  · exact C51_34
  · exact C51_35
  · exact C51_36
  · exact C51_37
  · exact C51_38
  · exact C51_39
  · exact C51_40
  · exact C51_41
  · exact C51_42
  · exact C51_43
  · exact C51_44
  · exact C51_45
  · exact C51_46
  · exact C51_47
  · exact C51_48
  · exact C51_49
  · exact C51_50
  · exact C51_51
  · exact C51_52
  · exact C51_53
  · exact C51_54
  · exact C51_55

def T51 : Q 7 ((R1.drop 51).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 51).take 1) (by decide +kernel) S51

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T52 : Q 7 ((R1.drop 52).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T53 : Q 7 ((R1.drop 53).take 1) = true := by decide +kernel

def Z54 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 54).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_0 : Q 6 ((Z54.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_1 : Q 6 ((Z54.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_2 : Q 6 ((Z54.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_3 : Q 6 ((Z54.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_4 : Q 6 ((Z54.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_5 : Q 6 ((Z54.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_6 : Q 6 ((Z54.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_7 : Q 6 ((Z54.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_8 : Q 6 ((Z54.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_9 : Q 6 ((Z54.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_10 : Q 6 ((Z54.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_11 : Q 6 ((Z54.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_12 : Q 6 ((Z54.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_13 : Q 6 ((Z54.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_14 : Q 6 ((Z54.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_15 : Q 6 ((Z54.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_16 : Q 6 ((Z54.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_17 : Q 6 ((Z54.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_18 : Q 6 ((Z54.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_19 : Q 6 ((Z54.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_20 : Q 6 ((Z54.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_21 : Q 6 ((Z54.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_22 : Q 6 ((Z54.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_23 : Q 6 ((Z54.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_24 : Q 6 ((Z54.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_25 : Q 6 ((Z54.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_26 : Q 6 ((Z54.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_27 : Q 6 ((Z54.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_28 : Q 6 ((Z54.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_29 : Q 6 ((Z54.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_30 : Q 6 ((Z54.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_31 : Q 6 ((Z54.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_32 : Q 6 ((Z54.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_33 : Q 6 ((Z54.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_34 : Q 6 ((Z54.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_35 : Q 6 ((Z54.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_36 : Q 6 ((Z54.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_37 : Q 6 ((Z54.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_38 : Q 6 ((Z54.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_39 : Q 6 ((Z54.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C54_40 : Q 6 ((Z54.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S54 : Q 6 Z54 = true := by
  refine all_of_chunks Z54 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C54_0
  · exact C54_1
  · exact C54_2
  · exact C54_3
  · exact C54_4
  · exact C54_5
  · exact C54_6
  · exact C54_7
  · exact C54_8
  · exact C54_9
  · exact C54_10
  · exact C54_11
  · exact C54_12
  · exact C54_13
  · exact C54_14
  · exact C54_15
  · exact C54_16
  · exact C54_17
  · exact C54_18
  · exact C54_19
  · exact C54_20
  · exact C54_21
  · exact C54_22
  · exact C54_23
  · exact C54_24
  · exact C54_25
  · exact C54_26
  · exact C54_27
  · exact C54_28
  · exact C54_29
  · exact C54_30
  · exact C54_31
  · exact C54_32
  · exact C54_33
  · exact C54_34
  · exact C54_35
  · exact C54_36
  · exact C54_37
  · exact C54_38
  · exact C54_39
  · exact C54_40

def T54 : Q 7 ((R1.drop 54).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 54).take 1) (by decide +kernel) S54

def Z55 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 55).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_0 : Q 6 ((Z55.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_1 : Q 6 ((Z55.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_2 : Q 6 ((Z55.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_3 : Q 6 ((Z55.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_4 : Q 6 ((Z55.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_5 : Q 6 ((Z55.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_6 : Q 6 ((Z55.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_7 : Q 6 ((Z55.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_8 : Q 6 ((Z55.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_9 : Q 6 ((Z55.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_10 : Q 6 ((Z55.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_11 : Q 6 ((Z55.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_12 : Q 6 ((Z55.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C55_13 : Q 6 ((Z55.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S55 : Q 6 Z55 = true := by
  refine all_of_chunks Z55 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C55_0
  · exact C55_1
  · exact C55_2
  · exact C55_3
  · exact C55_4
  · exact C55_5
  · exact C55_6
  · exact C55_7
  · exact C55_8
  · exact C55_9
  · exact C55_10
  · exact C55_11
  · exact C55_12
  · exact C55_13

def T55 : Q 7 ((R1.drop 55).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 55).take 1) (by decide +kernel) S55

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T56 : Q 7 ((R1.drop 56).take 1) = true := by decide +kernel

def Z57 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 57).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_0 : Q 6 ((Z57.drop 0).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_1 : Q 6 ((Z57.drop 1).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_2 : Q 6 ((Z57.drop 2).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_3 : Q 6 ((Z57.drop 3).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_4 : Q 6 ((Z57.drop 4).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_5 : Q 6 ((Z57.drop 5).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_6 : Q 6 ((Z57.drop 6).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_7 : Q 6 ((Z57.drop 7).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_8 : Q 6 ((Z57.drop 8).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_9 : Q 6 ((Z57.drop 9).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_10 : Q 6 ((Z57.drop 10).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_11 : Q 6 ((Z57.drop 11).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_12 : Q 6 ((Z57.drop 12).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_13 : Q 6 ((Z57.drop 13).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_14 : Q 6 ((Z57.drop 14).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_15 : Q 6 ((Z57.drop 15).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_16 : Q 6 ((Z57.drop 16).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_17 : Q 6 ((Z57.drop 17).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_18 : Q 6 ((Z57.drop 18).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_19 : Q 6 ((Z57.drop 19).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_20 : Q 6 ((Z57.drop 20).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_21 : Q 6 ((Z57.drop 21).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_22 : Q 6 ((Z57.drop 22).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_23 : Q 6 ((Z57.drop 23).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_24 : Q 6 ((Z57.drop 24).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_25 : Q 6 ((Z57.drop 25).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_26 : Q 6 ((Z57.drop 26).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_27 : Q 6 ((Z57.drop 27).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_28 : Q 6 ((Z57.drop 28).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_29 : Q 6 ((Z57.drop 29).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_30 : Q 6 ((Z57.drop 30).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_31 : Q 6 ((Z57.drop 31).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_32 : Q 6 ((Z57.drop 32).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_33 : Q 6 ((Z57.drop 33).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_34 : Q 6 ((Z57.drop 34).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_35 : Q 6 ((Z57.drop 35).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_36 : Q 6 ((Z57.drop 36).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_37 : Q 6 ((Z57.drop 37).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_38 : Q 6 ((Z57.drop 38).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_39 : Q 6 ((Z57.drop 39).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_40 : Q 6 ((Z57.drop 40).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_41 : Q 6 ((Z57.drop 41).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_42 : Q 6 ((Z57.drop 42).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_43 : Q 6 ((Z57.drop 43).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_44 : Q 6 ((Z57.drop 44).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_45 : Q 6 ((Z57.drop 45).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_46 : Q 6 ((Z57.drop 46).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_47 : Q 6 ((Z57.drop 47).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_48 : Q 6 ((Z57.drop 48).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_49 : Q 6 ((Z57.drop 49).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_50 : Q 6 ((Z57.drop 50).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_51 : Q 6 ((Z57.drop 51).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_52 : Q 6 ((Z57.drop 52).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_53 : Q 6 ((Z57.drop 53).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_54 : Q 6 ((Z57.drop 54).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_55 : Q 6 ((Z57.drop 55).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_56 : Q 6 ((Z57.drop 56).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_57 : Q 6 ((Z57.drop 57).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_58 : Q 6 ((Z57.drop 58).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_59 : Q 6 ((Z57.drop 59).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_60 : Q 6 ((Z57.drop 60).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_61 : Q 6 ((Z57.drop 61).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_62 : Q 6 ((Z57.drop 62).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_63 : Q 6 ((Z57.drop 63).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_64 : Q 6 ((Z57.drop 64).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_65 : Q 6 ((Z57.drop 65).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_66 : Q 6 ((Z57.drop 66).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_67 : Q 6 ((Z57.drop 67).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_68 : Q 6 ((Z57.drop 68).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_69 : Q 6 ((Z57.drop 69).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_70 : Q 6 ((Z57.drop 70).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_71 : Q 6 ((Z57.drop 71).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_72 : Q 6 ((Z57.drop 72).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_73 : Q 6 ((Z57.drop 73).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_74 : Q 6 ((Z57.drop 74).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_75 : Q 6 ((Z57.drop 75).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_76 : Q 6 ((Z57.drop 76).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_77 : Q 6 ((Z57.drop 77).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_78 : Q 6 ((Z57.drop 78).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_79 : Q 6 ((Z57.drop 79).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_80 : Q 6 ((Z57.drop 80).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C57_81 : Q 6 ((Z57.drop 81).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S57 : Q 6 Z57 = true := by
  refine all_of_chunks Z57 (fun c => !LS G MK 0 31 true 6 c) 1 82 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C57_0
  · exact C57_1
  · exact C57_2
  · exact C57_3
  · exact C57_4
  · exact C57_5
  · exact C57_6
  · exact C57_7
  · exact C57_8
  · exact C57_9
  · exact C57_10
  · exact C57_11
  · exact C57_12
  · exact C57_13
  · exact C57_14
  · exact C57_15
  · exact C57_16
  · exact C57_17
  · exact C57_18
  · exact C57_19
  · exact C57_20
  · exact C57_21
  · exact C57_22
  · exact C57_23
  · exact C57_24
  · exact C57_25
  · exact C57_26
  · exact C57_27
  · exact C57_28
  · exact C57_29
  · exact C57_30
  · exact C57_31
  · exact C57_32
  · exact C57_33
  · exact C57_34
  · exact C57_35
  · exact C57_36
  · exact C57_37
  · exact C57_38
  · exact C57_39
  · exact C57_40
  · exact C57_41
  · exact C57_42
  · exact C57_43
  · exact C57_44
  · exact C57_45
  · exact C57_46
  · exact C57_47
  · exact C57_48
  · exact C57_49
  · exact C57_50
  · exact C57_51
  · exact C57_52
  · exact C57_53
  · exact C57_54
  · exact C57_55
  · exact C57_56
  · exact C57_57
  · exact C57_58
  · exact C57_59
  · exact C57_60
  · exact C57_61
  · exact C57_62
  · exact C57_63
  · exact C57_64
  · exact C57_65
  · exact C57_66
  · exact C57_67
  · exact C57_68
  · exact C57_69
  · exact C57_70
  · exact C57_71
  · exact C57_72
  · exact C57_73
  · exact C57_74
  · exact C57_75
  · exact C57_76
  · exact C57_77
  · exact C57_78
  · exact C57_79
  · exact C57_80
  · exact C57_81

def T57 : Q 7 ((R1.drop 57).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 57).take 1) (by decide +kernel) S57

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T58 : Q 7 ((R1.drop 58).take 1) = true := by decide +kernel

def Z59 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 59).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_0 : Q 6 ((Z59.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_1 : Q 6 ((Z59.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_2 : Q 6 ((Z59.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_3 : Q 6 ((Z59.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_4 : Q 6 ((Z59.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_5 : Q 6 ((Z59.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_6 : Q 6 ((Z59.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_7 : Q 6 ((Z59.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_8 : Q 6 ((Z59.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_9 : Q 6 ((Z59.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_10 : Q 6 ((Z59.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_11 : Q 6 ((Z59.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_12 : Q 6 ((Z59.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C59_13 : Q 6 ((Z59.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S59 : Q 6 Z59 = true := by
  refine all_of_chunks Z59 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C59_0
  · exact C59_1
  · exact C59_2
  · exact C59_3
  · exact C59_4
  · exact C59_5
  · exact C59_6
  · exact C59_7
  · exact C59_8
  · exact C59_9
  · exact C59_10
  · exact C59_11
  · exact C59_12
  · exact C59_13

def T59 : Q 7 ((R1.drop 59).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 59).take 1) (by decide +kernel) S59

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T60 : Q 7 ((R1.drop 60).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T61 : Q 7 ((R1.drop 61).take 1) = true := by decide +kernel

def Z62 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 62).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_0 : Q 6 ((Z62.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_1 : Q 6 ((Z62.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_2 : Q 6 ((Z62.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_3 : Q 6 ((Z62.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_4 : Q 6 ((Z62.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_5 : Q 6 ((Z62.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_6 : Q 6 ((Z62.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_7 : Q 6 ((Z62.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_8 : Q 6 ((Z62.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_9 : Q 6 ((Z62.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_10 : Q 6 ((Z62.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_11 : Q 6 ((Z62.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_12 : Q 6 ((Z62.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_13 : Q 6 ((Z62.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_14 : Q 6 ((Z62.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_15 : Q 6 ((Z62.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_16 : Q 6 ((Z62.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_17 : Q 6 ((Z62.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_18 : Q 6 ((Z62.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_19 : Q 6 ((Z62.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_20 : Q 6 ((Z62.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_21 : Q 6 ((Z62.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_22 : Q 6 ((Z62.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_23 : Q 6 ((Z62.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_24 : Q 6 ((Z62.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_25 : Q 6 ((Z62.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_26 : Q 6 ((Z62.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_27 : Q 6 ((Z62.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_28 : Q 6 ((Z62.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_29 : Q 6 ((Z62.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_30 : Q 6 ((Z62.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_31 : Q 6 ((Z62.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_32 : Q 6 ((Z62.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_33 : Q 6 ((Z62.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_34 : Q 6 ((Z62.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_35 : Q 6 ((Z62.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_36 : Q 6 ((Z62.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_37 : Q 6 ((Z62.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_38 : Q 6 ((Z62.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_39 : Q 6 ((Z62.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C62_40 : Q 6 ((Z62.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S62 : Q 6 Z62 = true := by
  refine all_of_chunks Z62 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C62_0
  · exact C62_1
  · exact C62_2
  · exact C62_3
  · exact C62_4
  · exact C62_5
  · exact C62_6
  · exact C62_7
  · exact C62_8
  · exact C62_9
  · exact C62_10
  · exact C62_11
  · exact C62_12
  · exact C62_13
  · exact C62_14
  · exact C62_15
  · exact C62_16
  · exact C62_17
  · exact C62_18
  · exact C62_19
  · exact C62_20
  · exact C62_21
  · exact C62_22
  · exact C62_23
  · exact C62_24
  · exact C62_25
  · exact C62_26
  · exact C62_27
  · exact C62_28
  · exact C62_29
  · exact C62_30
  · exact C62_31
  · exact C62_32
  · exact C62_33
  · exact C62_34
  · exact C62_35
  · exact C62_36
  · exact C62_37
  · exact C62_38
  · exact C62_39
  · exact C62_40

def T62 : Q 7 ((R1.drop 62).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 62).take 1) (by decide +kernel) S62

def Z63 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 63).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_0 : Q 6 ((Z63.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_1 : Q 6 ((Z63.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_2 : Q 6 ((Z63.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_3 : Q 6 ((Z63.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_4 : Q 6 ((Z63.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_5 : Q 6 ((Z63.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_6 : Q 6 ((Z63.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_7 : Q 6 ((Z63.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_8 : Q 6 ((Z63.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_9 : Q 6 ((Z63.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_10 : Q 6 ((Z63.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_11 : Q 6 ((Z63.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_12 : Q 6 ((Z63.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C63_13 : Q 6 ((Z63.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S63 : Q 6 Z63 = true := by
  refine all_of_chunks Z63 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C63_0
  · exact C63_1
  · exact C63_2
  · exact C63_3
  · exact C63_4
  · exact C63_5
  · exact C63_6
  · exact C63_7
  · exact C63_8
  · exact C63_9
  · exact C63_10
  · exact C63_11
  · exact C63_12
  · exact C63_13

def T63 : Q 7 ((R1.drop 63).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 63).take 1) (by decide +kernel) S63

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T64 : Q 7 ((R1.drop 64).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T65 : Q 7 ((R1.drop 65).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T66 : Q 7 ((R1.drop 66).take 1) = true := by decide +kernel

def Z67 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 67).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_0 : Q 6 ((Z67.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_1 : Q 6 ((Z67.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_2 : Q 6 ((Z67.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_3 : Q 6 ((Z67.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_4 : Q 6 ((Z67.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_5 : Q 6 ((Z67.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_6 : Q 6 ((Z67.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_7 : Q 6 ((Z67.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_8 : Q 6 ((Z67.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_9 : Q 6 ((Z67.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_10 : Q 6 ((Z67.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_11 : Q 6 ((Z67.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_12 : Q 6 ((Z67.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C67_13 : Q 6 ((Z67.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S67 : Q 6 Z67 = true := by
  refine all_of_chunks Z67 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C67_0
  · exact C67_1
  · exact C67_2
  · exact C67_3
  · exact C67_4
  · exact C67_5
  · exact C67_6
  · exact C67_7
  · exact C67_8
  · exact C67_9
  · exact C67_10
  · exact C67_11
  · exact C67_12
  · exact C67_13

def T67 : Q 7 ((R1.drop 67).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 67).take 1) (by decide +kernel) S67

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T68 : Q 7 ((R1.drop 68).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T69 : Q 7 ((R1.drop 69).take 1) = true := by decide +kernel

def Z70 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 70).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_0 : Q 6 ((Z70.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_1 : Q 6 ((Z70.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_2 : Q 6 ((Z70.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_3 : Q 6 ((Z70.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_4 : Q 6 ((Z70.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_5 : Q 6 ((Z70.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_6 : Q 6 ((Z70.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_7 : Q 6 ((Z70.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_8 : Q 6 ((Z70.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_9 : Q 6 ((Z70.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_10 : Q 6 ((Z70.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_11 : Q 6 ((Z70.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_12 : Q 6 ((Z70.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_13 : Q 6 ((Z70.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_14 : Q 6 ((Z70.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_15 : Q 6 ((Z70.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_16 : Q 6 ((Z70.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_17 : Q 6 ((Z70.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_18 : Q 6 ((Z70.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_19 : Q 6 ((Z70.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_20 : Q 6 ((Z70.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_21 : Q 6 ((Z70.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_22 : Q 6 ((Z70.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_23 : Q 6 ((Z70.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_24 : Q 6 ((Z70.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_25 : Q 6 ((Z70.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_26 : Q 6 ((Z70.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_27 : Q 6 ((Z70.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_28 : Q 6 ((Z70.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_29 : Q 6 ((Z70.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_30 : Q 6 ((Z70.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_31 : Q 6 ((Z70.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_32 : Q 6 ((Z70.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_33 : Q 6 ((Z70.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_34 : Q 6 ((Z70.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_35 : Q 6 ((Z70.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_36 : Q 6 ((Z70.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_37 : Q 6 ((Z70.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_38 : Q 6 ((Z70.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_39 : Q 6 ((Z70.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C70_40 : Q 6 ((Z70.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S70 : Q 6 Z70 = true := by
  refine all_of_chunks Z70 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C70_0
  · exact C70_1
  · exact C70_2
  · exact C70_3
  · exact C70_4
  · exact C70_5
  · exact C70_6
  · exact C70_7
  · exact C70_8
  · exact C70_9
  · exact C70_10
  · exact C70_11
  · exact C70_12
  · exact C70_13
  · exact C70_14
  · exact C70_15
  · exact C70_16
  · exact C70_17
  · exact C70_18
  · exact C70_19
  · exact C70_20
  · exact C70_21
  · exact C70_22
  · exact C70_23
  · exact C70_24
  · exact C70_25
  · exact C70_26
  · exact C70_27
  · exact C70_28
  · exact C70_29
  · exact C70_30
  · exact C70_31
  · exact C70_32
  · exact C70_33
  · exact C70_34
  · exact C70_35
  · exact C70_36
  · exact C70_37
  · exact C70_38
  · exact C70_39
  · exact C70_40

def T70 : Q 7 ((R1.drop 70).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 70).take 1) (by decide +kernel) S70

def Z71 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 71).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_0 : Q 6 ((Z71.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_1 : Q 6 ((Z71.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_2 : Q 6 ((Z71.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_3 : Q 6 ((Z71.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_4 : Q 6 ((Z71.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_5 : Q 6 ((Z71.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_6 : Q 6 ((Z71.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_7 : Q 6 ((Z71.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_8 : Q 6 ((Z71.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_9 : Q 6 ((Z71.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_10 : Q 6 ((Z71.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_11 : Q 6 ((Z71.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_12 : Q 6 ((Z71.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C71_13 : Q 6 ((Z71.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S71 : Q 6 Z71 = true := by
  refine all_of_chunks Z71 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C71_0
  · exact C71_1
  · exact C71_2
  · exact C71_3
  · exact C71_4
  · exact C71_5
  · exact C71_6
  · exact C71_7
  · exact C71_8
  · exact C71_9
  · exact C71_10
  · exact C71_11
  · exact C71_12
  · exact C71_13

def T71 : Q 7 ((R1.drop 71).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 71).take 1) (by decide +kernel) S71

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T72 : Q 7 ((R1.drop 72).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T73 : Q 7 ((R1.drop 73).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T74 : Q 7 ((R1.drop 74).take 1) = true := by decide +kernel

def Z75 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 75).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_0 : Q 6 ((Z75.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_1 : Q 6 ((Z75.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_2 : Q 6 ((Z75.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_3 : Q 6 ((Z75.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_4 : Q 6 ((Z75.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_5 : Q 6 ((Z75.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_6 : Q 6 ((Z75.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_7 : Q 6 ((Z75.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_8 : Q 6 ((Z75.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_9 : Q 6 ((Z75.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_10 : Q 6 ((Z75.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_11 : Q 6 ((Z75.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_12 : Q 6 ((Z75.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C75_13 : Q 6 ((Z75.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S75 : Q 6 Z75 = true := by
  refine all_of_chunks Z75 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C75_0
  · exact C75_1
  · exact C75_2
  · exact C75_3
  · exact C75_4
  · exact C75_5
  · exact C75_6
  · exact C75_7
  · exact C75_8
  · exact C75_9
  · exact C75_10
  · exact C75_11
  · exact C75_12
  · exact C75_13

def T75 : Q 7 ((R1.drop 75).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 75).take 1) (by decide +kernel) S75

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T76 : Q 7 ((R1.drop 76).take 1) = true := by decide +kernel

def Z77 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 77).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_0 : Q 6 ((Z77.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_1 : Q 6 ((Z77.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_2 : Q 6 ((Z77.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_3 : Q 6 ((Z77.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_4 : Q 6 ((Z77.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_5 : Q 6 ((Z77.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_6 : Q 6 ((Z77.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_7 : Q 6 ((Z77.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_8 : Q 6 ((Z77.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_9 : Q 6 ((Z77.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_10 : Q 6 ((Z77.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_11 : Q 6 ((Z77.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_12 : Q 6 ((Z77.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_13 : Q 6 ((Z77.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_14 : Q 6 ((Z77.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_15 : Q 6 ((Z77.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_16 : Q 6 ((Z77.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_17 : Q 6 ((Z77.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_18 : Q 6 ((Z77.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_19 : Q 6 ((Z77.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_20 : Q 6 ((Z77.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_21 : Q 6 ((Z77.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_22 : Q 6 ((Z77.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_23 : Q 6 ((Z77.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_24 : Q 6 ((Z77.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_25 : Q 6 ((Z77.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_26 : Q 6 ((Z77.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_27 : Q 6 ((Z77.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_28 : Q 6 ((Z77.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_29 : Q 6 ((Z77.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_30 : Q 6 ((Z77.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_31 : Q 6 ((Z77.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_32 : Q 6 ((Z77.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_33 : Q 6 ((Z77.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_34 : Q 6 ((Z77.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_35 : Q 6 ((Z77.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_36 : Q 6 ((Z77.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_37 : Q 6 ((Z77.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_38 : Q 6 ((Z77.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_39 : Q 6 ((Z77.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C77_40 : Q 6 ((Z77.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S77 : Q 6 Z77 = true := by
  refine all_of_chunks Z77 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C77_0
  · exact C77_1
  · exact C77_2
  · exact C77_3
  · exact C77_4
  · exact C77_5
  · exact C77_6
  · exact C77_7
  · exact C77_8
  · exact C77_9
  · exact C77_10
  · exact C77_11
  · exact C77_12
  · exact C77_13
  · exact C77_14
  · exact C77_15
  · exact C77_16
  · exact C77_17
  · exact C77_18
  · exact C77_19
  · exact C77_20
  · exact C77_21
  · exact C77_22
  · exact C77_23
  · exact C77_24
  · exact C77_25
  · exact C77_26
  · exact C77_27
  · exact C77_28
  · exact C77_29
  · exact C77_30
  · exact C77_31
  · exact C77_32
  · exact C77_33
  · exact C77_34
  · exact C77_35
  · exact C77_36
  · exact C77_37
  · exact C77_38
  · exact C77_39
  · exact C77_40

def T77 : Q 7 ((R1.drop 77).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 77).take 1) (by decide +kernel) S77

def Z78 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 78).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_0 : Q 6 ((Z78.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_1 : Q 6 ((Z78.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_2 : Q 6 ((Z78.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_3 : Q 6 ((Z78.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_4 : Q 6 ((Z78.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_5 : Q 6 ((Z78.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_6 : Q 6 ((Z78.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_7 : Q 6 ((Z78.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_8 : Q 6 ((Z78.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_9 : Q 6 ((Z78.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_10 : Q 6 ((Z78.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_11 : Q 6 ((Z78.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_12 : Q 6 ((Z78.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_13 : Q 6 ((Z78.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_14 : Q 6 ((Z78.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_15 : Q 6 ((Z78.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_16 : Q 6 ((Z78.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_17 : Q 6 ((Z78.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_18 : Q 6 ((Z78.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_19 : Q 6 ((Z78.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_20 : Q 6 ((Z78.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_21 : Q 6 ((Z78.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_22 : Q 6 ((Z78.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_23 : Q 6 ((Z78.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_24 : Q 6 ((Z78.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_25 : Q 6 ((Z78.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_26 : Q 6 ((Z78.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_27 : Q 6 ((Z78.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_28 : Q 6 ((Z78.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_29 : Q 6 ((Z78.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_30 : Q 6 ((Z78.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_31 : Q 6 ((Z78.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_32 : Q 6 ((Z78.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_33 : Q 6 ((Z78.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_34 : Q 6 ((Z78.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_35 : Q 6 ((Z78.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_36 : Q 6 ((Z78.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_37 : Q 6 ((Z78.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_38 : Q 6 ((Z78.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_39 : Q 6 ((Z78.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C78_40 : Q 6 ((Z78.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S78 : Q 6 Z78 = true := by
  refine all_of_chunks Z78 (fun c => !LS G MK 0 31 true 6 c) 2 41 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C78_0
  · exact C78_1
  · exact C78_2
  · exact C78_3
  · exact C78_4
  · exact C78_5
  · exact C78_6
  · exact C78_7
  · exact C78_8
  · exact C78_9
  · exact C78_10
  · exact C78_11
  · exact C78_12
  · exact C78_13
  · exact C78_14
  · exact C78_15
  · exact C78_16
  · exact C78_17
  · exact C78_18
  · exact C78_19
  · exact C78_20
  · exact C78_21
  · exact C78_22
  · exact C78_23
  · exact C78_24
  · exact C78_25
  · exact C78_26
  · exact C78_27
  · exact C78_28
  · exact C78_29
  · exact C78_30
  · exact C78_31
  · exact C78_32
  · exact C78_33
  · exact C78_34
  · exact C78_35
  · exact C78_36
  · exact C78_37
  · exact C78_38
  · exact C78_39
  · exact C78_40

def T78 : Q 7 ((R1.drop 78).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 78).take 1) (by decide +kernel) S78

def Z79 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 79).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_0 : Q 6 ((Z79.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_1 : Q 6 ((Z79.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_2 : Q 6 ((Z79.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_3 : Q 6 ((Z79.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_4 : Q 6 ((Z79.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_5 : Q 6 ((Z79.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_6 : Q 6 ((Z79.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_7 : Q 6 ((Z79.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_8 : Q 6 ((Z79.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_9 : Q 6 ((Z79.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_10 : Q 6 ((Z79.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_11 : Q 6 ((Z79.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_12 : Q 6 ((Z79.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C79_13 : Q 6 ((Z79.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S79 : Q 6 Z79 = true := by
  refine all_of_chunks Z79 (fun c => !LS G MK 0 31 true 6 c) 8 14 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C79_0
  · exact C79_1
  · exact C79_2
  · exact C79_3
  · exact C79_4
  · exact C79_5
  · exact C79_6
  · exact C79_7
  · exact C79_8
  · exact C79_9
  · exact C79_10
  · exact C79_11
  · exact C79_12
  · exact C79_13

def T79 : Q 7 ((R1.drop 79).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 79).take 1) (by decide +kernel) S79

def Z80 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 80).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_0 : Q 6 ((Z80.drop 0).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_1 : Q 6 ((Z80.drop 4).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_2 : Q 6 ((Z80.drop 8).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_3 : Q 6 ((Z80.drop 12).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_4 : Q 6 ((Z80.drop 16).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_5 : Q 6 ((Z80.drop 20).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_6 : Q 6 ((Z80.drop 24).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_7 : Q 6 ((Z80.drop 28).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_8 : Q 6 ((Z80.drop 32).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_9 : Q 6 ((Z80.drop 36).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_10 : Q 6 ((Z80.drop 40).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_11 : Q 6 ((Z80.drop 44).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_12 : Q 6 ((Z80.drop 48).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_13 : Q 6 ((Z80.drop 52).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_14 : Q 6 ((Z80.drop 56).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_15 : Q 6 ((Z80.drop 60).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_16 : Q 6 ((Z80.drop 64).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_17 : Q 6 ((Z80.drop 68).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_18 : Q 6 ((Z80.drop 72).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_19 : Q 6 ((Z80.drop 76).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_20 : Q 6 ((Z80.drop 80).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_21 : Q 6 ((Z80.drop 84).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C80_22 : Q 6 ((Z80.drop 88).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S80 : Q 6 Z80 = true := by
  refine all_of_chunks Z80 (fun c => !LS G MK 0 31 true 6 c) 4 23 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C80_0
  · exact C80_1
  · exact C80_2
  · exact C80_3
  · exact C80_4
  · exact C80_5
  · exact C80_6
  · exact C80_7
  · exact C80_8
  · exact C80_9
  · exact C80_10
  · exact C80_11
  · exact C80_12
  · exact C80_13
  · exact C80_14
  · exact C80_15
  · exact C80_16
  · exact C80_17
  · exact C80_18
  · exact C80_19
  · exact C80_20
  · exact C80_21
  · exact C80_22

def T80 : Q 7 ((R1.drop 80).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 80).take 1) (by decide +kernel) S80

def Z81 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 81).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_0 : Q 6 ((Z81.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_1 : Q 6 ((Z81.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_2 : Q 6 ((Z81.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_3 : Q 6 ((Z81.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_4 : Q 6 ((Z81.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_5 : Q 6 ((Z81.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_6 : Q 6 ((Z81.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_7 : Q 6 ((Z81.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_8 : Q 6 ((Z81.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_9 : Q 6 ((Z81.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_10 : Q 6 ((Z81.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_11 : Q 6 ((Z81.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_12 : Q 6 ((Z81.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_13 : Q 6 ((Z81.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_14 : Q 6 ((Z81.drop 112).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C81_15 : Q 6 ((Z81.drop 120).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S81 : Q 6 Z81 = true := by
  refine all_of_chunks Z81 (fun c => !LS G MK 0 31 true 6 c) 8 16 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C81_0
  · exact C81_1
  · exact C81_2
  · exact C81_3
  · exact C81_4
  · exact C81_5
  · exact C81_6
  · exact C81_7
  · exact C81_8
  · exact C81_9
  · exact C81_10
  · exact C81_11
  · exact C81_12
  · exact C81_13
  · exact C81_14
  · exact C81_15

def T81 : Q 7 ((R1.drop 81).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 81).take 1) (by decide +kernel) S81

def Z82 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 82).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_0 : Q 6 ((Z82.drop 0).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_1 : Q 6 ((Z82.drop 4).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_2 : Q 6 ((Z82.drop 8).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_3 : Q 6 ((Z82.drop 12).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_4 : Q 6 ((Z82.drop 16).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_5 : Q 6 ((Z82.drop 20).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_6 : Q 6 ((Z82.drop 24).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_7 : Q 6 ((Z82.drop 28).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_8 : Q 6 ((Z82.drop 32).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_9 : Q 6 ((Z82.drop 36).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_10 : Q 6 ((Z82.drop 40).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_11 : Q 6 ((Z82.drop 44).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_12 : Q 6 ((Z82.drop 48).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_13 : Q 6 ((Z82.drop 52).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_14 : Q 6 ((Z82.drop 56).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_15 : Q 6 ((Z82.drop 60).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_16 : Q 6 ((Z82.drop 64).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_17 : Q 6 ((Z82.drop 68).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_18 : Q 6 ((Z82.drop 72).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_19 : Q 6 ((Z82.drop 76).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_20 : Q 6 ((Z82.drop 80).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_21 : Q 6 ((Z82.drop 84).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C82_22 : Q 6 ((Z82.drop 88).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S82 : Q 6 Z82 = true := by
  refine all_of_chunks Z82 (fun c => !LS G MK 0 31 true 6 c) 4 23 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C82_0
  · exact C82_1
  · exact C82_2
  · exact C82_3
  · exact C82_4
  · exact C82_5
  · exact C82_6
  · exact C82_7
  · exact C82_8
  · exact C82_9
  · exact C82_10
  · exact C82_11
  · exact C82_12
  · exact C82_13
  · exact C82_14
  · exact C82_15
  · exact C82_16
  · exact C82_17
  · exact C82_18
  · exact C82_19
  · exact C82_20
  · exact C82_21
  · exact C82_22

def T82 : Q 7 ((R1.drop 82).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 82).take 1) (by decide +kernel) S82

def Z83 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 83).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_0 : Q 6 ((Z83.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_1 : Q 6 ((Z83.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_2 : Q 6 ((Z83.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_3 : Q 6 ((Z83.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_4 : Q 6 ((Z83.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_5 : Q 6 ((Z83.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_6 : Q 6 ((Z83.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_7 : Q 6 ((Z83.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_8 : Q 6 ((Z83.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_9 : Q 6 ((Z83.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_10 : Q 6 ((Z83.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_11 : Q 6 ((Z83.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_12 : Q 6 ((Z83.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_13 : Q 6 ((Z83.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_14 : Q 6 ((Z83.drop 112).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C83_15 : Q 6 ((Z83.drop 120).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S83 : Q 6 Z83 = true := by
  refine all_of_chunks Z83 (fun c => !LS G MK 0 31 true 6 c) 8 16 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C83_0
  · exact C83_1
  · exact C83_2
  · exact C83_3
  · exact C83_4
  · exact C83_5
  · exact C83_6
  · exact C83_7
  · exact C83_8
  · exact C83_9
  · exact C83_10
  · exact C83_11
  · exact C83_12
  · exact C83_13
  · exact C83_14
  · exact C83_15

def T83 : Q 7 ((R1.drop 83).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 83).take 1) (by decide +kernel) S83

def Z84 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 84).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_0 : Q 6 ((Z84.drop 0).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_1 : Q 6 ((Z84.drop 1).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_2 : Q 6 ((Z84.drop 2).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_3 : Q 6 ((Z84.drop 3).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_4 : Q 6 ((Z84.drop 4).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_5 : Q 6 ((Z84.drop 5).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_6 : Q 6 ((Z84.drop 6).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_7 : Q 6 ((Z84.drop 7).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_8 : Q 6 ((Z84.drop 8).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_9 : Q 6 ((Z84.drop 9).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_10 : Q 6 ((Z84.drop 10).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_11 : Q 6 ((Z84.drop 11).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_12 : Q 6 ((Z84.drop 12).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_13 : Q 6 ((Z84.drop 13).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_14 : Q 6 ((Z84.drop 14).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_15 : Q 6 ((Z84.drop 15).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_16 : Q 6 ((Z84.drop 16).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_17 : Q 6 ((Z84.drop 17).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_18 : Q 6 ((Z84.drop 18).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_19 : Q 6 ((Z84.drop 19).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_20 : Q 6 ((Z84.drop 20).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_21 : Q 6 ((Z84.drop 21).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_22 : Q 6 ((Z84.drop 22).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_23 : Q 6 ((Z84.drop 23).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_24 : Q 6 ((Z84.drop 24).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_25 : Q 6 ((Z84.drop 25).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_26 : Q 6 ((Z84.drop 26).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_27 : Q 6 ((Z84.drop 27).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_28 : Q 6 ((Z84.drop 28).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_29 : Q 6 ((Z84.drop 29).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_30 : Q 6 ((Z84.drop 30).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_31 : Q 6 ((Z84.drop 31).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_32 : Q 6 ((Z84.drop 32).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_33 : Q 6 ((Z84.drop 33).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_34 : Q 6 ((Z84.drop 34).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_35 : Q 6 ((Z84.drop 35).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_36 : Q 6 ((Z84.drop 36).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_37 : Q 6 ((Z84.drop 37).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_38 : Q 6 ((Z84.drop 38).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_39 : Q 6 ((Z84.drop 39).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_40 : Q 6 ((Z84.drop 40).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_41 : Q 6 ((Z84.drop 41).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_42 : Q 6 ((Z84.drop 42).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_43 : Q 6 ((Z84.drop 43).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_44 : Q 6 ((Z84.drop 44).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_45 : Q 6 ((Z84.drop 45).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_46 : Q 6 ((Z84.drop 46).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_47 : Q 6 ((Z84.drop 47).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_48 : Q 6 ((Z84.drop 48).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_49 : Q 6 ((Z84.drop 49).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_50 : Q 6 ((Z84.drop 50).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_51 : Q 6 ((Z84.drop 51).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_52 : Q 6 ((Z84.drop 52).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_53 : Q 6 ((Z84.drop 53).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_54 : Q 6 ((Z84.drop 54).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_55 : Q 6 ((Z84.drop 55).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_56 : Q 6 ((Z84.drop 56).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_57 : Q 6 ((Z84.drop 57).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_58 : Q 6 ((Z84.drop 58).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_59 : Q 6 ((Z84.drop 59).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_60 : Q 6 ((Z84.drop 60).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_61 : Q 6 ((Z84.drop 61).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_62 : Q 6 ((Z84.drop 62).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_63 : Q 6 ((Z84.drop 63).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_64 : Q 6 ((Z84.drop 64).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_65 : Q 6 ((Z84.drop 65).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_66 : Q 6 ((Z84.drop 66).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_67 : Q 6 ((Z84.drop 67).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_68 : Q 6 ((Z84.drop 68).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_69 : Q 6 ((Z84.drop 69).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_70 : Q 6 ((Z84.drop 70).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_71 : Q 6 ((Z84.drop 71).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_72 : Q 6 ((Z84.drop 72).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_73 : Q 6 ((Z84.drop 73).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_74 : Q 6 ((Z84.drop 74).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_75 : Q 6 ((Z84.drop 75).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_76 : Q 6 ((Z84.drop 76).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_77 : Q 6 ((Z84.drop 77).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_78 : Q 6 ((Z84.drop 78).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_79 : Q 6 ((Z84.drop 79).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_80 : Q 6 ((Z84.drop 80).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_81 : Q 6 ((Z84.drop 81).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_82 : Q 6 ((Z84.drop 82).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_83 : Q 6 ((Z84.drop 83).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_84 : Q 6 ((Z84.drop 84).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_85 : Q 6 ((Z84.drop 85).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_86 : Q 6 ((Z84.drop 86).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_87 : Q 6 ((Z84.drop 87).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_88 : Q 6 ((Z84.drop 88).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C84_89 : Q 6 ((Z84.drop 89).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S84 : Q 6 Z84 = true := by
  refine all_of_chunks Z84 (fun c => !LS G MK 0 31 true 6 c) 1 90 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C84_0
  · exact C84_1
  · exact C84_2
  · exact C84_3
  · exact C84_4
  · exact C84_5
  · exact C84_6
  · exact C84_7
  · exact C84_8
  · exact C84_9
  · exact C84_10
  · exact C84_11
  · exact C84_12
  · exact C84_13
  · exact C84_14
  · exact C84_15
  · exact C84_16
  · exact C84_17
  · exact C84_18
  · exact C84_19
  · exact C84_20
  · exact C84_21
  · exact C84_22
  · exact C84_23
  · exact C84_24
  · exact C84_25
  · exact C84_26
  · exact C84_27
  · exact C84_28
  · exact C84_29
  · exact C84_30
  · exact C84_31
  · exact C84_32
  · exact C84_33
  · exact C84_34
  · exact C84_35
  · exact C84_36
  · exact C84_37
  · exact C84_38
  · exact C84_39
  · exact C84_40
  · exact C84_41
  · exact C84_42
  · exact C84_43
  · exact C84_44
  · exact C84_45
  · exact C84_46
  · exact C84_47
  · exact C84_48
  · exact C84_49
  · exact C84_50
  · exact C84_51
  · exact C84_52
  · exact C84_53
  · exact C84_54
  · exact C84_55
  · exact C84_56
  · exact C84_57
  · exact C84_58
  · exact C84_59
  · exact C84_60
  · exact C84_61
  · exact C84_62
  · exact C84_63
  · exact C84_64
  · exact C84_65
  · exact C84_66
  · exact C84_67
  · exact C84_68
  · exact C84_69
  · exact C84_70
  · exact C84_71
  · exact C84_72
  · exact C84_73
  · exact C84_74
  · exact C84_75
  · exact C84_76
  · exact C84_77
  · exact C84_78
  · exact C84_79
  · exact C84_80
  · exact C84_81
  · exact C84_82
  · exact C84_83
  · exact C84_84
  · exact C84_85
  · exact C84_86
  · exact C84_87
  · exact C84_88
  · exact C84_89

def T84 : Q 7 ((R1.drop 84).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 84).take 1) (by decide +kernel) S84

def Z85 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 85).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_0 : Q 6 ((Z85.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_1 : Q 6 ((Z85.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_2 : Q 6 ((Z85.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_3 : Q 6 ((Z85.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_4 : Q 6 ((Z85.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_5 : Q 6 ((Z85.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_6 : Q 6 ((Z85.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_7 : Q 6 ((Z85.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_8 : Q 6 ((Z85.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_9 : Q 6 ((Z85.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_10 : Q 6 ((Z85.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_11 : Q 6 ((Z85.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_12 : Q 6 ((Z85.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_13 : Q 6 ((Z85.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_14 : Q 6 ((Z85.drop 112).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C85_15 : Q 6 ((Z85.drop 120).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S85 : Q 6 Z85 = true := by
  refine all_of_chunks Z85 (fun c => !LS G MK 0 31 true 6 c) 8 16 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C85_0
  · exact C85_1
  · exact C85_2
  · exact C85_3
  · exact C85_4
  · exact C85_5
  · exact C85_6
  · exact C85_7
  · exact C85_8
  · exact C85_9
  · exact C85_10
  · exact C85_11
  · exact C85_12
  · exact C85_13
  · exact C85_14
  · exact C85_15

def T85 : Q 7 ((R1.drop 85).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 85).take 1) (by decide +kernel) S85

def Z86 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 86).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_0 : Q 6 ((Z86.drop 0).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_1 : Q 6 ((Z86.drop 1).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_2 : Q 6 ((Z86.drop 2).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_3 : Q 6 ((Z86.drop 3).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_4 : Q 6 ((Z86.drop 4).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_5 : Q 6 ((Z86.drop 5).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_6 : Q 6 ((Z86.drop 6).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_7 : Q 6 ((Z86.drop 7).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_8 : Q 6 ((Z86.drop 8).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_9 : Q 6 ((Z86.drop 9).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_10 : Q 6 ((Z86.drop 10).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_11 : Q 6 ((Z86.drop 11).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_12 : Q 6 ((Z86.drop 12).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_13 : Q 6 ((Z86.drop 13).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_14 : Q 6 ((Z86.drop 14).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_15 : Q 6 ((Z86.drop 15).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_16 : Q 6 ((Z86.drop 16).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_17 : Q 6 ((Z86.drop 17).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_18 : Q 6 ((Z86.drop 18).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_19 : Q 6 ((Z86.drop 19).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_20 : Q 6 ((Z86.drop 20).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_21 : Q 6 ((Z86.drop 21).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_22 : Q 6 ((Z86.drop 22).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_23 : Q 6 ((Z86.drop 23).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_24 : Q 6 ((Z86.drop 24).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_25 : Q 6 ((Z86.drop 25).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_26 : Q 6 ((Z86.drop 26).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_27 : Q 6 ((Z86.drop 27).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_28 : Q 6 ((Z86.drop 28).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_29 : Q 6 ((Z86.drop 29).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_30 : Q 6 ((Z86.drop 30).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_31 : Q 6 ((Z86.drop 31).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_32 : Q 6 ((Z86.drop 32).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_33 : Q 6 ((Z86.drop 33).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_34 : Q 6 ((Z86.drop 34).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_35 : Q 6 ((Z86.drop 35).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_36 : Q 6 ((Z86.drop 36).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_37 : Q 6 ((Z86.drop 37).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_38 : Q 6 ((Z86.drop 38).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_39 : Q 6 ((Z86.drop 39).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_40 : Q 6 ((Z86.drop 40).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_41 : Q 6 ((Z86.drop 41).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_42 : Q 6 ((Z86.drop 42).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_43 : Q 6 ((Z86.drop 43).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_44 : Q 6 ((Z86.drop 44).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_45 : Q 6 ((Z86.drop 45).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_46 : Q 6 ((Z86.drop 46).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_47 : Q 6 ((Z86.drop 47).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_48 : Q 6 ((Z86.drop 48).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_49 : Q 6 ((Z86.drop 49).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_50 : Q 6 ((Z86.drop 50).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_51 : Q 6 ((Z86.drop 51).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_52 : Q 6 ((Z86.drop 52).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_53 : Q 6 ((Z86.drop 53).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_54 : Q 6 ((Z86.drop 54).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_55 : Q 6 ((Z86.drop 55).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_56 : Q 6 ((Z86.drop 56).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_57 : Q 6 ((Z86.drop 57).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_58 : Q 6 ((Z86.drop 58).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_59 : Q 6 ((Z86.drop 59).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_60 : Q 6 ((Z86.drop 60).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_61 : Q 6 ((Z86.drop 61).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_62 : Q 6 ((Z86.drop 62).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_63 : Q 6 ((Z86.drop 63).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_64 : Q 6 ((Z86.drop 64).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_65 : Q 6 ((Z86.drop 65).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_66 : Q 6 ((Z86.drop 66).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_67 : Q 6 ((Z86.drop 67).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_68 : Q 6 ((Z86.drop 68).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_69 : Q 6 ((Z86.drop 69).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_70 : Q 6 ((Z86.drop 70).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_71 : Q 6 ((Z86.drop 71).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_72 : Q 6 ((Z86.drop 72).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_73 : Q 6 ((Z86.drop 73).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_74 : Q 6 ((Z86.drop 74).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_75 : Q 6 ((Z86.drop 75).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_76 : Q 6 ((Z86.drop 76).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_77 : Q 6 ((Z86.drop 77).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_78 : Q 6 ((Z86.drop 78).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_79 : Q 6 ((Z86.drop 79).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_80 : Q 6 ((Z86.drop 80).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_81 : Q 6 ((Z86.drop 81).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_82 : Q 6 ((Z86.drop 82).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_83 : Q 6 ((Z86.drop 83).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_84 : Q 6 ((Z86.drop 84).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_85 : Q 6 ((Z86.drop 85).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_86 : Q 6 ((Z86.drop 86).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_87 : Q 6 ((Z86.drop 87).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_88 : Q 6 ((Z86.drop 88).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C86_89 : Q 6 ((Z86.drop 89).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S86 : Q 6 Z86 = true := by
  refine all_of_chunks Z86 (fun c => !LS G MK 0 31 true 6 c) 1 90 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C86_0
  · exact C86_1
  · exact C86_2
  · exact C86_3
  · exact C86_4
  · exact C86_5
  · exact C86_6
  · exact C86_7
  · exact C86_8
  · exact C86_9
  · exact C86_10
  · exact C86_11
  · exact C86_12
  · exact C86_13
  · exact C86_14
  · exact C86_15
  · exact C86_16
  · exact C86_17
  · exact C86_18
  · exact C86_19
  · exact C86_20
  · exact C86_21
  · exact C86_22
  · exact C86_23
  · exact C86_24
  · exact C86_25
  · exact C86_26
  · exact C86_27
  · exact C86_28
  · exact C86_29
  · exact C86_30
  · exact C86_31
  · exact C86_32
  · exact C86_33
  · exact C86_34
  · exact C86_35
  · exact C86_36
  · exact C86_37
  · exact C86_38
  · exact C86_39
  · exact C86_40
  · exact C86_41
  · exact C86_42
  · exact C86_43
  · exact C86_44
  · exact C86_45
  · exact C86_46
  · exact C86_47
  · exact C86_48
  · exact C86_49
  · exact C86_50
  · exact C86_51
  · exact C86_52
  · exact C86_53
  · exact C86_54
  · exact C86_55
  · exact C86_56
  · exact C86_57
  · exact C86_58
  · exact C86_59
  · exact C86_60
  · exact C86_61
  · exact C86_62
  · exact C86_63
  · exact C86_64
  · exact C86_65
  · exact C86_66
  · exact C86_67
  · exact C86_68
  · exact C86_69
  · exact C86_70
  · exact C86_71
  · exact C86_72
  · exact C86_73
  · exact C86_74
  · exact C86_75
  · exact C86_76
  · exact C86_77
  · exact C86_78
  · exact C86_79
  · exact C86_80
  · exact C86_81
  · exact C86_82
  · exact C86_83
  · exact C86_84
  · exact C86_85
  · exact C86_86
  · exact C86_87
  · exact C86_88
  · exact C86_89

def T86 : Q 7 ((R1.drop 86).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 86).take 1) (by decide +kernel) S86

def Z87 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 87).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_0 : Q 6 ((Z87.drop 0).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_1 : Q 6 ((Z87.drop 8).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_2 : Q 6 ((Z87.drop 16).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_3 : Q 6 ((Z87.drop 24).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_4 : Q 6 ((Z87.drop 32).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_5 : Q 6 ((Z87.drop 40).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_6 : Q 6 ((Z87.drop 48).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_7 : Q 6 ((Z87.drop 56).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_8 : Q 6 ((Z87.drop 64).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_9 : Q 6 ((Z87.drop 72).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_10 : Q 6 ((Z87.drop 80).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_11 : Q 6 ((Z87.drop 88).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_12 : Q 6 ((Z87.drop 96).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_13 : Q 6 ((Z87.drop 104).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_14 : Q 6 ((Z87.drop 112).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C87_15 : Q 6 ((Z87.drop 120).take 8) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S87 : Q 6 Z87 = true := by
  refine all_of_chunks Z87 (fun c => !LS G MK 0 31 true 6 c) 8 16 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C87_0
  · exact C87_1
  · exact C87_2
  · exact C87_3
  · exact C87_4
  · exact C87_5
  · exact C87_6
  · exact C87_7
  · exact C87_8
  · exact C87_9
  · exact C87_10
  · exact C87_11
  · exact C87_12
  · exact C87_13
  · exact C87_14
  · exact C87_15

def T87 : Q 7 ((R1.drop 87).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 87).take 1) (by decide +kernel) S87

def Z88 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 88).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_0 : Q 6 ((Z88.drop 0).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_1 : Q 6 ((Z88.drop 4).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_2 : Q 6 ((Z88.drop 8).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_3 : Q 6 ((Z88.drop 12).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_4 : Q 6 ((Z88.drop 16).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_5 : Q 6 ((Z88.drop 20).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_6 : Q 6 ((Z88.drop 24).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_7 : Q 6 ((Z88.drop 28).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_8 : Q 6 ((Z88.drop 32).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_9 : Q 6 ((Z88.drop 36).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_10 : Q 6 ((Z88.drop 40).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_11 : Q 6 ((Z88.drop 44).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_12 : Q 6 ((Z88.drop 48).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_13 : Q 6 ((Z88.drop 52).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_14 : Q 6 ((Z88.drop 56).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_15 : Q 6 ((Z88.drop 60).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_16 : Q 6 ((Z88.drop 64).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_17 : Q 6 ((Z88.drop 68).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_18 : Q 6 ((Z88.drop 72).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_19 : Q 6 ((Z88.drop 76).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_20 : Q 6 ((Z88.drop 80).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_21 : Q 6 ((Z88.drop 84).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C88_22 : Q 6 ((Z88.drop 88).take 4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S88 : Q 6 Z88 = true := by
  refine all_of_chunks Z88 (fun c => !LS G MK 0 31 true 6 c) 4 23 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C88_0
  · exact C88_1
  · exact C88_2
  · exact C88_3
  · exact C88_4
  · exact C88_5
  · exact C88_6
  · exact C88_7
  · exact C88_8
  · exact C88_9
  · exact C88_10
  · exact C88_11
  · exact C88_12
  · exact C88_13
  · exact C88_14
  · exact C88_15
  · exact C88_16
  · exact C88_17
  · exact C88_18
  · exact C88_19
  · exact C88_20
  · exact C88_21
  · exact C88_22

def T88 : Q 7 ((R1.drop 88).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 88).take 1) (by decide +kernel) S88

def Z89 : List (List ℕ) := expand MK 0 31 true 6 ((R1.drop 89).take 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_0 : Q 6 ((Z89.drop 0).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_1 : Q 6 ((Z89.drop 2).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_2 : Q 6 ((Z89.drop 4).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_3 : Q 6 ((Z89.drop 6).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_4 : Q 6 ((Z89.drop 8).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_5 : Q 6 ((Z89.drop 10).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_6 : Q 6 ((Z89.drop 12).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_7 : Q 6 ((Z89.drop 14).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_8 : Q 6 ((Z89.drop 16).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_9 : Q 6 ((Z89.drop 18).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_10 : Q 6 ((Z89.drop 20).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_11 : Q 6 ((Z89.drop 22).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_12 : Q 6 ((Z89.drop 24).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_13 : Q 6 ((Z89.drop 26).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_14 : Q 6 ((Z89.drop 28).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_15 : Q 6 ((Z89.drop 30).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_16 : Q 6 ((Z89.drop 32).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_17 : Q 6 ((Z89.drop 34).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_18 : Q 6 ((Z89.drop 36).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_19 : Q 6 ((Z89.drop 38).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_20 : Q 6 ((Z89.drop 40).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_21 : Q 6 ((Z89.drop 42).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_22 : Q 6 ((Z89.drop 44).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_23 : Q 6 ((Z89.drop 46).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_24 : Q 6 ((Z89.drop 48).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_25 : Q 6 ((Z89.drop 50).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_26 : Q 6 ((Z89.drop 52).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_27 : Q 6 ((Z89.drop 54).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_28 : Q 6 ((Z89.drop 56).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_29 : Q 6 ((Z89.drop 58).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_30 : Q 6 ((Z89.drop 60).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_31 : Q 6 ((Z89.drop 62).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_32 : Q 6 ((Z89.drop 64).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_33 : Q 6 ((Z89.drop 66).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_34 : Q 6 ((Z89.drop 68).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_35 : Q 6 ((Z89.drop 70).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_36 : Q 6 ((Z89.drop 72).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_37 : Q 6 ((Z89.drop 74).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_38 : Q 6 ((Z89.drop 76).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_39 : Q 6 ((Z89.drop 78).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_40 : Q 6 ((Z89.drop 80).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_41 : Q 6 ((Z89.drop 82).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_42 : Q 6 ((Z89.drop 84).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_43 : Q 6 ((Z89.drop 86).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_44 : Q 6 ((Z89.drop 88).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_45 : Q 6 ((Z89.drop 90).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_46 : Q 6 ((Z89.drop 92).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_47 : Q 6 ((Z89.drop 94).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_48 : Q 6 ((Z89.drop 96).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_49 : Q 6 ((Z89.drop 98).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_50 : Q 6 ((Z89.drop 100).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_51 : Q 6 ((Z89.drop 102).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_52 : Q 6 ((Z89.drop 104).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_53 : Q 6 ((Z89.drop 106).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_54 : Q 6 ((Z89.drop 108).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_55 : Q 6 ((Z89.drop 110).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_56 : Q 6 ((Z89.drop 112).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_57 : Q 6 ((Z89.drop 114).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_58 : Q 6 ((Z89.drop 116).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_59 : Q 6 ((Z89.drop 118).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_60 : Q 6 ((Z89.drop 120).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_61 : Q 6 ((Z89.drop 122).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_62 : Q 6 ((Z89.drop 124).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def C89_63 : Q 6 ((Z89.drop 126).take 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def S89 : Q 6 Z89 = true := by
  refine all_of_chunks Z89 (fun c => !LS G MK 0 31 true 6 c) 2 64 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact C89_0
  · exact C89_1
  · exact C89_2
  · exact C89_3
  · exact C89_4
  · exact C89_5
  · exact C89_6
  · exact C89_7
  · exact C89_8
  · exact C89_9
  · exact C89_10
  · exact C89_11
  · exact C89_12
  · exact C89_13
  · exact C89_14
  · exact C89_15
  · exact C89_16
  · exact C89_17
  · exact C89_18
  · exact C89_19
  · exact C89_20
  · exact C89_21
  · exact C89_22
  · exact C89_23
  · exact C89_24
  · exact C89_25
  · exact C89_26
  · exact C89_27
  · exact C89_28
  · exact C89_29
  · exact C89_30
  · exact C89_31
  · exact C89_32
  · exact C89_33
  · exact C89_34
  · exact C89_35
  · exact C89_36
  · exact C89_37
  · exact C89_38
  · exact C89_39
  · exact C89_40
  · exact C89_41
  · exact C89_42
  · exact C89_43
  · exact C89_44
  · exact C89_45
  · exact C89_46
  · exact C89_47
  · exact C89_48
  · exact C89_49
  · exact C89_50
  · exact C89_51
  · exact C89_52
  · exact C89_53
  · exact C89_54
  · exact C89_55
  · exact C89_56
  · exact C89_57
  · exact C89_58
  · exact C89_59
  · exact C89_60
  · exact C89_61
  · exact C89_62
  · exact C89_63

def T89 : Q 7 ((R1.drop 89).take 1) = true :=
  split_all G MK 0 31 true 6 ((R1.drop 89).take 1) (by decide +kernel) S89

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T90 : Q 7 ((R1.drop 90).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T91 : Q 7 ((R1.drop 91).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T92 : Q 7 ((R1.drop 92).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T93 : Q 7 ((R1.drop 93).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T94 : Q 7 ((R1.drop 94).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T95 : Q 7 ((R1.drop 95).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T96 : Q 7 ((R1.drop 96).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T97 : Q 7 ((R1.drop 97).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T98 : Q 7 ((R1.drop 98).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T99 : Q 7 ((R1.drop 99).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T100 : Q 7 ((R1.drop 100).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T101 : Q 7 ((R1.drop 101).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T102 : Q 7 ((R1.drop 102).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T103 : Q 7 ((R1.drop 103).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T104 : Q 7 ((R1.drop 104).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T105 : Q 7 ((R1.drop 105).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T106 : Q 7 ((R1.drop 106).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T107 : Q 7 ((R1.drop 107).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T108 : Q 7 ((R1.drop 108).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T109 : Q 7 ((R1.drop 109).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T110 : Q 7 ((R1.drop 110).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T111 : Q 7 ((R1.drop 111).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T112 : Q 7 ((R1.drop 112).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T113 : Q 7 ((R1.drop 113).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T114 : Q 7 ((R1.drop 114).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T115 : Q 7 ((R1.drop 115).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T116 : Q 7 ((R1.drop 116).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T117 : Q 7 ((R1.drop 117).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T118 : Q 7 ((R1.drop 118).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T119 : Q 7 ((R1.drop 119).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T120 : Q 7 ((R1.drop 120).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T121 : Q 7 ((R1.drop 121).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T122 : Q 7 ((R1.drop 122).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T123 : Q 7 ((R1.drop 123).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T124 : Q 7 ((R1.drop 124).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T125 : Q 7 ((R1.drop 125).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T126 : Q 7 ((R1.drop 126).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T127 : Q 7 ((R1.drop 127).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T128 : Q 7 ((R1.drop 128).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T129 : Q 7 ((R1.drop 129).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T130 : Q 7 ((R1.drop 130).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T131 : Q 7 ((R1.drop 131).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T132 : Q 7 ((R1.drop 132).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T133 : Q 7 ((R1.drop 133).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T134 : Q 7 ((R1.drop 134).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T135 : Q 7 ((R1.drop 135).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T136 : Q 7 ((R1.drop 136).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T137 : Q 7 ((R1.drop 137).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T138 : Q 7 ((R1.drop 138).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T139 : Q 7 ((R1.drop 139).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T140 : Q 7 ((R1.drop 140).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T141 : Q 7 ((R1.drop 141).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T142 : Q 7 ((R1.drop 142).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T143 : Q 7 ((R1.drop 143).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T144 : Q 7 ((R1.drop 144).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T145 : Q 7 ((R1.drop 145).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T146 : Q 7 ((R1.drop 146).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T147 : Q 7 ((R1.drop 147).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T148 : Q 7 ((R1.drop 148).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T149 : Q 7 ((R1.drop 149).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T150 : Q 7 ((R1.drop 150).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T151 : Q 7 ((R1.drop 151).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T152 : Q 7 ((R1.drop 152).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T153 : Q 7 ((R1.drop 153).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T154 : Q 7 ((R1.drop 154).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T155 : Q 7 ((R1.drop 155).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T156 : Q 7 ((R1.drop 156).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T157 : Q 7 ((R1.drop 157).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T158 : Q 7 ((R1.drop 158).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T159 : Q 7 ((R1.drop 159).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T160 : Q 7 ((R1.drop 160).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T161 : Q 7 ((R1.drop 161).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T162 : Q 7 ((R1.drop 162).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T163 : Q 7 ((R1.drop 163).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T164 : Q 7 ((R1.drop 164).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T165 : Q 7 ((R1.drop 165).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T166 : Q 7 ((R1.drop 166).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T167 : Q 7 ((R1.drop 167).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T168 : Q 7 ((R1.drop 168).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T169 : Q 7 ((R1.drop 169).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T170 : Q 7 ((R1.drop 170).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T171 : Q 7 ((R1.drop 171).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T172 : Q 7 ((R1.drop 172).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T173 : Q 7 ((R1.drop 173).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T174 : Q 7 ((R1.drop 174).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T175 : Q 7 ((R1.drop 175).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T176 : Q 7 ((R1.drop 176).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T177 : Q 7 ((R1.drop 177).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T178 : Q 7 ((R1.drop 178).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T179 : Q 7 ((R1.drop 179).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T180 : Q 7 ((R1.drop 180).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T181 : Q 7 ((R1.drop 181).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T182 : Q 7 ((R1.drop 182).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T183 : Q 7 ((R1.drop 183).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T184 : Q 7 ((R1.drop 184).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T185 : Q 7 ((R1.drop 185).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T186 : Q 7 ((R1.drop 186).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T187 : Q 7 ((R1.drop 187).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T188 : Q 7 ((R1.drop 188).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T189 : Q 7 ((R1.drop 189).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T190 : Q 7 ((R1.drop 190).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T191 : Q 7 ((R1.drop 191).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T192 : Q 7 ((R1.drop 192).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T193 : Q 7 ((R1.drop 193).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T194 : Q 7 ((R1.drop 194).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T195 : Q 7 ((R1.drop 195).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T196 : Q 7 ((R1.drop 196).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T197 : Q 7 ((R1.drop 197).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T198 : Q 7 ((R1.drop 198).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T199 : Q 7 ((R1.drop 199).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T200 : Q 7 ((R1.drop 200).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T201 : Q 7 ((R1.drop 201).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T202 : Q 7 ((R1.drop 202).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T203 : Q 7 ((R1.drop 203).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T204 : Q 7 ((R1.drop 204).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T205 : Q 7 ((R1.drop 205).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T206 : Q 7 ((R1.drop 206).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T207 : Q 7 ((R1.drop 207).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T208 : Q 7 ((R1.drop 208).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T209 : Q 7 ((R1.drop 209).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T210 : Q 7 ((R1.drop 210).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T211 : Q 7 ((R1.drop 211).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T212 : Q 7 ((R1.drop 212).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T213 : Q 7 ((R1.drop 213).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T214 : Q 7 ((R1.drop 214).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T215 : Q 7 ((R1.drop 215).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T216 : Q 7 ((R1.drop 216).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T217 : Q 7 ((R1.drop 217).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T218 : Q 7 ((R1.drop 218).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T219 : Q 7 ((R1.drop 219).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T220 : Q 7 ((R1.drop 220).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T221 : Q 7 ((R1.drop 221).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T222 : Q 7 ((R1.drop 222).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T223 : Q 7 ((R1.drop 223).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T224 : Q 7 ((R1.drop 224).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T225 : Q 7 ((R1.drop 225).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T226 : Q 7 ((R1.drop 226).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T227 : Q 7 ((R1.drop 227).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T228 : Q 7 ((R1.drop 228).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T229 : Q 7 ((R1.drop 229).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T230 : Q 7 ((R1.drop 230).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T231 : Q 7 ((R1.drop 231).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T232 : Q 7 ((R1.drop 232).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T233 : Q 7 ((R1.drop 233).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T234 : Q 7 ((R1.drop 234).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T235 : Q 7 ((R1.drop 235).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T236 : Q 7 ((R1.drop 236).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T237 : Q 7 ((R1.drop 237).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T238 : Q 7 ((R1.drop 238).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T239 : Q 7 ((R1.drop 239).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T240 : Q 7 ((R1.drop 240).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T241 : Q 7 ((R1.drop 241).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T242 : Q 7 ((R1.drop 242).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T243 : Q 7 ((R1.drop 243).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T244 : Q 7 ((R1.drop 244).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T245 : Q 7 ((R1.drop 245).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T246 : Q 7 ((R1.drop 246).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T247 : Q 7 ((R1.drop 247).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T248 : Q 7 ((R1.drop 248).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T249 : Q 7 ((R1.drop 249).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T250 : Q 7 ((R1.drop 250).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T251 : Q 7 ((R1.drop 251).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T252 : Q 7 ((R1.drop 252).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T253 : Q 7 ((R1.drop 253).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T254 : Q 7 ((R1.drop 254).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T255 : Q 7 ((R1.drop 255).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T256 : Q 7 ((R1.drop 256).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T257 : Q 7 ((R1.drop 257).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T258 : Q 7 ((R1.drop 258).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T259 : Q 7 ((R1.drop 259).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T260 : Q 7 ((R1.drop 260).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T261 : Q 7 ((R1.drop 261).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T262 : Q 7 ((R1.drop 262).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T263 : Q 7 ((R1.drop 263).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T264 : Q 7 ((R1.drop 264).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T265 : Q 7 ((R1.drop 265).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T266 : Q 7 ((R1.drop 266).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T267 : Q 7 ((R1.drop 267).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T268 : Q 7 ((R1.drop 268).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T269 : Q 7 ((R1.drop 269).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T270 : Q 7 ((R1.drop 270).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T271 : Q 7 ((R1.drop 271).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T272 : Q 7 ((R1.drop 272).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T273 : Q 7 ((R1.drop 273).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T274 : Q 7 ((R1.drop 274).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T275 : Q 7 ((R1.drop 275).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T276 : Q 7 ((R1.drop 276).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T277 : Q 7 ((R1.drop 277).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T278 : Q 7 ((R1.drop 278).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T279 : Q 7 ((R1.drop 279).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T280 : Q 7 ((R1.drop 280).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T281 : Q 7 ((R1.drop 281).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T282 : Q 7 ((R1.drop 282).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T283 : Q 7 ((R1.drop 283).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T284 : Q 7 ((R1.drop 284).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T285 : Q 7 ((R1.drop 285).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T286 : Q 7 ((R1.drop 286).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T287 : Q 7 ((R1.drop 287).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T288 : Q 7 ((R1.drop 288).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T289 : Q 7 ((R1.drop 289).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T290 : Q 7 ((R1.drop 290).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T291 : Q 7 ((R1.drop 291).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T292 : Q 7 ((R1.drop 292).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T293 : Q 7 ((R1.drop 293).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T294 : Q 7 ((R1.drop 294).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T295 : Q 7 ((R1.drop 295).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T296 : Q 7 ((R1.drop 296).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T297 : Q 7 ((R1.drop 297).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T298 : Q 7 ((R1.drop 298).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T299 : Q 7 ((R1.drop 299).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T300 : Q 7 ((R1.drop 300).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T301 : Q 7 ((R1.drop 301).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T302 : Q 7 ((R1.drop 302).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T303 : Q 7 ((R1.drop 303).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T304 : Q 7 ((R1.drop 304).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T305 : Q 7 ((R1.drop 305).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T306 : Q 7 ((R1.drop 306).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T307 : Q 7 ((R1.drop 307).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T308 : Q 7 ((R1.drop 308).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T309 : Q 7 ((R1.drop 309).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T310 : Q 7 ((R1.drop 310).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T311 : Q 7 ((R1.drop 311).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T312 : Q 7 ((R1.drop 312).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T313 : Q 7 ((R1.drop 313).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T314 : Q 7 ((R1.drop 314).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T315 : Q 7 ((R1.drop 315).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T316 : Q 7 ((R1.drop 316).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T317 : Q 7 ((R1.drop 317).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T318 : Q 7 ((R1.drop 318).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T319 : Q 7 ((R1.drop 319).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T320 : Q 7 ((R1.drop 320).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T321 : Q 7 ((R1.drop 321).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T322 : Q 7 ((R1.drop 322).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T323 : Q 7 ((R1.drop 323).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T324 : Q 7 ((R1.drop 324).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T325 : Q 7 ((R1.drop 325).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T326 : Q 7 ((R1.drop 326).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T327 : Q 7 ((R1.drop 327).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T328 : Q 7 ((R1.drop 328).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T329 : Q 7 ((R1.drop 329).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T330 : Q 7 ((R1.drop 330).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T331 : Q 7 ((R1.drop 331).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T332 : Q 7 ((R1.drop 332).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T333 : Q 7 ((R1.drop 333).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T334 : Q 7 ((R1.drop 334).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T335 : Q 7 ((R1.drop 335).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T336 : Q 7 ((R1.drop 336).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T337 : Q 7 ((R1.drop 337).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T338 : Q 7 ((R1.drop 338).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T339 : Q 7 ((R1.drop 339).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T340 : Q 7 ((R1.drop 340).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T341 : Q 7 ((R1.drop 341).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T342 : Q 7 ((R1.drop 342).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T343 : Q 7 ((R1.drop 343).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T344 : Q 7 ((R1.drop 344).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T345 : Q 7 ((R1.drop 345).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T346 : Q 7 ((R1.drop 346).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T347 : Q 7 ((R1.drop 347).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T348 : Q 7 ((R1.drop 348).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T349 : Q 7 ((R1.drop 349).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T350 : Q 7 ((R1.drop 350).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T351 : Q 7 ((R1.drop 351).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T352 : Q 7 ((R1.drop 352).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T353 : Q 7 ((R1.drop 353).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T354 : Q 7 ((R1.drop 354).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T355 : Q 7 ((R1.drop 355).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T356 : Q 7 ((R1.drop 356).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T357 : Q 7 ((R1.drop 357).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T358 : Q 7 ((R1.drop 358).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T359 : Q 7 ((R1.drop 359).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T360 : Q 7 ((R1.drop 360).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T361 : Q 7 ((R1.drop 361).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T362 : Q 7 ((R1.drop 362).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def T363 : Q 7 ((R1.drop 363).take 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
def searchR1 : Q 7 R1 = true := by
  refine all_of_chunks R1 (fun c => !LS G MK 0 31 true 7 c) 1 364 (by decide +kernel) ?_
  intro i hi
  interval_cases i
  · exact T0
  · exact T1
  · exact T2
  · exact T3
  · exact T4
  · exact T5
  · exact T6
  · exact T7
  · exact T8
  · exact T9
  · exact T10
  · exact T11
  · exact T12
  · exact T13
  · exact T14
  · exact T15
  · exact T16
  · exact T17
  · exact T18
  · exact T19
  · exact T20
  · exact T21
  · exact T22
  · exact T23
  · exact T24
  · exact T25
  · exact T26
  · exact T27
  · exact T28
  · exact T29
  · exact T30
  · exact T31
  · exact T32
  · exact T33
  · exact T34
  · exact T35
  · exact T36
  · exact T37
  · exact T38
  · exact T39
  · exact T40
  · exact T41
  · exact T42
  · exact T43
  · exact T44
  · exact T45
  · exact T46
  · exact T47
  · exact T48
  · exact T49
  · exact T50
  · exact T51
  · exact T52
  · exact T53
  · exact T54
  · exact T55
  · exact T56
  · exact T57
  · exact T58
  · exact T59
  · exact T60
  · exact T61
  · exact T62
  · exact T63
  · exact T64
  · exact T65
  · exact T66
  · exact T67
  · exact T68
  · exact T69
  · exact T70
  · exact T71
  · exact T72
  · exact T73
  · exact T74
  · exact T75
  · exact T76
  · exact T77
  · exact T78
  · exact T79
  · exact T80
  · exact T81
  · exact T82
  · exact T83
  · exact T84
  · exact T85
  · exact T86
  · exact T87
  · exact T88
  · exact T89
  · exact T90
  · exact T91
  · exact T92
  · exact T93
  · exact T94
  · exact T95
  · exact T96
  · exact T97
  · exact T98
  · exact T99
  · exact T100
  · exact T101
  · exact T102
  · exact T103
  · exact T104
  · exact T105
  · exact T106
  · exact T107
  · exact T108
  · exact T109
  · exact T110
  · exact T111
  · exact T112
  · exact T113
  · exact T114
  · exact T115
  · exact T116
  · exact T117
  · exact T118
  · exact T119
  · exact T120
  · exact T121
  · exact T122
  · exact T123
  · exact T124
  · exact T125
  · exact T126
  · exact T127
  · exact T128
  · exact T129
  · exact T130
  · exact T131
  · exact T132
  · exact T133
  · exact T134
  · exact T135
  · exact T136
  · exact T137
  · exact T138
  · exact T139
  · exact T140
  · exact T141
  · exact T142
  · exact T143
  · exact T144
  · exact T145
  · exact T146
  · exact T147
  · exact T148
  · exact T149
  · exact T150
  · exact T151
  · exact T152
  · exact T153
  · exact T154
  · exact T155
  · exact T156
  · exact T157
  · exact T158
  · exact T159
  · exact T160
  · exact T161
  · exact T162
  · exact T163
  · exact T164
  · exact T165
  · exact T166
  · exact T167
  · exact T168
  · exact T169
  · exact T170
  · exact T171
  · exact T172
  · exact T173
  · exact T174
  · exact T175
  · exact T176
  · exact T177
  · exact T178
  · exact T179
  · exact T180
  · exact T181
  · exact T182
  · exact T183
  · exact T184
  · exact T185
  · exact T186
  · exact T187
  · exact T188
  · exact T189
  · exact T190
  · exact T191
  · exact T192
  · exact T193
  · exact T194
  · exact T195
  · exact T196
  · exact T197
  · exact T198
  · exact T199
  · exact T200
  · exact T201
  · exact T202
  · exact T203
  · exact T204
  · exact T205
  · exact T206
  · exact T207
  · exact T208
  · exact T209
  · exact T210
  · exact T211
  · exact T212
  · exact T213
  · exact T214
  · exact T215
  · exact T216
  · exact T217
  · exact T218
  · exact T219
  · exact T220
  · exact T221
  · exact T222
  · exact T223
  · exact T224
  · exact T225
  · exact T226
  · exact T227
  · exact T228
  · exact T229
  · exact T230
  · exact T231
  · exact T232
  · exact T233
  · exact T234
  · exact T235
  · exact T236
  · exact T237
  · exact T238
  · exact T239
  · exact T240
  · exact T241
  · exact T242
  · exact T243
  · exact T244
  · exact T245
  · exact T246
  · exact T247
  · exact T248
  · exact T249
  · exact T250
  · exact T251
  · exact T252
  · exact T253
  · exact T254
  · exact T255
  · exact T256
  · exact T257
  · exact T258
  · exact T259
  · exact T260
  · exact T261
  · exact T262
  · exact T263
  · exact T264
  · exact T265
  · exact T266
  · exact T267
  · exact T268
  · exact T269
  · exact T270
  · exact T271
  · exact T272
  · exact T273
  · exact T274
  · exact T275
  · exact T276
  · exact T277
  · exact T278
  · exact T279
  · exact T280
  · exact T281
  · exact T282
  · exact T283
  · exact T284
  · exact T285
  · exact T286
  · exact T287
  · exact T288
  · exact T289
  · exact T290
  · exact T291
  · exact T292
  · exact T293
  · exact T294
  · exact T295
  · exact T296
  · exact T297
  · exact T298
  · exact T299
  · exact T300
  · exact T301
  · exact T302
  · exact T303
  · exact T304
  · exact T305
  · exact T306
  · exact T307
  · exact T308
  · exact T309
  · exact T310
  · exact T311
  · exact T312
  · exact T313
  · exact T314
  · exact T315
  · exact T316
  · exact T317
  · exact T318
  · exact T319
  · exact T320
  · exact T321
  · exact T322
  · exact T323
  · exact T324
  · exact T325
  · exact T326
  · exact T327
  · exact T328
  · exact T329
  · exact T330
  · exact T331
  · exact T332
  · exact T333
  · exact T334
  · exact T335
  · exact T336
  · exact T337
  · exact T338
  · exact T339
  · exact T340
  · exact T341
  · exact T342
  · exact T343
  · exact T344
  · exact T345
  · exact T346
  · exact T347
  · exact T348
  · exact T349
  · exact T350
  · exact T351
  · exact T352
  · exact T353
  · exact T354
  · exact T355
  · exact T356
  · exact T357
  · exact T358
  · exact T359
  · exact T360
  · exact T361
  · exact T362
  · exact T363

def search : Q 8 R0 = true :=
  split_all G MK 0 31 true 7 R0 (by decide +kernel) searchR1

lemma no_five : ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5,
    C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
      (4443 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  refuteT 4443 8 0 31 62 G MK I E
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) search

end PEqualNP.Outside.L_meta_24717_aux.Circ

theorem PEqualNP.Outside.L_meta_24717 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_24717_aux.helper8_restriction PEqualNP.Outside.L_meta_24717_aux.Circ.no_five
