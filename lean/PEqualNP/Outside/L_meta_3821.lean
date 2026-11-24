import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


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
  | [Sum.inr j, Sum.inr k] =>
    if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
    if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)


def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_duplicate (op : GateOp) (m : ℕ) (s : Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) : simplify op m [s, s] = (none, s) := by
  rcases hop with rfl | rfl <;> cases s with
  | inl b => cases b <;> rfl
  | inr j => simp [simplify, simpAnd, simpOr]

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> split_ifs at hg <;> simp_all [Ok] <;> subst g <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> split_ifs at hg <;> simp_all [Ok] <;> subst g <;> simp
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
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom] <;>
        split_ifs <;> simp_all [Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom] <;>
        split_ifs <;> simp_all [Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
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

def erasedCount (n : ℕ) : List Gate → List Stat × List Gate → ℕ
  | [], _ => 0
  | g :: gs, acc =>
      (if (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.isNone then 1 else 0) +
      erasedCount n gs (elimStep n acc g)

lemma elim_size_exact (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length + erasedCount n gs acc = acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim, erasedCount]
  | cons g gs ih =>
    intro acc
    have h := ih (elimStep n acc g)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, erasedCount, List.length_cons]
    cases ho : (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
    | none =>
      have hl : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append, ho, Option.toList_none, List.length_nil,
          Nat.add_zero]
      simp only [Option.isNone_none, ↓reduceIte]
      omega
    | some q =>
      have hl : (elimStep n acc g).2.length = acc.2.length + 1 := by
        simp only [elimStep, List.length_append, ho, Option.toList_some, List.length_singleton]
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, zero_add]
      omega

lemma restrict_nonconstant (n : ℕ) (C : Circuit) (b : Bool) (hC : FanInTwo C)
    (hnc : ∃ y z : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) ≠
      C.eval (List.ofFn (Fin.snoc z b : Fin (n + 1) → Bool))) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + erasedCount n (C.gates.map normGate) (initStats n b, []) = C.size ∧
      ∀ y : Fin n → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) := by
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, Ok g := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
    exact (normGate_nok g₀ (hC g₀ hg₀)).1
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ hok (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, z, hyz⟩ := hnc
    apply hyz
    rw [← hval y, ← hval z, hst]
    rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
    · exact elim_ok n gs (initStats n b, []) (by simp)
    · have h := elim_size_exact n gs (initStats n b, [])
      simpa [Circuit.size, hgs, ← hacc] using h
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

lemma elim_count_erased (n : ℕ) (acc : List Stat × List Gate) :
    ∀ (gs : List Gate) (S : Finset ℕ),
      (∀ p ∈ S, ∃ g, gs[p]? = some g ∧
        (simplify g.op (n + (elim n (gs.take p) acc).2.length)
          (g.inputs.map fun i => (elim n (gs.take p) acc).1.getD i (Sum.inl false))).1 = none) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      simp [elim, List.foldl_append]
    have ih' := ih (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        have h1 := (List.getElem?_eq_some_iff.1 hg').1
        simp only [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [List.take_append_of_le_length (Nat.le_of_lt hpl)] at hc
      exact ⟨g', hg', hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', hc⟩ := hS gs.length hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst g'
      rw [List.take_append_length] at hc
      have hlen : (elimStep n (elim n gs acc) g).2.length = (elim n gs acc).2.length := by
        change ((elim n gs acc).2 ++ (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1.toList).length = _
        rw [hc]
        simp
      have hcard := Finset.card_erase_of_mem hin
      omega
    · have hlen : (elimStep n (elim n gs acc) g).2.length ≤
          (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have h := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

lemma card_le_erasedCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (S : Finset ℕ)
    (hS : ∀ p ∈ S, ∃ g, gs[p]? = some g ∧
      (simplify g.op (n + (elim n (gs.take p) acc).2.length)
        (g.inputs.map fun i => (elim n (gs.take p) acc).1.getD i (Sum.inl false))).1 = none) :
    S.card ≤ erasedCount n gs acc := by
  have hc := elim_count_erased n acc gs S hS
  have he := elim_size_exact n gs acc
  omega

lemma erasedCount_append (n : ℕ) (gs hs : List Gate) (acc : List Stat × List Gate) :
    erasedCount n (gs ++ hs) acc =
      erasedCount n gs acc + erasedCount n hs (elim n gs acc) := by
  have hfull := elim_size_exact n (gs ++ hs) acc
  have hpre := elim_size_exact n gs acc
  have hpost := elim_size_exact n hs (elim n gs acc)
  have he : elim n (gs ++ hs) acc = elim n hs (elim n gs acc) := by
    simp [elim, List.foldl_append]
  rw [he, List.length_append] at hfull
  omega

lemma restrict_nonconstant_of_erased_set (n : ℕ) (C : Circuit) (b : Bool)
    (hC : FanInTwo C)
    (hnc : ∃ y z : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) ≠
      C.eval (List.ofFn (Fin.snoc z b : Fin (n + 1) → Bool)))
    (S : Finset ℕ)
    (hS : ∀ p ∈ S, ∃ g, (C.gates.map normGate)[p]? = some g ∧
      let acc := elim n ((C.gates.map normGate).take p) (initStats n b, [])
      (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card ≤ C.size ∧
      ∀ y : Fin n → Bool,
        D.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) := by
  obtain ⟨D, hD, hs, he⟩ := restrict_nonconstant n C b hC hnc
  have hc := card_le_erasedCount n (C.gates.map normGate) (initStats n b, []) S hS
  exact ⟨D, hD, by omega, he⟩

def aliasStats (m j : ℕ) : List Stat :=
  List.ofFn (fun i : Fin m => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inr j]

lemma inv_alias (n : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (j : ℕ) (hj : j < n + pre.length) (b : Bool)
    (hb : b = (wiresFrom pre y).getD j false) :
    Inv n y (wiresFrom pre y ++ [b]) (aliasStats (n + pre.length) j, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by
    rw [length_wiresFrom, hy]
  have ls : (List.ofFn (fun i : Fin (n + pre.length) =>
      (Sum.inr (i : ℕ) : Stat))).length = n + pre.length := by simp
  refine ⟨by simp [aliasStats, lw], ?_⟩
  intro i
  change ((aliasStats (n + pre.length) j).getD i (Sum.inl false)).Valid (n + pre.length) ∧
    ((aliasStats (n + pre.length) j).getD i (Sum.inl false)).val (wiresFrom pre y) =
      (wiresFrom pre y ++ [b]).getD i false
  by_cases hi : i = n + pre.length
  · subst i
    simp only [aliasStats]
    rw [getD_snoc_len _ _ _ _ ls, getD_snoc_len _ _ _ _ lw]
    exact ⟨hj, hb.symm⟩
  · simp only [aliasStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n + pre.length
    · simp [hlt, Stat.Valid, Stat.val]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma remove_semantic_alias (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate) (j : ℕ)
    (hgs : C.gates = pre ++ g :: post) (hC : FanInTwo C) (hj : j < n + pre.length)
    (halias : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) =
        (wiresFrom pre (List.ofFn x)).getD j false)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hokpre : ∀ g' ∈ pre, Ok g' := by
    intro g' hg'
    apply hC g'
    rw [hgs]
    exact List.mem_append_left _ hg'
  have hokpost : ∀ g' ∈ post, Ok g' := by
    intro g' hg'
    apply hC g'
    rw [hgs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hg')
  let acc₀ : List Stat × List Gate := (aliasStats (n + pre.length) j, pre)
  let acc := elim n post acc₀
  have hinv : ∀ x : Fin n → Bool, Inv n (List.ofFn x) (C.wires (List.ofFn x)) acc := by
    intro x
    change Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc
    rw [hgs, wiresFrom_append]
    exact inv_elim n (List.ofFn x) (by simp) post _ acc₀ hokpost
      (inv_alias n pre (List.ofFn x) (by simp) j hj _ (halias x))
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn x) := by
    intro x
    exact ((hinv x).2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hst]
    rfl
  | inr k =>
    refine ⟨⟨acc.2, k⟩, ?_, ?_, ?_⟩
    · exact elim_ok n post acc₀ hokpre
    · have hlen : acc.2.length ≤ pre.length + post.length := elim_len n post acc₀
      have hsize : C.size = pre.length + (post.length + 1) := by
        simp [Circuit.size, hgs, Nat.add_assoc]
      change acc.2.length + 1 ≤ C.size
      omega
    · intro x
      have h := hval x
      rw [hst] at h
      exact h

lemma duplicate_gate_value (g : Gate) (mid : List Gate) (w : List Bool)
    (hbound : ∀ i ∈ g.inputs, i < w.length) :
    g.op.eval (g.inputs.map fun i => (wiresFrom (g :: mid) w).getD i false) =
      (wiresFrom (g :: mid) w).getD w.length false := by
  have hin : (g.inputs.map fun i => (wiresFrom (g :: mid) w).getD i false) =
      g.inputs.map fun i => w.getD i false := by
    apply List.map_congr_left
    intro i hi
    exact getD_wiresFrom _ _ _ (hbound i hi)
  rw [hin]
  change _ = (wiresFrom mid (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD
    w.length false
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

lemma remove_duplicate_gate (n : ℕ) (C : Circuit) (pre mid post : List Gate) (g : Gate)
    (hgs : C.gates = pre ++ g :: mid ++ g :: post) (hC : FanInTwo C)
    (hbound : ∀ i ∈ g.inputs, i < n + pre.length)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  apply remove_semantic_alias n C (pre ++ g :: mid) post g (n + pre.length)
    (by simpa [List.append_assoc] using hgs) hC (by simp) ?_ hnc
  intro x
  rw [wiresFrom_append]
  have hw : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
    simp [length_wiresFrom]
  simpa only [hw] using duplicate_gate_value g mid (wiresFrom pre (List.ofFn x))
    (by intro i hi; simpa only [hw] using hbound i hi)

end PEqualNP.Outside.L_meta_3821
