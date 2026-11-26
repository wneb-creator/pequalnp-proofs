import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17563

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
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

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
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

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
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

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
  next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
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

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
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

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
  saved. -/
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

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
  and every old wire has a valid status whose value on the new wires is the old value. -/
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


theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (elim n gs acc).2.length + (gs.filter (fun g => g.inputs.contains k)).length
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.filter_cons]
    by_cases hkg : k ∈ g.inputs
    · have hkc : g.inputs.contains k = true := by simpa using hkg
      rw [if_pos hkc, List.length_cons]
      obtain ⟨c, hc⟩ := hc
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
      omega
    · have hkc : ¬ (g.inputs.contains k = true) := by simpa using hkg
      rw [if_neg hkc]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem readers_eq (gs : List Gate) (k : ℕ) (hok : ∀ g ∈ gs, Ok g) :
    ((gs.map normGate).filter (fun g => g.inputs.contains k)).length
      = (gs.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains k)).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro g hg
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hok _ hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h <;> subst h
  all_goals simp [normGate, GateOp.eval, List.take_of_length_le hlen]
  all_goals exact Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true (of_decide_eq_true h), fun h => decide_eq_true (of_decide_eq_true h)⟩


section supp

variable {n : ℕ}

/-- The support of a gate: the union of the supports of the wires it reads. -/
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

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
  `y` agree on. -/
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

end supp

def Stat.isC : Stat → Bool
  | Stat.const _ => true
  | Stat.wire _ => false

theorem elim_append (n : ℕ) (A B : List Gate) (acc : List Stat × List Gate) :
    elim n (A ++ B) acc = elim n B (elim n A acc) := by
  simp [elim, List.foldl_append]

theorem elim_len1 (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih]; simp [elimStep]; omega

/-- Every gate that reads a wire whose final status is a constant emits nothing. -/
theorem elim_saved (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) →
    (elim n gs acc).2.length + gs.countP (fun g =>
      g.inputs.any (fun a => ((elim n gs acc).1.getD a (Stat.const false)).isC))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _; simp [elim]
  | cons g gs ih =>
    intro acc hok
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    rw [h3, List.countP_cons, List.length_cons]
    set Sf := (elim n gs (elimStep n acc g)).1 with hSf
    by_cases hP : (g.inputs.any (fun a => (Sf.getD a (Stat.const false)).isC)) = true
    · rw [if_pos hP]
      obtain ⟨a, ha, hac⟩ := List.any_eq_true.1 hP
      have hconst : ∃ c, acc.1.getD a (Stat.const false) = Stat.const c := by
        by_cases hal : a < acc.1.length
        · have e : Sf.getD a (Stat.const false) = acc.1.getD a (Stat.const false) := by
            rw [hSf, elim_getD n a _ gs _ (by simp [elimStep]; omega)]
            simp only [elimStep]
            exact getD_snoc_ne _ _ _ _ (by omega)
          rw [e] at hac
          revert hac
          cases acc.1.getD a (Stat.const false) with
          | const c => intro _; exact ⟨c, rfl⟩
          | wire j => intro h; simp [Stat.isC] at h
        · exact ⟨false, List.getD_eq_default _ _ (by omega)⟩
      obtain ⟨c, hc⟩ := hconst
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨a, ha, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      omega
    · rw [if_neg hP]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : Stat.const false ∈ ins) :
    ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem suppsFrom_append {N : ℕ} (A B : List Gate) (L : List (Finset (Fin N))) :
    suppsFrom (A ++ B) L = suppsFrom B (suppsFrom A L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {N : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin N)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; simp [suppsFrom]
  | cons g gs ih =>
    intro L
    have : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [this, ih]; simp; omega

/-- Gates that read no wire of `T` keep input `x` out of the supports of the wires outside
  `T`. -/
theorem supp_avoid {N : ℕ} (x : Fin N) (T : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin N)), (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ T a) →
    (∀ j, ¬ T j → x ∉ L.getD j ∅) → ∀ j, ¬ T j → x ∉ (suppsFrom gs L).getD j ∅ := by
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

theorem supp_one {N : ℕ} (x : Fin N) (T : ℕ → Prop) (g : Gate) (L : List (Finset (Fin N)))
    (hT : T L.length) (h : ∀ j, ¬ T j → x ∉ L.getD j ∅) :
    ∀ j, ¬ T j → x ∉ (suppsFrom [g] L).getD j ∅ := by
  intro j hj
  show x ∉ (L ++ [gateSupp L g]).getD j ∅
  rw [getD_snoc_ne _ _ _ _ (fun e => hj (by rw [e]; exact hT))]
  exact h j hj

theorem inputSupps_avoid (N : ℕ) (i : Fin N) : ∀ j : ℕ, j ≠ i.val →
    i ∉ (inputSupps N).getD j ∅ := by
  intro j hj
  by_cases hlt : j < N
  · have e : (inputSupps N).getD j ∅ = {⟨j, hlt⟩} := by simp [inputSupps, hlt]
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by rw [e'])
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem ofFn_getD (a : List Bool) (N : ℕ) (ha : a.length = N) :
    List.ofFn (fun j : Fin N => a.getD j false) = a := by
  apply List.ext_getElem (by simp [ha])
  intro k h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- If input `i` is not in the support of wire `o`, two inputs that differ only at `i` give
  wire `o` the same value. -/
theorem dep_out (N : ℕ) (gs : List Gate) (o : ℕ) (i : Fin N)
    (hns : i ∉ (suppsFrom gs (inputSupps N)).getD o ∅) (a b : List Bool) (ha : a.length = N)
    (hb : b.length = N) (hab : ∀ j, j ≠ i.val → a.getD j false = b.getD j false) :
    (wiresFrom gs a).getD o false = (wiresFrom gs b).getD o false := by
  have hag := (agree_wiresFrom (fun j : Fin N => a.getD j false) (fun j : Fin N => b.getD j false)
    gs _ _ _ (agree_inputs _ _)).2.2 o (by
      intro k hk
      apply hab
      intro e
      apply hns
      have : k = i := Fin.ext e
      rw [← this]; exact hk)
  rw [ofFn_getD a N ha, ofFn_getD b N hb] at hag
  exact hag

theorem readers_eq' (gs : List Gate) (k : ℕ) (hok : ∀ g ∈ gs, Ok g) :
    ((gs.map normGate).countP (fun g => g.inputs.contains k))
      = (gs.filter (fun g =>
        (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains k)).length := by
  rw [List.countP_eq_length_filter, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro g hg
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hok _ hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h <;> subst h
  all_goals simp [normGate, GateOp.eval]
  all_goals exact Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true (of_decide_eq_true h), fun h => decide_eq_true (of_decide_eq_true h)⟩

def subStats {n : ℕ} (w : List (Option (Fin n))) : List Stat :=
  w.map fun p => p.elim (Stat.const false) (fun q => Stat.wire q.val)

theorem inv_sub (n : ℕ) (w : List (Option (Fin n))) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (w.map fun p => p.elim false y) (subStats w, []) := by
  refine ⟨by simp [subStats], ?_⟩
  intro j
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [subStats, List.getElem?_map]
  cases h : w[j]? with
  | none => exact ⟨trivial, rfl⟩
  | some p =>
    cases p with
    | none => exact ⟨trivial, rfl⟩
    | some q => simp [Stat.Valid, Stat.val, wiresFrom]


theorem main (j : Fin 10) (f : Bool → Bool) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hdep : ∃ a b : Fin 10 → Bool, (∀ i, i ≠ 0 → a i = b i) ∧
      C.eval (List.ofFn a ++ [f (a j)]) ≠ C.eval (List.ofFn b ++ [f (b j)]))
    (hnc : ∃ y z : Fin 9 → Bool,
      C.eval (List.ofFn (Fin.cases false y : Fin 10 → Bool) ++ [f ((Fin.cases false y : Fin 10 → Bool) j)]) ≠
      C.eval (List.ofFn (Fin.cases false z : Fin 10 → Bool) ++ [f ((Fin.cases false z : Fin 10 → Bool) j)])) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size < C.size ∧
      ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [f ((Fin.cases false y : Fin 10 → Bool) j)]) =
        C.eval (List.ofFn (Fin.cases false y : Fin 10 → Bool) ++ [f ((Fin.cases false y : Fin 10 → Bool) j)]) := by
  have ok : ∀ g ∈ C.gates, Ok g := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevD : ∀ a : List Bool, C.eval a = (wiresFrom gs a).getD C.output false := by
    intro a; rw [hgs, wiresFrom_norm]; rfl
  let pin : (Fin 9 → Bool) → Fin 10 → Bool := fun y => Fin.cases false y
  let T0 : ℕ → Prop := fun t => t = 0 ∨ (j.val = 0 ∧ t = 10)
  let sw : List Stat := Stat.const false :: (List.ofFn fun k : Fin 9 => Stat.wire k.val) ++
    [if j.val = 0 then Stat.const (f false) else Stat.wire 9]
  have hswl : sw.length = 11 := by simp [sw]
  have hInv : ∀ y : Fin 9 → Bool, Inv 10 (List.ofFn y ++ [f (pin y j)])
      (List.ofFn (pin y) ++ [f (pin y j)]) (sw, []) := by
    intro y
    refine ⟨by simp [sw], ?_⟩
    intro i
    simp only [List.length_nil, Nat.add_zero]
    by_cases hi : i < 11
    · by_cases hj0 : j.val = 0
      · have hj : j = 0 := Fin.ext hj0
        interval_cases i <;> simp [sw, hj, pin, Stat.Valid, Stat.val, wiresFrom, List.getD_eq_getElem?_getD]
      · interval_cases i <;> simp [sw, hj0, pin, Stat.Valid, Stat.val, wiresFrom, List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ (by rw [hswl]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  set acc := elim 10 gs (sw, []) with hacc
  have hval : ∀ y : Fin 9 → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y ++ [f (pin y j)]))
        = C.eval (List.ofFn (pin y) ++ [f (pin y j)]) := by
    intro y
    have hi := inv_elim 10 _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (hInv y)
    rw [← hacc] at hi
    rw [(hi.2 C.output).2, hevD]
  obtain ⟨jo, hst⟩ : ∃ jo, acc.1.getD C.output (Stat.const false) = Stat.wire jo := by
    cases hst : acc.1.getD C.output (Stat.const false) with
    | wire jo => exact ⟨jo, rfl⟩
    | const c =>
      exfalso
      obtain ⟨a, b, hne⟩ := hnc
      apply hne
      have ha := hval a
      have hb := hval b
      rw [hst] at ha hb
      exact ha.symm.trans hb
  have hTc : ∀ t, T0 t → ∃ c, acc.1.getD t (Stat.const false) = Stat.const c := by
    intro t ht
    have htl : t < sw.length := by rw [hswl]; rcases ht with rfl | ⟨_, rfl⟩ <;> omega
    rw [hacc, elim_getD 10 t _ gs _ htl]
    rcases ht with rfl | ⟨hj0, rfl⟩
    · exact ⟨false, rfl⟩
    · exact ⟨f false, by simp [sw, hj0]⟩
  have hoT : ¬ T0 C.output := by
    intro h
    obtain ⟨c, hc⟩ := hTc _ h
    rw [hc] at hst; cases hst
  have key : ∃ g ∈ gs, ∃ t ∈ g.inputs, T0 t := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    obtain ⟨a, b, hab, hne⟩ := hdep
    apply hne
    set A := List.ofFn a ++ [f (a j)] with hA
    set B := List.ofFn b ++ [f (b j)] with hB
    have hAl : A.length = 11 := by simp [hA]
    have hBl : B.length = 11 := by simp [hB]
    have hag := (agree_wiresFrom (fun k : Fin 11 => A.getD k false) (fun k : Fin 11 => B.getD k false)
      gs _ _ _ (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have hnT : ¬ T0 k.val := by
          intro hT
          apply supp_avoid k T0 gs (inputSupps 11) (fun g hg t ht => hno g hg t ht) (by
            intro j' hj'
            exact inputSupps_avoid 11 k j' (fun e => hj' (e ▸ hT))) C.output hoT
          exact hk
        simp only [T0, not_or, not_and] at hnT
        obtain ⟨hk0, hk10⟩ := hnT
        show (List.ofFn a ++ [f (a j)]).getD k.val false = (List.ofFn b ++ [f (b j)]).getD k.val false
        by_cases hk9 : k.val < 10
        · rw [List.getD_append _ _ _ _ (by simpa using hk9),
            List.getD_append _ _ _ _ (by simpa using hk9)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          have := hab ⟨k.val, hk9⟩ (fun e => hk0 (by simpa using congrArg Fin.val e))
          simp [hk9, this]
        · have hk : k.val = 10 := by omega
          have hjne : j ≠ 0 := fun e => hk10 (by rw [e]; rfl) hk
          rw [hk, List.getD_append_right _ _ _ _ (by simp),
            List.getD_append_right _ _ _ _ (by simp), hab j hjne]
          simp)
    rw [ofFn_getD A 11 hAl, ofFn_getD B 11 hBl] at hag
    rw [hevD, hevD]
    exact hag
  set P := fun g : Gate => g.inputs.any (fun a => (acc.1.getD a (Stat.const false)).isC) with hP
  have hsaved := elim_saved 10 gs (sw, []) hnok
  rw [← hacc] at hsaved
  simp only [List.length_nil, zero_add] at hsaved
  have hP1 : 1 ≤ gs.countP P := by
    obtain ⟨g, hg, t, ht, hT⟩ := key
    obtain ⟨c, hc⟩ := hTc t hT
    have : P g = true := by
      rw [hP]; exact List.any_eq_true.2 ⟨t, ht, by rw [hc]; rfl⟩
    exact List.countP_pos_iff.2 ⟨g, hg, this⟩
  have hgl : gs.length = C.size := by simp [hgs, Circuit.size]
  have hs' : acc.2.length + gs.countP P ≤ gs.length := hsaved
  refine ⟨⟨acc.2, jo⟩, elim_ok 10 gs _ (by simp), ?_, ?_⟩
  · show acc.2.length < C.size
    omega
  · intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_17563

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_17563 in
theorem PEqualNP.Outside.L_meta_17563 :
    ∀ (x1 : Fin (10 : ℕ)) (x2 : Bool → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   have x4 : (Fin (10 : ℕ) → Bool) → Bool := fun (x4 : Fin (10 : ℕ) → Bool) => x3.eval (List.ofFn x4 ++ [x2 (x4 x1)]);   have x5 : (Fin (9 : ℕ) → Bool) → Fin (10 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ) → Bool) (x6 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.cases Bool.false x5 x6;   PEqualNP.MetaComplexity.FanInTwo x3 → (∃ (x7 : Fin (10 : ℕ) → Bool) (x8 : Fin (10 : ℕ) → Bool), (∀ (x9 : Fin (10 : ℕ)), x9 ≠ (0 : Fin (10 : ℕ)) → x7 x9 = x8 x9) ∧ x4 x7 ≠ x4 x8) → (∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), x4 (x5 x8) ≠ x4 (x5 x9)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size < x3.size ∧ ∀ (x10 : Fin (9 : ℕ) → Bool), x9.eval (List.ofFn x10 ++ [x2 (x5 x10 x1)]) = x4 (x5 x10) := by
  intro j f C run pin hC hdep hnc
  exact main j f C hC hdep hnc
