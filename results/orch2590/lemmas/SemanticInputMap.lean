import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590.Semantic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit simplifier is adapted from L_meta_7328 and L_meta_1411
-- in open-goat/pequalnp-proofs under the Apache 2.0 license.
abbrev Stat := Bool ⊕ ℕ

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

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma op_cases {g : Gate} (h : Good g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa using h.1

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Good g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Good]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Good]
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Good g) → Inv n y w acc →
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
    have hs := simplify_sound g.op (op_cases hgok) w' ins (by simpa [hins] using hgok.2)
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

-- Every gate with a constant input can be omitted. An absorbing input
-- additionally marks the gate output as a constant for the next gate.
def absorb : GateOp → Bool
  | .or => true
  | _ => false

lemma simplify_drop (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : ∃ b, Sum.inl b ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨b, hb⟩
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hb hl
  all_goals cases s <;> (try cases t) <;> simp_all [simplify, simpAnd, simpOr]

lemma simplify_absorb (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : Sum.inl (absorb op) ∈ ins) :
    (simplify op m ins).2 = Sum.inl (absorb op) := by
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hc hl
  all_goals cases s <;> (try cases t) <;> simp_all [absorb, simplify, simpAnd, simpOr]
  grind

abbrev State := List Stat × List Gate

def stat (s : State) (i : ℕ) : Stat := s.1.getD i (Sum.inl false)

def plan (n : ℕ) (s : State) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + s.2.length) (g.inputs.map (stat s))

lemma elim_append (n : ℕ) (pre post : List Gate) (s : State) :
    elim n (pre ++ post) s = elim n post (elim n pre s) := by
  simp [elim, List.foldl_append]

lemma elim_extends (n : ℕ) (gs : List Gate) (s : State) :
    ∃ t, (elim n gs s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (elimStep n s g)
    refine ⟨(plan n s g).2 :: t, ?_, by simp [hlen]⟩
    change (elim n gs (elimStep n s g)).1 = _
    rw [ht]
    change (s.1 ++ [(plan n s g).2]) ++ t = _
    simp

lemma elim_stat (n : ℕ) (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    stat (elim n gs s) i = stat s i := by
  obtain ⟨t, ht, _⟩ := elim_extends n gs s
  unfold stat
  rw [ht, List.getD_append _ _ _ _ hi]

lemma elim_good (n : ℕ) (gs : List Gate) (s : State)
    (h : ∀ g ∈ gs, Good g) (hs : ∀ g ∈ s.2, Good g) :
    ∀ g ∈ (elim n gs s).2, Good g := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    change ∀ g' ∈ (elim n gs (elimStep n s g)).2, Good g'
    apply ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    intro a ha
    change a ∈ s.2 ++ (plan n s g).1.toList at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hs a ha
    · exact simplify_ok _ _ _ a (by simpa [plan] using ha)

def fix {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = p then b else x i

def initial {n : ℕ} (p : Fin n) (b : Bool) : State :=
  (List.ofFn fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val, [])

lemma initial_length {n : ℕ} (p : Fin n) (b : Bool) :
    (initial p b).1.length = n := by simp [initial]

lemma initial_stat {n : ℕ} (p : Fin n) (b : Bool) : stat (initial p b) p.val = Sum.inl b := by
  simp [stat, initial]

lemma initial_inv {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (fix p b x)) (initial p b) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (stat (initial p b) j.val).Valid _ ∧ (stat (initial p b) j.val).val _ = _
    by_cases hj : j = p <;>
      simp [stat, initial, fix, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at *
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma drop_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} {b : Bool} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl b) :
    (plan n s g).1 = none := by
  apply simplify_drop _ (op_cases hg) _ _ (by simpa using hg.2)
  exact ⟨b, hb ▸ List.mem_map_of_mem hi⟩

lemma absorb_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl (absorb g.op)) :
    (plan n s g).2 = Sum.inl (absorb g.op) := by
  apply simplify_absorb _ (op_cases hg) _ _ (by simpa using hg.2)
  exact hb ▸ List.mem_map_of_mem hi

lemma restriction (C : Circuit) (hm : Monotone2 C) {n : ℕ} (p : Fin n) (b : Bool)
    (hnc : ∃ x y, circuitFun n C (fix p b x) ≠ circuitFun n C (fix p b y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧
      D.size = (elim n C.gates (initial p b)).2.length := by
  let s := elim n C.gates (initial p b)
  have hval (x : Fin n → Bool) :
      (stat s C.output).val (wiresFrom s.2 (List.ofFn x)) =
        circuitFun n C (fix p b x) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ hm (initial_inv p b x)).2 C.output).2
  cases hz : stat s C.output with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x
    have hy := hval y
    rw [hz] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨s.2, j⟩, elim_good n _ _ hm (by simp [initial]), ?_, rfl⟩
    intro x
    change (wiresFrom s.2 (List.ofFn x)).getD j false = _
    simpa only [hz, Stat.val] using hval x

def droppedSet (n : Nat) : List Gate → State → Finset Nat
  | [], _ => ∅
  | g :: gs, s =>
    let tail := (droppedSet n gs (elimStep n s g)).image Nat.succ
    if (plan n s g).1.isNone then insert 0 tail else tail

lemma elim_drop_count (n : Nat) (gs : List Gate) (s : State) :
    (elim n gs s).2.length + (droppedSet n gs s).card = s.2.length + gs.length := by
  induction gs generalizing s with
  | nil => simp [elim, droppedSet]
  | cons g gs ih =>
    have h := ih (elimStep n s g)
    have zeroMissing : 0 ∉ (droppedSet n gs (elimStep n s g)).image Nat.succ := by simp
    have cardImage : ((droppedSet n gs (elimStep n s g)).image Nat.succ).card =
        (droppedSet n gs (elimStep n s g)).card :=
      Finset.card_image_of_injective _ Nat.succ_injective
    change (elim n gs (elimStep n s g)).2.length +
      (droppedSet n (g :: gs) s).card = _
    have stepLength : (elimStep n s g).2.length = s.2.length + (plan n s g).1.toList.length := by
      change (s.2 ++ (plan n s g).1.toList).length = _
      exact List.length_append
    rw [stepLength] at h
    cases hp : (plan n s g).1 with
    | none =>
      simp only [droppedSet, hp, Option.isNone_none, Bool.true_eq, ↓reduceIte,
        Finset.card_insert_of_notMem zeroMissing, cardImage]
      simp only [hp, Option.toList_none, List.length_nil, Nat.add_zero] at h
      simp only [List.length_cons]
      omega
    | some a =>
      simp only [droppedSet, hp, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, cardImage]
      simp only [hp, Option.toList_some, List.length_singleton] at h
      simp only [List.length_cons]
      omega

lemma droppedSet_member (n : Nat) (gs : List Gate) (s : State) (j : Nat) (hj : j < gs.length) :
    j ∈ droppedSet n gs s ↔
      (plan n (elim n (gs.take j) s) gs[j]).1 = none := by
  induction gs generalizing s j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [droppedSet, List.take_zero, elim, List.foldl_nil, List.getElem_cons_zero]
      cases hp : (plan n s g).1 <;> simp [hp]
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have h := ih (elimStep n s g) j hj'
      simp only [droppedSet, List.take_succ_cons, elim, List.foldl_cons,
        List.getElem_cons_succ] at h ⊢
      cases hp : (plan n s g).1 <;> simpa [hp, Finset.mem_image] using h

lemma restriction_charged {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (p : Fin n) (b : Bool)
    (nonconstant : ∃ x y, circuitFun n C (fix p b x) ≠ circuitFun n C (fix p b y))
    (S : Finset Nat) (bound : ∀ j ∈ S, j < C.gates.length)
    (charge : ∀ j (hj : j ∈ S), (plan n (elim n (C.gates.take j) (initial p b))
      (C.gates[j]'(bound j hj))).1 = none) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧
      D.size + S.card ≤ C.size := by
  obtain ⟨D, good, computes, size⟩ := restriction C mono p b nonconstant
  refine ⟨D, good, computes, ?_⟩
  have sub : S ⊆ droppedSet n C.gates (initial p b) := by
    intro j hj
    exact (droppedSet_member n C.gates (initial p b) j (bound j hj)).mpr (charge j hj)
  have count := elim_drop_count n C.gates (initial p b)
  have card := Finset.card_le_card sub
  have empty : (initial p b).2.length = 0 := rfl
  rw [empty] at count
  change D.size + S.card ≤ C.gates.length
  omega

lemma before_input {n : Nat} (p : Fin n) (b : Bool) (gs : List Gate) :
    stat (elim n gs (initial p b)) p.val = Sum.inl b := by
  rw [elim_stat n gs (initial p b) p.val (by simpa [initial_length] using p.isLt), initial_stat]

lemma direct_reader_charge {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (p : Fin n) (b : Bool) (j : Nat) (hj : j < C.gates.length)
    (reads : p.val ∈ C.gates[j].inputs) :
    (plan n (elim n (C.gates.take j) (initial p b)) C.gates[j]).1 = none := by
  exact drop_at_reader n _ _ (mono _ (List.getElem_mem hj)) reads
    (before_input p b (C.gates.take j))

lemma and_wire_false {n : Nat} (gs : List Gate) (p : Fin n) (j : Nat)
    (hj : j < gs.length) (good : Good gs[j]) (op : gs[j].op = GateOp.and)
    (reads : p.val ∈ gs[j].inputs) :
    stat (elim n gs (initial p false)) (n + j) = Sum.inl false := by
  let pre := gs.take j
  let g := gs[j]
  let post := gs.drop (j + 1)
  let s := elim n pre (initial p false)
  have split : gs = pre ++ g :: post := by
    dsimp [pre, g, post]
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have slen : s.1.length = n + j := by
    obtain ⟨t, ht, hlen⟩ := elim_extends n pre (initial p false)
    change (elim n pre (initial p false)).1.length = _
    rw [ht, List.length_append, initial_length, hlen]
    dsimp [pre]
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have constant : (plan n s g).2 = Sum.inl false := by
    have input : stat s p.val = Sum.inl (absorb g.op) := by
      simpa [s, op, g, absorb] using before_input p false pre
    have h := absorb_at_reader n s g good reads input
    simpa [g, op, absorb] using h
  have nextStat : stat (elimStep n s g) (n + j) = Sum.inl false := by
    change (s.1 ++ [(plan n s g).2]).getD (n + j) _ = _
    rw [getD_snoc_len _ _ _ _ slen, constant]
  have inside : n + j < (elimStep n s g).1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [slen]
  rw [split, elim_append]
  change stat (elim n post (elimStep n s g)) (n + j) = _
  exact (elim_stat n post (elimStep n s g) (n + j) inside).trans nextStat

lemma and_consumer_charge {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (p : Fin n) (j k : Nat) (hj : j < C.gates.length) (hk : k < C.gates.length)
    (before : j < k) (op : C.gates[j].op = GateOp.and)
    (reads : p.val ∈ C.gates[j].inputs) (consumer : n + j ∈ C.gates[k].inputs) :
    (plan n (elim n (C.gates.take k) (initial p false)) C.gates[k]).1 = none := by
  have small : j < (C.gates.take k).length := by simp; omega
  have gateEq : (C.gates.take k)[j] = C.gates[j] := by simp
  have constant : stat (elim n (C.gates.take k) (initial p false)) (n + j) = Sum.inl false :=
    and_wire_false (C.gates.take k) p j small
      (by rw [gateEq]; exact mono _ (List.getElem_mem hj))
      (by rw [gateEq]; exact op) (by rw [gateEq]; exact reads)
  exact drop_at_reader n _ _ (mono _ (List.getElem_mem hk)) consumer constant

end PEqualNP.Outside.L_meta_2590.Semantic


namespace PEqualNP.Outside.L_meta_2590.Semantic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def inputMap {m n : Nat} (f : Fin m → Option (Fin n)) (x : Fin n → Bool) : Fin m → Bool :=
  fun i => (f i).elim false x

def mapInitial {m n : Nat} (f : Fin m → Option (Fin n)) : State :=
  (List.ofFn fun i => (f i).elim (Sum.inl false) (fun j => Sum.inr j.val), [])

lemma mapInitial_inv {m n : Nat} (f : Fin m → Option (Fin n)) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (inputMap f x)) (mapInitial f) := by
  refine ⟨by simp [mapInitial], ?_⟩
  intro i
  by_cases hi : i < m
  · let j : Fin m := ⟨i, hi⟩
    change ((mapInitial f).1.getD j.val (Sum.inl false)).Valid _ ∧
      ((mapInitial f).1.getD j.val (Sum.inl false)).val _ = _
    cases hj : f j with
    | none => simp [mapInitial, inputMap, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at *
    | some k => simp [mapInitial, inputMap, hj, Stat.Valid, Stat.val, wiresFrom, j, hi, k.isLt] at *
  · rw [List.getD_eq_default _ _ (by simpa [mapInitial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma inputMap_restriction {m n : Nat} (C : Circuit) (mono : Monotone2 C)
    (f : Fin m → Option (Fin n))
    (nonconstant : ∃ x y, circuitFun m C (inputMap f x) ≠ circuitFun m C (inputMap f y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun m C (inputMap f x)) ∧ D.size ≤ C.size := by
  let s := elim n C.gates (mapInitial f)
  have value (x : Fin n → Bool) :
      (stat s C.output).val (wiresFrom s.2 (List.ofFn x)) = circuitFun m C (inputMap f x) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ mono (mapInitial_inv f x)).2 C.output).2
  cases hs : stat s C.output with
  | inl b =>
    obtain ⟨x, y, different⟩ := nonconstant
    have hx := value x
    have hy := value y
    rw [hs] at hx hy
    exact (different (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨s.2, j⟩, elim_good n _ _ mono (by simp [mapInitial]), ?_, ?_⟩
    · intro x
      change (wiresFrom s.2 (List.ofFn x)).getD j false = _
      simpa only [hs, Stat.val] using value x
    · have size := elim_len n C.gates (mapInitial f)
      simpa only [s, mapInitial, List.length_nil, Nat.zero_add, Circuit.size] using size

end PEqualNP.Outside.L_meta_2590.Semantic
