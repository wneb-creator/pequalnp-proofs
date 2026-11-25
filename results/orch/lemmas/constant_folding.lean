import Mathlib
import PEqualNP.Defs

-- Adapted from the project constant-folding pass in Helpers/Elim.lean.
-- The wire status uses the existing sum type.

namespace PEqualNP.Outside.L_meta_2583_aux.ConstantFolding

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
  next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

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
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

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

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
  and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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

def GateAO (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
    ∀ i ∈ g.inputs, i < m

theorem simplify_AO (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, GateAO m g := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd, Stat.Valid, GateAO] <;> subst g <;> simp_all [GateAO]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr, Stat.Valid, GateAO] <;> subst g <;> simp_all [GateAO]

theorem AO_append_gate (n : ℕ) (gs : List Gate) (g : Gate)
    (h : PEqualNP.TopForm.IsAO2 n ⟨gs, 0⟩)
    (hg : GateAO (n + gs.length) g) :
    PEqualNP.TopForm.IsAO2 n ⟨gs ++ [g], 0⟩ := by
  obtain ⟨hops, hback, hlen⟩ := h
  obtain ⟨gop, glen, gback⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hops a ha
    · simpa only [List.mem_singleton.mp ha] using gop
  · intro j hj i hi
    by_cases hjs : j < gs.length
    · have he : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ j =
          PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j :=
        List.getD_append _ _ _ _ hjs
      rw [he] at hi
      exact hback j hjs i hi
    · have hje : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      have hi' : i ∈ g.inputs := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi
      exact gback i hi'
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hlen a ha
    · simpa only [List.mem_singleton.mp ha] using glen

theorem AO_append_option (n : ℕ) (gs : List Gate) (g : Option Gate)
    (h : PEqualNP.TopForm.IsAO2 n ⟨gs, 0⟩)
    (hg : ∀ a ∈ g, GateAO (n + gs.length) a) :
    PEqualNP.TopForm.IsAO2 n ⟨gs ++ g.toList, 0⟩ := by
  cases g with
  | none => simpa using h
  | some g => exact AO_append_gate n gs g h (hg g rfl)

theorem elim_AO (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      Inv n y w acc → PEqualNP.TopForm.IsAO2 n ⟨acc.2, 0⟩ →
      PEqualNP.TopForm.IsAO2 n ⟨(elim n gs acc).2, 0⟩ := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hao
    have hg := hok g List.mem_cons_self
    have hgos : ∀ g' ∈ [g], Ok g' := by
      intro g' hg'
      have he : g' = g := List.mem_singleton.mp hg'
      subst g'
      exact ⟨hg.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hg.2⟩
    have hi := inv_elim n y hy [g] w acc hgos hinv
    have hi' : Inv n y
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g) := hi
    have ha : PEqualNP.TopForm.IsAO2 n ⟨(elimStep n acc g).2, 0⟩ := by
      apply AO_append_option n acc.2 _ hao
      apply simplify_AO g.op (n + acc.2.length) _ hg.1
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
      exact (hinv.2 a).1
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hi' ha

def initForced (n : ℕ) (pre : List Gate) (b : Bool) : List Stat × List Gate :=
  ((List.range (n + pre.length)).map Sum.inr ++ [Sum.inl b], pre)

theorem inv_initForced (n : ℕ) (y : List Bool) (hy : y.length = n)
    (pre : List Gate) (b : Bool) :
    Inv n y (wiresFrom pre y ++ [b]) (initForced n pre b) := by
  have hl : (wiresFrom pre y).length = n + pre.length := by
    rw [length_wiresFrom, hy]
  refine ⟨by simp [initForced, hl], ?_⟩
  intro i
  by_cases hi : i < n + pre.length
  · have hs : (initForced n pre b).1.getD i (Sum.inl false) = Sum.inr i := by
      change ((List.range (n + pre.length)).map Sum.inr ++ [Sum.inl b]).getD i
        (Sum.inl false) = Sum.inr i
      rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
    rw [hs]
    refine ⟨hi, ?_⟩
    change (wiresFrom pre y).getD i false = (wiresFrom pre y ++ [b]).getD i false
    exact (List.getD_append _ _ _ _ (by omega)).symm
  · by_cases he : i = n + pre.length
    · subst i
      simp [initForced, Stat.Valid, Stat.val, ← hl]
    · have hs : (initForced n pre b).1.length ≤ i := by
        simp [initForced]
        omega
      have hw : (wiresFrom pre y ++ [b]).length ≤ i := by
        simp [hl]
        omega
      rw [List.getD_eq_default _ _ hs, List.getD_eq_default _ _ hw]
      simp [Stat.Valid, Stat.val]

def forcedEval (n : ℕ) (pre post : List Gate) (b : Bool) (out : ℕ)
    (x : Fin n → Bool) : Bool :=
  (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [b])).getD out false

theorem forced_replacement (n : ℕ) (pre post : List Gate) (b : Bool) (out : ℕ)
    (hpre : PEqualNP.TopForm.IsAO2 n ⟨pre, 0⟩)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hnonconstant : ∃ x y : Fin n → Bool,
      forcedEval n pre post b out x ≠ forcedEval n pre post b out y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ pre.length + post.length ∧
      ∀ x : Fin n → Bool,
        PEqualNP.MetaComplexity.circuitFun n D x = forcedEval n pre post b out x := by
  let acc := elim n post (initForced n pre b)
  have hok : ∀ g ∈ post, Ok g := by
    intro g hg
    have h := hpost g hg
    exact ⟨h.1.elim Or.inl (fun e => Or.inr (Or.inl e)), h.2⟩
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [b])) acc := by
    intro x
    exact inv_elim n (List.ofFn x) (by simp) post _ _ hok
      (inv_initForced n (List.ofFn x) (by simp) pre b)
  have hao : PEqualNP.TopForm.IsAO2 n ⟨acc.2, 0⟩ :=
    elim_AO n (List.ofFn (fun _ : Fin n => false)) (by simp) post _ _ hpost
      (inv_initForced n (List.ofFn (fun _ : Fin n => false)) (by simp) pre b) hpre
  have hsize : acc.2.length ≤ pre.length + post.length :=
    elim_len n post (initForced n pre b)
  cases hs : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnonconstant
    have hx := (hinv x).2 out |>.2
    have hy := (hinv y).2 out |>.2
    rw [hs] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨acc.2, j⟩, hao, hsize, ?_⟩
    intro x
    have hx := (hinv x).2 out |>.2
    rw [hs] at hx
    exact hx

theorem AO_prefix (n : ℕ) (pre tail : List Gate) (out : ℕ)
    (h : PEqualNP.TopForm.IsAO2 n ⟨pre ++ tail, out⟩) :
    PEqualNP.TopForm.IsAO2 n ⟨pre, 0⟩ := by
  obtain ⟨hops, hback, hlen⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hops g (List.mem_append_left _ hg)
  · intro j hj i hi
    change j < pre.length at hj
    have he : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨pre ++ tail, out⟩ j =
        PEqualNP.MetaComplexity.NestedCover.gateAt ⟨pre, 0⟩ j :=
      List.getD_append _ _ _ _ hj
    apply hback j (by simp; omega) i
    rwa [he]
  · intro g hg
    exact hlen g (List.mem_append_left _ hg)

theorem delete_forced_gate (n : ℕ) (C : Circuit) (pre : List Gate) (g : Gate)
    (post : List Gate) (b : Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hgs : C.gates = pre ++ g :: post)
    (hnonconstant : ∃ x y : Fin n → Bool,
      forcedEval n pre post b C.output x ≠ forcedEval n pre post b C.output y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool,
        PEqualNP.MetaComplexity.circuitFun n D x = forcedEval n pre post b C.output x := by
  rcases C with ⟨gs, out⟩
  dsimp at hgs
  subst gs
  have hp : PEqualNP.TopForm.IsAO2 n ⟨pre, 0⟩ := AO_prefix n pre (g :: post) out hC
  have ht : ∀ g' ∈ post, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧
      g'.inputs.length ≤ 2 := by
    intro g' hg'
    have hm : g' ∈ pre ++ g :: post := List.mem_append_right _ (List.mem_cons_of_mem _ hg')
    exact ⟨hC.1 g' hm, (hC.2.2 g' hm).le⟩
  obtain ⟨D, hD, hs, he⟩ := forced_replacement n pre post b out hp ht hnonconstant
  refine ⟨D, hD, ?_, he⟩
  change D.gates.length ≤ pre.length + post.length at hs
  change D.gates.length < (pre ++ g :: post).length
  simp only [List.length_append, List.length_cons]
  omega

theorem minimal_forced_ne (n : ℕ) (C : Circuit) (pre : List Gate) (g : Gate)
    (post : List Gate) (b : Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hgs : C.gates = pre ++ g :: post)
    (hnonconstant : ∃ x y : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y)
    (hminimal : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D →
      (∀ x : Fin n → Bool,
        PEqualNP.MetaComplexity.circuitFun n D x = PEqualNP.MetaComplexity.circuitFun n C x) →
      C.size ≤ D.size) :
    forcedEval n pre post b C.output ≠ PEqualNP.MetaComplexity.circuitFun n C := by
  intro heq
  have hnc : ∃ x y : Fin n → Bool,
      forcedEval n pre post b C.output x ≠ forcedEval n pre post b C.output y := by
    simpa only [heq] using hnonconstant
  obtain ⟨D, hD, hsize, hfun⟩ := delete_forced_gate n C pre g post b hC hgs hnc
  have hm := hminimal D hD (fun x => (hfun x).trans (congrFun heq x))
  exact (not_lt_of_ge hm) hsize

end PEqualNP.Outside.L_meta_2583_aux.ConstantFolding
