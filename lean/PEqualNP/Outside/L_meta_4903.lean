import Mathlib
import PEqualNP.Defs

-- The symbolic wire compiler below is adapted from visez's L-meta-2110 proof
-- (open-goat/pequalnp-proofs PR #4456), under the repository's Apache-2.0 license.
-- The helper declarations are included here to keep the proof self-contained.

namespace PEqualNP.Outside.L_meta_4903.Compiler

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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

end PEqualNP.Outside.L_meta_4903.Compiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4903.Compiler

namespace PEqualNP.Outside.L_meta_4903.Restrict

def initMap {n : ℕ} (a : Fin n) : List Stat :=
  List.ofFn fun i : Fin n => if i = a then Sum.inl false else Sum.inr i.val

theorem inv_initMap {n : ℕ} (a : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn fun i => if i = a then false else x i) (initMap a, []) := by
  refine ⟨by simp [initMap], ?_⟩
  intro j
  by_cases hj : j < n
  · let i : Fin n := ⟨j, hj⟩
    change ((initMap a).getD i.val (Sum.inl false)).Valid (n + 0) ∧
      ((initMap a).getD i.val (Sum.inl false)).val (List.ofFn x) =
        (List.ofFn fun v => if v = a then false else x v).getD i.val false
    simp only [initMap, getD_ofFn, Nat.add_zero]
    by_cases h : i = a
    · simp [h, Stat.Valid, Stat.val]
    · simp only [ite_eq_right h, Stat.Valid, Stat.val, getD_ofFn]
      exact ⟨hj, trivial⟩
  · change ((initMap a).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((initMap a).getD j (Sum.inl false)).val (List.ofFn x) =
        (List.ofFn fun v => if v = a then false else x v).getD j false
    rw [List.getD_eq_default _ _ (by simpa [initMap] using Nat.le_of_not_lt hj),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hj)]
    exact ⟨trivial, rfl⟩

def reads (a : ℕ) (g : Gate) : Bool := g.inputs.contains a

theorem count_elim (n a : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, NOk g) (ha : a < acc.1.length)
    (pinned : acc.1.getD a (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).2.length + (gs.filter (reads a)).length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    have hok := ok g List.mem_cons_self
    let next := elimStep n acc g
    have nextLen : a < next.1.length := by simp [next, elimStep]; omega
    have nextPinned : next.1.getD a (Sum.inl false) = Sum.inl false := by
      dsimp [next, elimStep]
      rw [List.getD_append _ _ _ _ ha, pinned]
    have rest := ih next (fun h hh => ok h (List.mem_cons_of_mem _ hh)) nextLen nextPinned
    have step : elim n (g::gs) acc = elim n gs next := rfl
    rw [step, List.length_cons, List.filter_cons]
    by_cases read : reads a g = true
    · have hm : a ∈ g.inputs := List.contains_iff_mem.mp read
      have same : next.2.length = acc.2.length := elimStep_none n acc g hok a hm false pinned
      simp only [ite_eq_left read, List.length_cons]
      omega
    · have no : reads a g = false := Bool.eq_false_of_not_eq_true read
      have one : next.2.length ≤ acc.2.length + 1 := elim_len n [g] acc
      simp only [ite_eq_right read]
      omega

theorem norm_inputs (g : Gate) (ok : Ok g) :
    (normGate g).inputs = g.inputs.take (cond (g.op.eval [false]) 1 2) := by
  obtain ⟨op, ins⟩ := g
  have len : ins.length ≤ 2 := ok.2
  rcases ok.1 with rfl | rfl | rfl <;> simp [normGate, GateOp.eval, List.take_of_length_le len]

theorem restrict (n : ℕ) (C : Circuit) (a : Fin n) :
    let pinned := fun (x : Fin n → Bool) (i : Fin n) => ite (i = a) false (x i)
    let readers := C.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains a.val)
    FanInTwo C → (∃ x, circuitFun n C (pinned x) = true) →
      (∃ x, circuitFun n C (pinned x) = false) →
      ∃ E : Circuit, FanInTwo E ∧ E.output < n + E.size ∧ E.size + readers.length ≤ C.size ∧
        ∀ x, circuitFun n E x = circuitFun n C (pinned x) := by
  intro pin readers fan htrue hfalse
  let gs := C.gates.map normGate
  let acc := elim n gs (initMap a, [])
  have nok (g : Gate) (hg : g ∈ gs) : NOk g := by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok h (fan h hh)
  have inv (x : Fin n → Bool) : Inv n (List.ofFn x) (wiresFrom gs (List.ofFn (pin x))) acc :=
    inv_elim n _ (by simp) gs _ _ (fun g hg => (nok g hg).1) (inv_initMap a x)
  have values (x : Fin n → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = circuitFun n C (pin x) := by
    rw [((inv x).2 C.output).2]
    change (wiresFrom (C.gates.map normGate) (List.ofFn (pin x))).getD C.output false = _
    rw [wiresFrom_norm]
    rfl
  have count : (gs.filter (reads a.val)).length = readers.length := by
    change ((C.gates.map normGate).filter (reads a.val)).length = readers.length
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro g hg
    change (normGate g).inputs.contains a.val = (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains a.val
    rw [norm_inputs g (fan g hg)]
  have save := count_elim n a.val gs (initMap a, []) nok (by simp [initMap])
    (by change (initMap a).getD a.val (.inl false) = _; simp [initMap])
  rw [count, show gs.length = C.size from by change (C.gates.map normGate).length = C.gates.length; simp] at save
  simp only [List.length_nil, zero_add] at save
  cases hout : acc.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨x, hx⟩ := htrue
    obtain ⟨y, hy⟩ := hfalse
    have ht := values x
    have hf := values y
    rw [hout, hx] at ht
    rw [hout, hy] at hf
    change b = true at ht
    change b = false at hf
    cases b <;> contradiction
  | inr j =>
    have valid := ((inv (fun _ => false)).2 C.output).1
    rw [hout] at valid
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),valid,save,?_⟩
    intro x
    have value := values x
    rw [hout] at value
    exact value

end PEqualNP.Outside.L_meta_4903.Restrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4903.Compiler

namespace PEqualNP.Outside.L_meta_4903.Preservation

def synth (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (.inl false))

theorem step_eq (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    elimStep n acc g = (acc.1 ++ [(synth n acc g).2], acc.2 ++ (synth n acc g).1.toList) := rfl

def wire (acc : List Stat × List Gate) (i : ℕ) : Stat := acc.1.getD i (.inl false)

theorem step_wire (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (i : ℕ) (hi : i < acc.1.length) :
    wire (elimStep n acc g) i = wire acc i := by
  rw [wire,step_eq]
  exact List.getD_append _ _ _ _ hi

theorem step_new (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    wire (elimStep n acc g) acc.1.length = (synth n acc g).2 := by
  rw [wire,step_eq]
  exact getD_snoc_eq _ _ _

theorem step_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (a : ℕ)
    (ha : a ∈ g.inputs) (hb : wire acc a = .inl false) : (synth n acc g).1 = none := by
  apply simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2) (by intro h; simpa using hg.2 h)
  exact ⟨false,List.mem_map.mpr ⟨a,ha,hb⟩⟩

theorem surviving (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (h : (simplify op m ins).1 = some g) :
    (simplify op m ins).2 = .inr m ∧ g.op = op ∧
      ins.take (cond (op.eval [false]) 1 2) = g.inputs.map Sum.inr := by
  cases op <;> simp only [simplify] at h ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at h
    subst g
    exact ⟨rfl,rfl,rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at h
    subst g
    exact ⟨rfl,rfl,rfl⟩
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [simpNot] at h
    subst g
    exact ⟨rfl,rfl,rfl⟩
  · contradiction
  · contradiction

def emits (n : ℕ) (acc : List Stat × List Gate) (gs : List Gate) : List (Gate × Option Gate × Stat) :=
  match gs with
  | [] => []
  | g :: rest => (g, synth n acc g) :: emits n (elimStep n acc g) rest

theorem emits_split (n : ℕ) (acc : List Stat × List Gate) (pre post : List Gate) :
    emits n acc (pre ++ post) = emits n acc pre ++ emits n (elim n pre acc) post := by
  induction pre generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.cons_append, emits, elim_cons]
    rw [ih]

def inactive (e : Gate × Option Gate × Stat) : Bool := e.2.1.isNone

theorem counts (n : ℕ) (acc : List Stat × List Gate) (gs : List Gate) :
    ((emits n acc gs).filter inactive).length + (elim n gs acc).2.length = acc.2.length+gs.length := by
  induction gs generalizing acc with
  | nil => simp [emits,elim]
  | cons g gs ih =>
    have rest := ih (elimStep n acc g)
    simp only [elim_cons,emits,List.filter_cons,List.length_cons]
    have collected : (elimStep n acc g).2 = acc.2 ++ (synth n acc g).1.toList := rfl
    rw [collected] at rest
    cases h : (synth n acc g).1 <;> simp [inactive,h] at * <;> omega

theorem kept_read (n v : ℕ) (acc : List Stat × List Gate) (g h : Gate)
    (loc : ∀ i, wire acc i = .inr v ↔ i = v) (normal : NOk g)
    (out : (synth n acc g).1 = some h) : h.op = g.op ∧ (h.inputs.contains v) = (g.inputs.contains v) := by
  have sem := surviving g.op (n+acc.2.length) _ h out
  obtain ⟨_, op, ins⟩ := sem
  have le : g.inputs.length ≤ cond (g.op.eval [false]) 1 2 := by
    rcases normal.1.1 with e | e | e
    · rw [e]; exact normal.1.2
    · rw [e]; exact normal.1.2
    · rw [e]; exact normal.2 e
  rw [List.take_of_length_le (by simpa only [List.length_map] using le)] at ins
  change g.inputs.map (wire acc) = h.inputs.map Sum.inr at ins
  refine ⟨op,Bool.eq_iff_iff.mpr ?_⟩
  simp only [List.contains_iff_mem]
  constructor
  · intro hin
    have hmap : (Sum.inr v : Stat) ∈ h.inputs.map Sum.inr := List.mem_map_of_mem hin
    rw [← ins] at hmap
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp hmap
    simpa only [(loc i).mp eq] using hi
  · intro hin
    have hmap : Sum.inr v ∈ g.inputs.map (wire acc) := by
      exact List.mem_map.mpr ⟨v,hin,(loc v).mpr rfl⟩
    rw [ins] at hmap
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp hmap
    cases eq
    exact hi

theorem location_step (n v : ℕ) (acc : List Stat × List Gate) (g : Gate) (hv : v < acc.1.length)
    (loc : ∀ i, wire acc i = .inr v ↔ i = v) (new : (synth n acc g).2 ≠ .inr v) :
    ∀ i, wire (elimStep n acc g) i = .inr v ↔ i = v := by
  intro i
  by_cases small : i < acc.1.length
  · rw [step_wire _ _ _ _ small, loc]
  by_cases hit : i = acc.1.length
  · subst i
    rw [step_new]
    exact ⟨fun h => (new h).elim, fun h => (Nat.ne_of_gt hv h).elim⟩
  have above : (elimStep n acc g).1.length ≤ i := by rw [step_eq]; simp; omega
  rw [wire,List.getD_eq_default _ _ above]
  constructor
  · intro h
    cases h
  · intro h
    subst i
    exact (small hv).elim

def opReads (v : ℕ) (gs : List Gate) : List GateOp :=
  (gs.filter (fun g => g.inputs.contains v)).map Gate.op

theorem opReads_append (v : ℕ) (gs hs : List Gate) :
    opReads v (gs ++ hs) = opReads v gs ++ opReads v hs := by simp [opReads]

theorem keep_reads (n v : ℕ) (hv : v < n) (acc : List Stat × List Gate) (gs : List Gate)
    (hpos : v < acc.1.length) (ok : ∀ g ∈ gs, NOk g)
    (loc : ∀ i, wire acc i = .inr v ↔ i = v)
    (dead : ∀ e ∈ emits n acc gs, e.2.1 = none → e.2.2 ≠ .inr v ∧ e.1.inputs.contains v = false) :
    opReads v (elim n gs acc).2 = opReads v acc.2 ++ opReads v gs := by
  induction gs generalizing acc with
  | nil => simp [elim,opReads]
  | cons g gs ih =>
    let next := elimStep n acc g
    have good := ok g List.mem_cons_self
    have nextPos : v < next.1.length := by simp [next,elimStep]; omega
    have nextDead (e : Gate × Option Gate × Stat) (he : e ∈ emits n next gs) :
        e.2.1 = none → e.2.2 ≠ .inr v ∧ e.1.inputs.contains v = false :=
      dead e (List.mem_cons_of_mem _ he)
    have nextLoc : (synth n acc g).2 ≠ .inr v := by
      cases form : (synth n acc g).1 with
      | none => exact (dead (g,synth n acc g) List.mem_cons_self form).1
      | some h =>
        have shape := surviving g.op (n+acc.2.length) _ h form
        rw [show (synth n acc g).2 = .inr (n+acc.2.length) from shape.1]
        intro eq
        injection eq
        omega
    have tail := ih next nextPos (fun h hh => ok h (List.mem_cons_of_mem _ hh))
      (location_step n v acc g hpos loc nextLoc) nextDead
    have nextOps : opReads v next.2 = opReads v acc.2 ++ opReads v [g] := by
      change opReads v (elimStep n acc g).2 = _
      rw [step_eq,opReads_append]
      cases form : (synth n acc g).1 with
      | none =>
        have no : g.inputs.contains v = false := (dead (g,synth n acc g) List.mem_cons_self form).2
        simp only [opReads,Option.toList_none,List.filter_nil,List.map_nil,List.filter_cons,no]
        rfl
      | some h =>
        obtain ⟨op, same⟩ := kept_read n v acc g h loc good form
        simp only [opReads,Option.toList_some,List.filter_cons,List.filter_nil,same]
        cases test : g.inputs.contains v <;> simp [op]
    rw [elim_cons, show elimStep n acc g = next from rfl, tail,nextOps,List.append_assoc]
    rw [show g::gs = [g]++gs from rfl,opReads_append]

def AgreeOff (excluded : ℕ → Prop) (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, ¬excluded i → w.getD i false = z.getD i false

theorem agree_extend (excluded : ℕ → Prop) (w z : List Bool) (b c : Bool)
    (same : AgreeOff excluded w z) (here : ¬excluded w.length → b = c) :
    AgreeOff excluded (w ++ [b]) (z ++ [c]) := by
  refine ⟨by simp [same.1], ?_⟩
  intro i included
  by_cases atEnd : i = w.length
  · subst i
    rw [getD_snoc_eq,getD_snoc_len _ _ _ _ same.1.symm,here included]
  · rw [getD_snoc_ne _ _ _ _ atEnd,getD_snoc_ne _ _ _ _ (by rw [← same.1]; exact atEnd)]
    exact same.2 i included

theorem agreement (excluded : ℕ → Prop) (m : ℕ) (gs : List Gate) (w z : List Bool)
    (len : w.length = m) (initial : AgreeOff excluded w z)
    (no : ∀ p g, gs[p]? = some g → ¬excluded (m+p) → ∀ i ∈ g.inputs, i < m+p → ¬excluded i) :
    AgreeOff excluded (wiresFrom gs w) (wiresFrom gs z) := by
  induction gs generalizing m w z with
  | nil => exact initial
  | cons g gs ih =>
    let value (y : List Bool) := g.op.eval (g.inputs.map fun i => y.getD i false)
    apply ih (m+1) (w ++ [value w]) (z ++ [value z]) (by simp [len])
    · apply agree_extend _ _ _ _ _ initial
      intro included
      apply congrArg (GateOp.eval g.op)
      apply List.map_congr_left
      intro i hi
      by_cases valid : i < m
      · apply initial.2 i
        exact no 0 g rfl (by simpa [← len] using included) i hi (by simpa using valid)
      · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by have := initial.1; omega)]
    · intro p h hh there i hi small
      have index : m + (p+1) = m+1+p := by omega
      exact no (p+1) h hh (index.symm ▸ there) i hi (index.symm ▸ small)

theorem trace_at (n : ℕ) (acc : List Stat × List Gate) (pre post : List Gate) (g : Gate) :
    (g,synth n (elim n pre acc) g) ∈ emits n acc (pre ++ g::post) := by
  rw [emits_split]
  exact List.mem_append_right _ List.mem_cons_self

theorem anchor (n i : ℕ) (acc : List Stat × List Gate) (gs : List Gate) (hi : i < acc.1.length) :
    wire (elim n gs acc) i = wire acc i := elim_getD _ _ _ _ _ hi

theorem absent_after_const (n : ℕ) (acc : List Stat × List Gate) (pre post : List Gate) (g : Gate)
    (gone : (synth n (elim n pre acc) g).1 = none)
    (total : ((emits n acc (pre ++ g::post)).filter inactive).length = 1) :
    ((emits n acc pre).filter inactive).length = 0 ∧
    ((emits n (elimStep n (elim n pre acc) g) post).filter inactive).length = 0 := by
  rw [emits_split] at total
  simp only [emits,List.filter_append,List.length_append,List.filter_cons] at total
  have h : inactive (g,synth n (elim n pre acc) g) = true := by simp [inactive,gone]
  rw [ite_eq_left h,List.length_cons] at total
  constructor <;> omega

theorem pinned_or (g : Gate) (normal : NOk g) (m : ℕ) (ins : List Stat)
    (len : ins.length = g.inputs.length) (constant : Sum.inl false ∈ ins) (j : ℕ)
    (out : (simplify g.op m ins).2 = .inr j) :
    g.op = .or ∧ ∀ i, Sum.inr i ∈ ins → i = j := by
  rcases normal.1.1 with op | op | op
  · rw [op] at out
    have bound : ins.length ≤ 2 := len.symm ▸ normal.1.2
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify,simpAnd,Sum.inl.injEq]
  · refine ⟨op,?_⟩
    rw [op] at out
    have bound : ins.length ≤ 2 := len.symm ▸ normal.1.2
    intro i hi
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify,simpOr,Sum.inl.injEq]
  · rw [op] at out
    have bound : ins.length ≤ 1 := len.symm ▸ normal.2 op
    rcases ins with _ | ⟨a, _ | ⟨b,l⟩⟩ <;> (try cases a) <;>
      simp_all [simplify,simpNot,Sum.inl.injEq] <;> omega

theorem no_later_reader (n : ℕ) (acc : List Stat × List Gate) (pre post : List Gate) (g : Gate)
    (ok : ∀ h ∈ post, NOk h)
    (lost : (synth n (elim n pre acc) g).1 = none)
    (lostCount : ((emits n acc (pre ++ g::post)).filter inactive).length = 1)
    (c : Bool) (constant : (synth n (elim n pre acc) g).2 = .inl c) :
    ∀ h ∈ post, (elim n pre acc).1.length ∉ h.inputs := by
  intro h hh member
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hh
  obtain ⟨early,late,rfl,_⟩ := split_at post p h hp
  let before := elim n pre acc
  let after := elimStep n before g
  have pos : before.1.length < after.1.length := by simp [after,step_eq]
  have read : wire (elim n early after) before.1.length = .inl c := by
    rw [anchor _ _ _ _ pos, show wire after before.1.length = _ from step_new n before g,constant]
  have stops : (synth n (elim n early after) h).1 = none := by
    apply simplify_count _ _ _ (ok h hh).1.1 (by simpa using (ok h hh).1.2)
      (by intro e; simpa using (ok h hh).2 e)
    exact ⟨c,List.mem_map.mpr ⟨_,member,read⟩⟩
  have occurs := trace_at n after early late h
  have counted : (h,synth n (elim n early after) h) ∈ (emits n after (early ++ h::late)).filter inactive :=
    List.mem_filter.mpr ⟨occurs,by simp [inactive,stops]⟩
  have empty := (absent_after_const n acc pre (early ++ h::late) g lost lostCount).2
  have positive := List.length_pos_of_mem counted
  exact (Nat.ne_of_gt positive) empty

end PEqualNP.Outside.L_meta_4903.Preservation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4903.Compiler

namespace PEqualNP.Outside.L_meta_4903.Graph

def setOnly {n : ℕ} (a : Fin n) (b : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = a then b else x i

def evaluate {n : ℕ} (gs : List Gate) (j : ℕ) (x : Fin n → Bool) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD j false

theorem eval_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (a : Fin n) :
    evaluate gs a.val x = x a := by
  rw [evaluate,getD_wiresFrom _ _ _ (by simp),getD_ofFn]

theorem set_agrees {n : ℕ} (a : Fin n) (x : Fin n → Bool) (b c : Bool)
    (excluded : ℕ → Prop) (ha : excluded a.val) :
    PEqualNP.Outside.L_meta_4903.Preservation.AgreeOff excluded (List.ofFn (setOnly a b x)) (List.ofFn (setOnly a c x)) := by
  refine ⟨by simp,?_⟩
  intro i inScope
  by_cases hi : i < n
  · let j : Fin n := ⟨i,hi⟩
    have ne : j ≠ a := by
      intro e
      have eq : i = a.val := congrArg Fin.val e
      exact inScope (eq.symm ▸ ha)
    change (List.ofFn (setOnly a b x)).getD j.val false = (List.ofFn (setOnly a c x)).getD j.val false
    rw [getD_ofFn,getD_ofFn]
    simp [setOnly,ne]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]

theorem one_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) (x : Fin n → Bool) :
    graphFun G A (setOnly a true x) = true := by
  change (decide (∃ i ∈ A, setOnly a true x i = true) || decide _) = true
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inl ⟨a,ha,by simp [setOnly]⟩

theorem no_edge_on_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A) : graphFun G A (setOnly v true (fun _ => false)) = false := by
  let x := setOnly v true (fun _ => false)
  have pick (i : Fin n) (on : x i = true) : i = v := by simpa [x,setOnly] using on
  change (decide (∃ i ∈ A, x i = true) || decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true)) = false
  rw [Bool.or_eq_false_iff]
  constructor
  · exact decide_eq_false (fun ⟨i,h,on⟩ => hv (pick i on ▸ h))
  · exact decide_eq_false (fun ⟨p,q,adj,pOn,qOn⟩ => adj.ne ((pick p pOn).trans (pick q qOn).symm))

theorem or_true (ins : List Bool) (h : true ∈ ins) : GateOp.or.eval ins = true := by
  induction ins with
  | nil => cases h
  | cons b rest ih =>
    change (b || GateOp.or.eval rest) = true
    rcases List.mem_cons.mp h with e | e
    · rw [← e]; rfl
    · rw [ih e,Bool.or_true]

end PEqualNP.Outside.L_meta_4903.Graph

namespace PEqualNP.Outside.L_meta_4903.Graph

theorem add {n : ℕ} (D : Circuit) (a : Fin n) (ok : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = D.size+1 ∧
        ∀ x, circuitFun n E x = (x a || circuitFun n D x) := by
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wireLength (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_nil, List.length_cons]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  let last : Gate := ⟨.or,[a.val,D.output]⟩
  let E : Circuit := ⟨D.gates ++ [last],n+D.size⟩
  refine ⟨E, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ D.gates ++ [last] at hg
    rcases List.mem_append.mp hg with h | h
    · exact ok g h
    · have same := List.mem_singleton.mp h
      subst g
      simp [last]
  · change (D.gates ++ [last]).length = D.gates.length + 1
    simp
  · intro x
    let w := D.gates.foldl step (List.ofFn x)
    have len : w.length = n+D.size := by
      change (D.gates.foldl step (List.ofFn x)).length = n+D.gates.length
      rw [wireLength,List.length_ofFn]
    have primary : w.getD a.val false = x a := by
      change (D.gates.foldl step (List.ofFn x)).getD a.val false = _
      rw [keep _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    change ((D.gates ++ [last]).foldl step (List.ofFn x)).getD (n+D.size) false = _
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (w ++ [w.getD a.val false || (w.getD D.output false || false)]).getD (n+D.size) false = _
    rw [← len,List.getD_append_right _ _ _ _ (by omega),Nat.sub_self]
    change (w.getD a.val false || (w.getD D.output false || false)) = (x a || w.getD D.output false)
    simp only [primary,Bool.or_false]

theorem insertFun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n)) (a : Fin n) (x : Fin n → Bool) :
      graphFun G (insert a B) x = (x a || graphFun G B x) := by
  apply Bool.eq_iff_iff.mpr
  change (decide (∃ v ∈ insert a B, x v = true) ||
    decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true)) = true ↔
    (x a || (decide (∃ v ∈ B, x v = true) ||
      decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true))) = true
  simp only [Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert]
  constructor
  · rintro (⟨v, hv, on⟩ | h)
    · rcases hv with rfl | hv
      · exact Or.inl on
      · exact Or.inr (Or.inl ⟨v,hv,on⟩)
    · exact Or.inr (Or.inr h)
  · rintro (on | ⟨v,hv,on⟩ | h)
    · exact Or.inl ⟨a,Or.inl rfl,on⟩
    · exact Or.inl ⟨v,Or.inr hv,on⟩
    · exact Or.inr h

theorem independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n)) (a : Fin n) (absent : a ∉ B) (apart : ∀ v, ¬G.Adj a v)
      (x : Fin n → Bool) : graphFun G B (fun i => ite (i = a) false (x i)) = graphFun G B x := by
  let y (i : Fin n) := ite (i = a) false (x i)
  apply Bool.eq_iff_iff.mpr
  change (decide (∃ v ∈ B, y v = true) ||
    decide (∃ p q, G.Adj p q ∧ y p = true ∧ y q = true)) = true ↔
    (decide (∃ v ∈ B, x v = true) ||
      decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true)) = true
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  have mark (v : Fin n) (hv : v ∈ B) : y v = x v := by
    have ne : v ≠ a := fun h => absent (h ▸ hv)
    simp only [y,ite_eq_right ne]
  have endpoints (p q : Fin n) (h : G.Adj p q) : y p = x p ∧ y q = x q := by
    have hp : p ≠ a := fun e => apart q (e ▸ h)
    have hq : q ≠ a := fun e => apart p (e ▸ h.symm)
    simp only [y,ite_eq_right hp,ite_eq_right hq,and_self]
  constructor
  · rintro (⟨v,hv,on⟩ | ⟨p,q,e,onP,onQ⟩)
    · exact Or.inl ⟨v,hv,(mark v hv).symm.trans on⟩
    · exact Or.inr ⟨p,q,e,(endpoints p q e).1.symm.trans onP,(endpoints p q e).2.symm.trans onQ⟩
  · rintro (⟨v,hv,on⟩ | ⟨p,q,e,onP,onQ⟩)
    · exact Or.inl ⟨v,hv,(mark v hv).trans on⟩
    · exact Or.inr ⟨p,q,e,(endpoints p q e).1.trans onP,(endpoints p q e).2.trans onQ⟩

theorem high {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (edge : ∃ p q, G.Adj p q) (B : Finset (Fin n)) : graphFun G B (fun _ => true) = true := by
  change (decide (∃ a ∈ B, (true : Bool) = true) ||
    decide (∃ p q, G.Adj p q ∧ (true : Bool) = true ∧ (true : Bool) = true)) = true
  simp only [Bool.or_eq_true,decide_eq_true_eq,and_true]
  exact Or.inr edge

theorem low {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Finset (Fin n)) : graphFun G B (fun _ => false) = false := by
  change (decide (∃ a ∈ B, (false : Bool) = true) ||
    decide (∃ p q, G.Adj p q ∧ (false : Bool) = true ∧ (false : Bool) = true)) = false
  simp

end PEqualNP.Outside.L_meta_4903.Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4903.Compiler
open PEqualNP.Outside.L_meta_4903.Restrict PEqualNP.Outside.L_meta_4903.Preservation PEqualNP.Outside.L_meta_4903.Graph

namespace PEqualNP.Outside.L_meta_4903.Remove

theorem only_other_index (n : ℕ) (pre post : List Gate) (g : Gate) (p : ℕ) (h : Gate)
    (hh : (pre ++ g :: post)[p]? = some h) (different : n + p ≠ n + pre.length) :
    (p < pre.length ∧ h ∈ pre) ∨ (pre.length < p ∧ h ∈ post) := by
  by_cases left : p < pre.length
  · rw [List.getElem?_append_left left] at hh
    exact Or.inl ⟨left,List.mem_iff_getElem?.mpr ⟨p,hh⟩⟩
  · have right : pre.length < p := by omega
    rw [List.getElem?_append_right (by omega)] at hh
    have offset : p-pre.length = p-(pre.length+1)+1 := by omega
    rw [offset,List.getElem?_cons_succ] at hh
    exact Or.inr ⟨right,List.mem_iff_getElem?.mpr ⟨_,hh⟩⟩

theorem no_member {α : Type} (l : List α) (p : α → Bool) (len : (l.filter p).length = 0)
    (x : α) (hx : x ∈ l) : p x = false := by
  cases state : p x with
  | false => rfl
  | true =>
    have present := List.mem_filter.mpr ⟨hx,state⟩
    exact ((Nat.ne_of_gt (List.length_pos_of_mem present)) len).elim

theorem length_pre (n : ℕ) (a : Fin n) (gs : List Gate) :
    (elim n gs (initMap a, [])).1.length = n + gs.length := by
  rw [elim_fst_len]
  simp [initMap]

theorem init_loc {n : ℕ} (a v : Fin n) (different : v ≠ a) :
    ∀ i, wire (initMap a,[]) i = .inr v.val ↔ i = v.val := by
  intro i
  by_cases valid : i < n
  · let j : Fin n := ⟨i,valid⟩
    change (initMap a).getD j.val (.inl false) = .inr v.val ↔ j.val = v.val
    simp only [initMap,getD_ofFn]
    by_cases h : j = a
    · rw [h,ite_eq_left rfl]
      constructor
      · intro e; cases e
      · intro e; exact (different (Fin.ext e.symm)).elim
    · rw [ite_eq_right h,Sum.inr.injEq]
  · change (initMap a).getD i (.inl false) = .inr v.val ↔ i = v.val
    rw [List.getD_eq_default _ _ (by simpa [initMap] using Nat.le_of_not_lt valid)]
    constructor
    · intro h; cases h
    · intro h; exact (valid (h.symm ▸ v.isLt)).elim

theorem retained_ops (v : ℕ) (gs : List Gate) (ok : ∀ g ∈ gs, NOk g) :
    opReads v gs = (gs.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v)).map Gate.op := by
  unfold opReads
  congr 1
  apply List.filter_congr
  intro g hg
  congr 1
  symm
  apply List.take_of_length_le
  have shape := ok g hg
  rcases shape.1.1 with op | op | op
  · rw [op]; exact shape.1.2
  · rw [op]; exact shape.1.2
  · rw [op]; exact shape.2 op

theorem normalized_ops (C : Circuit) (v : ℕ) (fan : FanInTwo C) :
    opReads v (C.gates.map normGate) =
      (C.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v)).map Gate.op := by
  rw [opReads,List.filter_map,List.map_map]
  have predicates : C.gates.filter ((fun g => g.inputs.contains v) ∘ normGate) =
      C.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v) := by
    apply List.filter_congr
    intro g mem
    change (normGate g).inputs.contains v = _
    rw [norm_inputs g (fan g mem)]
  rw [predicates]
  apply List.map_congr_left
  intro g _
  obtain ⟨op,ins⟩ := g
  cases op <;> rfl

set_option maxHeartbeats 5000000 in
theorem remove (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : Finset (Fin n)) (a : Fin n) (C : Circuit) :
    let active := fun (D : Circuit) (v : Fin n) =>
      D.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)
    a ∉ B → (∀ v, ¬G.Adj a v) → (∃ p q, G.Adj p q) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G (insert a B) →
      (active C a).length ≤ 1 →
      ∃ D : Circuit, IsMinimalCircuit n D ∧ circuitFun n D = graphFun G B ∧
        ∀ v ∉ B, v ≠ a → (active D v).map Gate.op = (active C v).map Gate.op := by
  intro active absent apart edge minimum computes one
  let original := C.gates.map normGate
  let initial : List Stat × List Gate := (initMap a,[])
  have shape (g : Gate) (hg : g ∈ original) : NOk g := by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok h (minimum.1 h hh)
  have originalFn (x : Fin n → Bool) : evaluate original C.output x = graphFun G (insert a B) x := by
    change (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false = _
    rw [wiresFrom_norm,← computes]
    rfl
  have pinFn (x : Fin n → Bool) : evaluate original C.output (setOnly a false x) = graphFun G B x := by
    rw [originalFn,insertFun]
    change (setOnly a false x a || graphFun G B (fun i => ite (i=a) false (x i))) = _
    rw [independent G B a absent apart x]
    simp [setOnly]
  have notA : C.output ≠ a.val := by
    intro out
    have hv := pinFn (fun _ => true)
    rw [out,eval_input,high G edge B] at hv
    simp [setOnly] at hv
  have reader : ∃ g ∈ original, a.val ∈ g.inputs := by
    by_contra! no
    let exc (i : ℕ) := i = a.val
    have agree := agreement exc n original (List.ofFn (setOnly a false (fun _ => false)))
      (List.ofFn (setOnly a true (fun _ => false))) (by simp)
      (set_agrees a (fun _ => false) false true exc rfl) (by
        intro p g hg _ i hi _ hit
        exact no g (List.mem_iff_getElem?.mpr ⟨p,hg⟩) (hit ▸ hi))
    have same := agree.2 C.output notA
    change evaluate original C.output (setOnly a false (fun _ => false)) =
        evaluate original C.output (setOnly a true (fun _ => false)) at same
    rw [pinFn,low,originalFn,one_true G _ a (Finset.mem_insert_self _ _) _] at same
    exact Bool.false_ne_true same
  obtain ⟨g, hg, ga⟩ := reader
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hg
  obtain ⟨pre,post,split,_⟩ := split_at original p g hp
  let before := elim n pre initial
  let after := elimStep n before g
  let saved := elim n post after
  let k := n + pre.length
  have kLength : before.1.length = k := length_pre n a pre
  have finish : elim n original initial = saved := by rw [split,elim_append,elim_cons]
  have initLen : initial.1.length = n := by simp [initial,initMap]
  have initA : wire initial a.val = .inl false := by simp [wire,initial,initMap]
  have beforeA := anchor n a.val initial pre (by rw [initLen]; exact a.isLt)
  rw [initA] at beforeA
  have gone : (synth n before g).1 = none := step_const n before g (shape g hg) a.val ga beforeA
  have filtered : (original.filter (reads a.val)).length = (active C a).length := by
    change ((C.gates.map normGate).filter (fun g => g.inputs.contains a.val)).length = _
    have eq := congrArg List.length (normalized_ops C a.val minimum.1)
    simpa only [opReads,List.length_map] using eq
  have notReadPre : (pre.filter (reads a.val)).length = 0 := by
    rw [split] at filtered
    have yes : reads a.val g = true := List.contains_iff_mem.mpr ga
    simp only [List.filter_append,List.length_append,List.filter_cons,ite_eq_left yes,List.length_cons] at filtered
    omega
  have notReadPost : (post.filter (reads a.val)).length = 0 := by
    rw [split] at filtered
    have yes : reads a.val g = true := List.contains_iff_mem.mpr ga
    simp only [List.filter_append,List.length_append,List.filter_cons,ite_eq_left yes,List.length_cons] at filtered
    omega
  have noPre (h : Gate) (hh : h ∈ pre) : a.val ∉ h.inputs :=
    fun member => Bool.false_ne_true ((no_member pre (reads a.val) notReadPre h hh).symm.trans
      (List.contains_iff_mem.mpr member))
  have noPost (h : Gate) (hh : h ∈ post) : a.val ∉ h.inputs :=
    fun member => Bool.false_ne_true ((no_member post (reads a.val) notReadPost h hh).symm.trans
      (List.contains_iff_mem.mpr member))
  have inv (x : Fin n → Bool) : Inv n (List.ofFn x) (wiresFrom original (List.ofFn (setOnly a false x))) saved := by
    rw [← finish]
    exact inv_elim n _ (by simp) original _ _ (fun h hh => (shape h hh).1) (inv_initMap a x)
  have value (x : Fin n → Bool) :
      (wire saved C.output).val (wiresFrom saved.2 (List.ofFn x)) = graphFun G B x :=
    ((inv x).2 C.output).2.trans (pinFn x)
  obtain ⟨out, output⟩ : ∃ j : ℕ, wire saved C.output = .inr j := by
    cases result : wire saved C.output with
    | inr j => exact ⟨j,rfl⟩
    | inl b =>
      have l := value (fun _ => false)
      have h := value (fun _ => true)
      rw [result,low] at l
      rw [result,high G edge] at h
      exact (Bool.false_ne_true (l.symm.trans h)).elim
  let D : Circuit := ⟨saved.2,out⟩
  have dfun : circuitFun n D = graphFun G B := by
    funext x
    have ev := value x
    rw [output] at ev
    exact ev
  have dfan : FanInTwo D := by
    change ∀ h ∈ saved.2, Ok h
    rw [← finish]
    exact elim_ok _ _ _ (by simp [initial])
  have addBound (E : Circuit) (efan : FanInTwo E) (efun : circuitFun n E = graphFun G B) : C.size ≤ E.size+1 := by
    obtain ⟨U,ufan,usize,uval⟩ := add E a efan
    have same : circuitFun n U = circuitFun n C := by
      funext x
      rw [uval,efun,computes,insertFun]
    rw [← usize]
    exact minimum.2 U ufan same
  have trace := counts n initial original
  have traceSize : ((emits n initial original).filter inactive).length + D.size = C.size := by
    rw [finish] at trace
    simpa [D,initial,original,Circuit.size] using trace
  have marked := trace_at n initial pre post g
  rw [← split] at marked
  have marked' : (g,synth n before g) ∈ (emits n initial original).filter inactive :=
    List.mem_filter.mpr ⟨marked,by simp [inactive,gone]⟩
  have lostPos := List.length_pos_of_mem marked'
  have exactlyOne : ((emits n initial original).filter inactive).length = 1 := by
    have bound := addBound D dfan dfun
    omega
  have dmin : IsMinimalCircuit n D := by
    refine ⟨dfan,?_⟩
    intro E efan same
    have bound := addBound E efan (same.trans dfun)
    omega
  have loss_eq : (emits n initial original).filter inactive = [(g,synth n before g)] := by
    cases hh : (emits n initial original).filter inactive with
    | nil => rw [hh] at exactlyOne; contradiction
    | cons e rest =>
      rw [hh,List.length_cons] at exactlyOne
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hh,empty] at marked'
      rw [empty,List.mem_singleton.mp marked']
  have notConst (c : Bool) : (synth n before g).2 ≠ .inl c := by
    intro constant
    have noLater := no_later_reader n initial pre post g
      (fun h hh => shape h (by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
      gone (split ▸ exactlyOne) c constant
    let exc (i : ℕ) := i = a.val ∨ i = k
    have notK : C.output ≠ k := by
      intro atK
      have pos : k < after.1.length := by simp [after,step_eq,kLength]
      rw [atK,show saved = elim n post after from rfl,anchor _ _ _ _ pos,← kLength,step_new,constant] at output
      contradiction
    have same := agreement exc n original (List.ofFn (setOnly a false (fun _ => false)))
      (List.ofFn (setOnly a true (fun _ => false))) (by simp)
      (set_agrees a _ false true exc (Or.inl rfl)) (by
        intro p h hh hv i hi valid hit
        have atOther : n+p ≠ k := fun equal => hv (Or.inr equal)
        rcases only_other_index n pre post g p h (split ▸ hh) atOther with ⟨early,left⟩ | ⟨right,hr⟩
        · rcases hit with eq | eq
          · exact noPre h left (eq ▸ hi)
          · change i = n + pre.length at eq
            omega
        · rcases hit with eq | eq
          · exact noPost h hr (eq ▸ hi)
          · exact noLater h hr (kLength.symm ▸ eq ▸ hi))
    have eq := same.2 C.output (fun h => h.elim notA notK)
    change evaluate original C.output (setOnly a false (fun _ => false)) =
        evaluate original C.output (setOnly a true (fun _ => false)) at eq
    rw [pinFn,low,originalFn,one_true G _ a (Finset.mem_insert_self _ _) _] at eq
    exact Bool.false_ne_true eq
  obtain ⟨target,hAlias⟩ : ∃ j : ℕ, (synth n before g).2 = .inr j := by
    cases atG : (synth n before g).2 with
    | inl c => exact (notConst c atG).elim
    | inr j => exact ⟨j,rfl⟩
  have pinIn : Sum.inl false ∈ g.inputs.map (wire before) := List.mem_map.mpr ⟨a.val,ga,beforeA⟩
  obtain ⟨op,onlyTarget⟩ := pinned_or g (shape g hg) _ (g.inputs.map (wire before)) (by simp) pinIn target hAlias
  refine ⟨D,dmin,dfun,?_⟩
  intro v hv ne
  have initV : wire initial v.val = .inr v.val := (init_loc a v ne v.val).mpr rfl
  have beforeV := (anchor n v.val initial pre (by rw [initLen]; exact v.isLt)).trans initV
  have notTarget : target ≠ v.val := by
    intro equal
    let x := setOnly v true (fun _ => false)
    let W := wiresFrom pre (List.ofFn (setOnly a false x))
    let Z := wiresFrom pre (List.ofFn (setOnly a true x))
    let gx := g.op.eval (g.inputs.map fun i => W.getD i false)
    let gy := g.op.eval (g.inputs.map fun i => Z.getD i false)
    have lenW : W.length = k := by
      change (wiresFrom pre (List.ofFn (setOnly a false x))).length = _
      rw [length_wiresFrom,List.length_ofFn]
    have invAt : Inv n (List.ofFn x) (W ++ [gx]) after := by
      have first : W ++ [gx] = wiresFrom (pre ++ [g]) (List.ofFn (setOnly a false x)) := by
        rw [wiresFrom_append]
        rfl
      have second : after = elim n (pre ++ [g]) initial := by rw [elim_append,elim_cons]; rfl
      rw [first,second]
      apply inv_elim n _ (by simp) (pre ++ [g]) _ _ ?_ (inv_initMap a x)
      · intro h hh
        apply (shape h ?_).1
        rw [split]
        rcases List.mem_append.mp hh with hh | hh
        · exact List.mem_append_left _ hh
        · have same := List.mem_singleton.mp hh
          exact List.mem_append_right _ (same ▸ List.mem_cons_self)
    have gxTrue : gx = true := by
      have eq := (invAt.2 k).2
      change (wire after k).val (wiresFrom after.2 (List.ofFn x)) = (W ++ [gx]).getD k false at eq
      have wAt : wire after k = .inr v.val := by rw [← kLength,step_new,hAlias,equal]
      rw [wAt,getD_snoc_len _ _ _ _ lenW] at eq
      change evaluate after.2 v.val x = gx at eq
      rw [eval_input] at eq
      simpa [x,setOnly] using eq.symm
    have gyTrue : gy = true := by
      change g.op.eval (g.inputs.map fun i => Z.getD i false) = true
      rw [op]
      apply PEqualNP.Outside.L_meta_4903.Graph.or_true
      refine List.mem_map.mpr ⟨a.val,ga,?_⟩
      change evaluate pre a.val (setOnly a true x) = true
      rw [eval_input]
      simp [setOnly]
    let exc (i : ℕ) := i = a.val
    have preSame := agreement exc n pre (List.ofFn (setOnly a false x)) (List.ofFn (setOnly a true x))
      (by simp) (set_agrees a x false true exc rfl) (by
        intro p h hh _ i hi _ hit
        exact noPre h (List.mem_iff_getElem?.mpr ⟨p,hh⟩) (hit ▸ hi))
    have stepSame := agree_extend exc W Z gx gy preSame (fun _ => gxTrue.trans gyTrue.symm)
    have finSame := agreement exc (k+1) post (W ++ [gx]) (Z ++ [gy]) (by simp [lenW]) stepSame (by
      intro p h hh _ i hi _ hit
      exact noPost h (List.mem_iff_getElem?.mpr ⟨p,hh⟩) (hit ▸ hi))
    have same : evaluate (pre ++ g::post) C.output (setOnly a false x) =
        evaluate (pre ++ g::post) C.output (setOnly a true x) := by
      simp only [evaluate,wiresFrom_append]
      exact finSame.2 C.output notA
    rw [← split,pinFn,originalFn,one_true G _ a (Finset.mem_insert_self _ _) _] at same
    exact Bool.false_ne_true ((no_edge_on_singleton G B v hv).symm.trans same)
  have noG : g.inputs.contains v.val = false := by
    cases read : g.inputs.contains v.val with
    | false => rfl
    | true =>
      have h := onlyTarget v.val (List.mem_map.mpr ⟨v.val,List.contains_iff_mem.mp read,beforeV⟩)
      exact (notTarget h.symm).elim
  have dead (e : Gate × Option Gate × Stat) (he : e ∈ emits n initial original) (hnone : e.2.1 = none) :
      e.2.2 ≠ .inr v.val ∧ e.1.inputs.contains v.val = false := by
    have member : e ∈ (emits n initial original).filter inactive :=
      List.mem_filter.mpr ⟨he,by simp [inactive,hnone]⟩
    rw [loss_eq] at member
    rw [List.mem_singleton.mp member]
    exact ⟨fun h => notTarget (Sum.inr.inj (hAlias.symm.trans h)),noG⟩
  have keep := keep_reads n v.val v.isLt initial original (by rw [initLen]; exact v.isLt)
    shape (init_loc a v ne) dead
  rw [finish] at keep
  change opReads v.val D.gates = [] ++ opReads v.val original at keep
  rw [List.nil_append] at keep
  have clean : CleanL n D.gates := by
    change CleanL n saved.2
    rw [← finish]
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) original _ _
      (fun h hh => (shape h hh).1) (inv_initMap a _) (by intro p h hp; simp [initial] at hp)
  change (active D v).map Gate.op = (active C v).map Gate.op
  exact (retained_ops v.val D.gates (clean_nok _ _ clean)).symm.trans
    (keep.trans (normalized_ops C v.val minimum.1))

end PEqualNP.Outside.L_meta_4903.Remove

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_4903 :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>     have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x6.gates;     (∀ x8 ∉ x4, (x7 x8).length ≤ (3 : ℕ) ∧ ((x7 x8).length = (3 : ℕ) → ∀ x11 ∈ x7 x8, x11.op = PEqualNP.CircuitLowerBounds.GateOp.or)) ∧ ∃ x8 ∉ x4, (x7 x8).length ≤ (1 : ℕ);   (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → x6 x5 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x14 ∧ PEqualNP.MetaComplexity.circuitFun x1 x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x6 x14 := by
  have restrict := PEqualNP.Outside.L_meta_4903.Restrict.restrict
  have remove := PEqualNP.Outside.L_meta_4903.Remove.remove
  intro n G inst A C
  dsimp only
  intro _degree _girth away edge min computes profile
  let reads (D : Circuit) (v : Fin n) :=
    D.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wireLength (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_nil, List.length_cons]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have add (D : Circuit) (a : Fin n) (ok : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = D.size+1 ∧
        ∀ x, circuitFun n E x = (x a || circuitFun n D x) := by
    let last : Gate := ⟨.or,[a.val,D.output]⟩
    let E : Circuit := ⟨D.gates ++ [last],n+D.size⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ D.gates ++ [last] at hg
      rcases List.mem_append.mp hg with h | h
      · exact ok g h
      · have same := List.mem_singleton.mp h
        subst g
        simp [last]
    · change (D.gates ++ [last]).length = D.gates.length + 1
      simp
    · intro x
      let w := D.gates.foldl step (List.ofFn x)
      have len : w.length = n+D.size := by
        change (D.gates.foldl step (List.ofFn x)).length = n+D.gates.length
        rw [wireLength,List.length_ofFn]
      have primary : w.getD a.val false = x a := by
        change (D.gates.foldl step (List.ofFn x)).getD a.val false = _
        rw [keep _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
      change ((D.gates ++ [last]).foldl step (List.ofFn x)).getD (n+D.size) false = _
      rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change (w ++ [w.getD a.val false || (w.getD D.output false || false)]).getD (n+D.size) false = _
      rw [← len,List.getD_append_right _ _ _ _ (by omega),Nat.sub_self]
      change (w.getD a.val false || (w.getD D.output false || false)) = (x a || w.getD D.output false)
      simp only [primary,Bool.or_false]
  have insertFun (B : Finset (Fin n)) (a : Fin n) (x : Fin n → Bool) :
      graphFun G (insert a B) x = (x a || graphFun G B x) := by
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ v ∈ insert a B, x v = true) ||
      decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true)) = true ↔
      (x a || (decide (∃ v ∈ B, x v = true) ||
        decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true))) = true
    simp only [Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert]
    constructor
    · rintro (⟨v, hv, on⟩ | h)
      · rcases hv with rfl | hv
        · exact Or.inl on
        · exact Or.inr (Or.inl ⟨v,hv,on⟩)
      · exact Or.inr (Or.inr h)
    · rintro (on | ⟨v,hv,on⟩ | h)
      · exact Or.inl ⟨a,Or.inl rfl,on⟩
      · exact Or.inl ⟨v,Or.inr hv,on⟩
      · exact Or.inr h
  have independent (B : Finset (Fin n)) (a : Fin n) (absent : a ∉ B) (apart : ∀ v, ¬G.Adj a v)
      (x : Fin n → Bool) : graphFun G B (fun i => ite (i = a) false (x i)) = graphFun G B x := by
    let y (i : Fin n) := ite (i = a) false (x i)
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ v ∈ B, y v = true) ||
      decide (∃ p q, G.Adj p q ∧ y p = true ∧ y q = true)) = true ↔
      (decide (∃ v ∈ B, x v = true) ||
        decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true)) = true
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    have mark (v : Fin n) (hv : v ∈ B) : y v = x v := by
      have ne : v ≠ a := fun h => absent (h ▸ hv)
      simp only [y,ite_eq_right ne]
    have endpoints (p q : Fin n) (h : G.Adj p q) : y p = x p ∧ y q = x q := by
      have hp : p ≠ a := fun e => apart q (e ▸ h)
      have hq : q ≠ a := fun e => apart p (e ▸ h.symm)
      simp only [y,ite_eq_right hp,ite_eq_right hq,and_self]
    constructor
    · rintro (⟨v,hv,on⟩ | ⟨p,q,e,onP,onQ⟩)
      · exact Or.inl ⟨v,hv,(mark v hv).symm.trans on⟩
      · exact Or.inr ⟨p,q,e,(endpoints p q e).1.symm.trans onP,(endpoints p q e).2.symm.trans onQ⟩
    · rintro (⟨v,hv,on⟩ | ⟨p,q,e,onP,onQ⟩)
      · exact Or.inl ⟨v,hv,(mark v hv).trans on⟩
      · exact Or.inr ⟨p,q,e,(endpoints p q e).1.trans onP,(endpoints p q e).2.trans onQ⟩
  have high (B : Finset (Fin n)) : graphFun G B (fun _ => true) = true := by
    change (decide (∃ a ∈ B, (true : Bool) = true) ||
      decide (∃ p q, G.Adj p q ∧ (true : Bool) = true ∧ (true : Bool) = true)) = true
    simp only [Bool.or_eq_true,decide_eq_true_eq,and_true]
    exact Or.inr edge
  have low (B : Finset (Fin n)) : graphFun G B (fun _ => false) = false := by
    change (decide (∃ a ∈ B, (false : Bool) = true) ||
      decide (∃ p q, G.Adj p q ∧ (false : Bool) = true ∧ (false : Bool) = true)) = false
    simp
  have clear (B : Finset (Fin n)) : B ⊆ A → ∀ D : Circuit, IsMinimalCircuit n D →
      circuitFun n D = graphFun G B → ∃ E : Circuit, IsMinimalCircuit n E ∧
        circuitFun n E = graphFun G ∅ ∧ ∀ v ∉ A, (reads E v).map Gate.op = (reads D v).map Gate.op := by
    induction B using Finset.induction_on with
    | empty =>
      intro _ D dmin dfun
      exact ⟨D,dmin,dfun,by intro v hv; rfl⟩
    | @insert a B absent ih =>
      intro subset D dmin dfun
      have hA : a ∈ A := subset (Finset.mem_insert_self _ _)
      have sub : B ⊆ A := fun v hv => subset (Finset.mem_insert_of_mem hv)
      have apart (v : Fin n) : ¬G.Adj a v := fun h => away a v h hA
      have restricted (x : Fin n → Bool) : circuitFun n D (fun i => ite (i = a) false (x i)) = graphFun G B x := by
        rw [dfun,insertFun,independent B a absent apart x]
        rw [ite_eq_left rfl, Bool.false_or]
      obtain ⟨E, efan, _valid, small, agree⟩ := restrict n D a dmin.1
        ⟨fun _ => true, (restricted _).trans (high B)⟩ ⟨fun _ => false, (restricted _).trans (low B)⟩
      obtain ⟨U, ufan, usize, uval⟩ := add E a efan
      have eq : circuitFun n U = circuitFun n D := by
        funext x
        rw [uval,agree,restricted,dfun,insertFun]
      have bound := dmin.2 U ufan eq
      have small' : E.size + (reads D a).length ≤ D.size := small
      have one : (reads D a).length ≤ 1 := by omega
      obtain ⟨Rd, rm, rf, keepV⟩ := remove n G B a D absent apart edge dmin dfun one
      obtain ⟨V, vm, vf, same⟩ := ih sub Rd rm rf
      refine ⟨V,vm,vf,?_⟩
      intro v outside
      have notB : v ∉ B := fun hv => outside (sub hv)
      have notA : v ≠ a := fun hv => outside (hv ▸ hA)
      exact (same v outside).trans (keepV v notB notA)
  obtain ⟨E, em, ev, keepV⟩ := clear A (fun _ h => h) C min computes
  have counts (v : Fin n) (outside : v ∉ A) : (reads E v).length = (reads C v).length := by
    simpa only [List.length_map] using congrArg List.length (keepV v outside)
  refine ⟨E,em,ev,?_,?_⟩
  · intro v outside
    have before := profile.1 v outside
    change (reads C v).length ≤ 3 ∧ ((reads C v).length = 3 → ∀ g ∈ reads C v, g.op = .or) at before
    change (reads E v).length ≤ 3 ∧ ((reads E v).length = 3 → ∀ g ∈ reads E v, g.op = .or)
    rw [counts v outside]
    refine ⟨before.1, ?_⟩
    intro triple g hg
    have occurs : g.op ∈ (reads E v).map Gate.op := List.mem_map_of_mem hg
    rw [keepV v outside] at occurs
    obtain ⟨h,hh,op⟩ := List.mem_map.mp occurs
    exact op.symm.trans (before.2 triple h hh)
  · obtain ⟨v,outside,short⟩ := profile.2
    refine ⟨v,outside,?_⟩
    change (reads E v).length ≤ 1
    rw [counts v outside]
    exact short
