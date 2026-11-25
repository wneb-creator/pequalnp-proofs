import Mathlib.Tactic.ByContra
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

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

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Sum Bool Nat

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

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof


open CircuitProof

def PairInv (w₀ w₁ : List Bool) (a : List Stat) : Prop :=
  a.length = w₀.length ∧ w₀.length = w₁.length ∧
    ∀ i j, a.getD i (Sum.inl false) = Sum.inr j → w₀.getD i false = w₁.getD i false

lemma simplify_live_equal (g : Gate) (hg : Ok g) (m : ℕ)
    (a : List Stat) (w₀ w₁ : List Bool)
    (rel : ∀ i j, a.getD i (Sum.inl false) = Sum.inr j → w₀.getD i false = w₁.getD i false)
    (keep : isNotGate g.op = true ∨
      (simplify g.op m (g.inputs.map fun i => a.getD i (Sum.inl false))).1 ≠ none)
    (j : ℕ) (live : (simplify g.op m
      (g.inputs.map fun i => a.getD i (Sum.inl false))).2 = Sum.inr j) :
    g.op.eval (g.inputs.map fun i => w₀.getD i false) =
      g.op.eval (g.inputs.map fun i => w₁.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with hop | hop | hop
  · change op = GateOp.and at hop
    subst op
    simp only [isNotGate, Bool.false_eq_true, false_or] at keep
    rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, tail⟩⟩⟩
    · simp [simplify, simpAnd] at live
    · cases hu : a.getD u (Sum.inl false) <;>
        simp only [List.map_cons, List.map_nil, hu, simplify, simpAnd, ne_eq, not_true_eq_false] at keep
    · cases hu : a.getD u (Sum.inl false) with
      | inl b =>
        cases hv : a.getD v (Sum.inl false) <;>
          simp only [List.map_cons, List.map_nil, hu, hv, simplify, simpAnd, ne_eq, not_true_eq_false] at keep
      | inr r =>
        cases hv : a.getD v (Sum.inl false) with
        | inl b => simp only [List.map_cons, List.map_nil, hu, hv, simplify, simpAnd, ne_eq, not_true_eq_false] at keep
        | inr t =>
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [rel u r hu, rel v t hv]
    · simp at hlen
  · change op = GateOp.or at hop
    subst op
    simp only [isNotGate, Bool.false_eq_true, false_or] at keep
    rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, tail⟩⟩⟩
    · simp [simplify, simpOr] at live
    · cases hu : a.getD u (Sum.inl false) <;>
        simp only [List.map_cons, List.map_nil, hu, simplify, simpOr, ne_eq, not_true_eq_false] at keep
    · cases hu : a.getD u (Sum.inl false) with
      | inl b =>
        cases hv : a.getD v (Sum.inl false) <;>
          simp only [List.map_cons, List.map_nil, hu, hv, simplify, simpOr, ne_eq, not_true_eq_false] at keep
      | inr r =>
        cases hv : a.getD v (Sum.inl false) with
        | inl b => simp only [List.map_cons, List.map_nil, hu, hv, simplify, simpOr, ne_eq, not_true_eq_false] at keep
        | inr t =>
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [rel u r hu, rel v t hv]
    · simp at hlen
  · change op = GateOp.not at hop
    subst op
    cases ins with
    | nil => simp [simplify, simpNot] at live
    | cons u tail =>
      cases hu : a.getD u (Sum.inl false) with
      | inl b =>
        simp only [List.map_cons, hu, simplify, simpNot] at live
        cases live
      | inr r =>
        simp only [List.map_cons, GateOp.eval, List.headD_cons]
        rw [rel u r hu]

lemma pairInv_step (n : ℕ) (g : Gate) (hg : Ok g)
    (w₀ w₁ : List Bool) (acc : List Stat × List Gate)
    (inv : PairInv w₀ w₁ acc.1)
    (keep : isNotGate g.op = true ∨
      (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 ≠ none) :
    PairInv (wiresFrom [g] w₀) (wiresFrom [g] w₁) (elimStep n acc g).1 := by
  obtain ⟨len₀, len₁, rel⟩ := inv
  refine ⟨by simp [elimStep, wiresFrom, len₀], by simp [wiresFrom, len₁], ?_⟩
  intro i j live
  by_cases hi : i = acc.1.length
  · subst i
    simp only [elimStep, getD_snoc_eq] at live
    change (w₀ ++ [_]).getD acc.1.length false = (w₁ ++ [_]).getD acc.1.length false
    rw [len₀, getD_snoc_eq, len₁, getD_snoc_eq]
    exact simplify_live_equal g hg _ _ _ _ rel keep j live
  · change (acc.1 ++ [_]).getD i (Sum.inl false) = Sum.inr j at live
    rw [getD_snoc_ne _ _ _ _ hi] at live
    change (w₀ ++ [_]).getD i false = (w₁ ++ [_]).getD i false
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    exact rel i j live

lemma elim_pair_or_saves (n : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, Ok g)
    (w₀ w₁ : List Bool) (acc : List Stat × List Gate) (inv : PairInv w₀ w₁ acc.1) :
    nonNotCount (elim n gs acc).2 + 1 ≤ nonNotCount acc.2 + nonNotCount gs ∨
      PairInv (wiresFrom gs w₀) (wiresFrom gs w₁) (elim n gs acc).1 := by
  induction gs generalizing w₀ w₁ acc with
  | nil => exact Or.inr inv
  | cons g gs ih =>
    let d := if !(isNotGate g.op) then 1 else 0
    have count : nonNotCount (g :: gs) = nonNotCount gs + d := by
      exact opCount_cons (fun op => !(isNotGate op)) g gs
    have stepBudget : nonNotCount (elimStep n acc g).2 ≤ nonNotCount acc.2 + d := by
      have h := elim_nonNotCount n [g] acc
      simpa [elim, nonNotCount, d] using h
    by_cases saves : nonNotCount (elimStep n acc g).2 + 1 ≤ nonNotCount acc.2 + d
    · left
      have rest := elim_nonNotCount n gs (elimStep n acc g)
      change nonNotCount (elim n gs (elimStep n acc g)).2 + 1 ≤ _
      rw [count]
      omega
    · have keep : isNotGate g.op = true ∨
          (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 ≠ none := by
        by_cases hn : isNotGate g.op = true
        · exact Or.inl hn
        · right
          intro gone
          have val : isNotGate g.op = false := Bool.eq_false_iff.mpr hn
          have cost : nonNotCount (elimStep n acc g).2 = nonNotCount acc.2 := by
            unfold elimStep
            rw [gone]
            simp only [Option.toList_none, List.append_nil]
          have one : d = 1 := by simp [d, val]
          omega
      have stepInv := pairInv_step n g (hok g List.mem_cons_self) w₀ w₁ acc inv keep
      have rest := ih (fun h mem => hok h (List.mem_cons_of_mem _ mem))
        (wiresFrom [g] w₀) (wiresFrom [g] w₁) (elimStep n acc g) stepInv
      rcases rest with saved | relation
      · left
        change nonNotCount (elim n gs (elimStep n acc g)).2 + 1 ≤ _
        rw [count]
        omega
      · exact Or.inr relation

def initialStats (n : ℕ) : List Stat :=
  List.ofFn fun i : Fin (n + 1) => if i.val < n then Sum.inr i.val else Sum.inl false

lemma initialStats_get (n i : ℕ) :
    (initialStats n).getD i (Sum.inl false) =
      if i < n then Sum.inr i else Sum.inl false := by
  by_cases hi : i < n + 1
  · unfold initialStats
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some, List.getElem_ofFn]
  · have hi' : ¬ i < n := by omega
    simp [initialStats, hi, hi']

lemma initialStats_inv (n : ℕ) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x ++ [false]) (initialStats n, []) := by
  refine ⟨by simp [initialStats], ?_⟩
  intro i
  simp only [initialStats_get]
  by_cases hi : i < n
  · simp only [hi, ↓reduceIte, Stat.Valid, Stat.val]
    refine ⟨by omega, ?_⟩
    change (List.ofFn x).getD i false = (List.ofFn x ++ [false]).getD i false
    rw [List.getD_append _ _ _ _ (by simpa using hi)]
  · simp only [hi, ↓reduceIte, Stat.Valid, Stat.val]
    refine ⟨trivial, ?_⟩
    by_cases he : i = n
    · subst i
      simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma initialStats_pair (n : ℕ) (x : Fin n → Bool) :
    PairInv (List.ofFn x ++ [false]) (List.ofFn x ++ [true]) (initialStats n) := by
  refine ⟨by simp [initialStats], by simp, ?_⟩
  intro i j live
  rw [initialStats_get] at live
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi)]
  · simp [hi] at live

lemma elim_ok (n : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, Ok g)
    (acc : List Stat × List Gate) (ha : ∀ g ∈ acc.2, Ok g) :
    ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g gs ih =>
    apply ih (fun h mem => hok h (List.mem_cons_of_mem _ mem)) (elimStep n acc g)
    intro h mem
    rcases List.mem_append.mp mem with before | emitted
    · exact ha h before
    · exact simplify_ok _ _ _ h (by simpa using emitted)

lemma restrict_last_binary (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (nonconstant : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn y ++ [false]))
    (depends : ∃ x : Fin n → Bool,
      C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn x ++ [true])) :
    ∃ D : Circuit, FanInTwo D ∧
      nonNotCount D.gates + 1 ≤ nonNotCount C.gates ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [false]) := by
  let result := elim n C.gates (initialStats n, [])
  have sound (x : Fin n → Bool) :
      (result.1.getD C.output (Sum.inl false)).val (wiresFrom result.2 (List.ofFn x)) =
        C.eval (List.ofFn x ++ [false]) :=
    ((inv_elim n (List.ofFn x) (by simp) C.gates _ _ fan (initialStats_inv n x)).2 C.output).2
  cases out : result.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, y, different⟩ := nonconstant
    apply different
    rw [← sound x, ← sound y, out]
    rfl
  | inr j =>
    refine ⟨⟨result.2, j⟩, elim_ok n C.gates fan _ (by simp), ?_, ?_⟩
    · obtain ⟨x, different⟩ := depends
      have split := elim_pair_or_saves n C.gates fan
        (List.ofFn x ++ [false]) (List.ofFn x ++ [true])
        (initialStats n, []) (initialStats_pair n x)
      rcases split with saved | relation
      · simpa [nonNotCount] using saved
      · exfalso
        exact different (relation.2.2 C.output j out)
    · intro x
      have h := sound x
      rw [out] at h
      exact h

def fullEdge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def deletedEdge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def extend (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, b]

lemma extend_list (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (extend x b) = List.ofFn x ++ [b] := by
  rfl

lemma petersen_restrict_binary (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = fullEdge x) :
    ∃ D : Circuit, FanInTwo D ∧
      nonNotCount D.gates + 1 ≤ nonNotCount C.gates ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = deletedEdge x := by
  have evals (x : Fin 9 → Bool) (b : Bool) :
      C.eval (List.ofFn x ++ [b]) = fullEdge (extend x b) := by
    rw [← extend_list]
    exact correct _
  have nonconstant : ∃ x y : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn y ++ [false]) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [evals, evals]
    decide
  have depends : ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn x ++ [true]) := by
    refine ⟨fun j => decide (j = 4), ?_⟩
    rw [evals, evals]
    decide
  obtain ⟨D, fanD, saved, agrees⟩ := restrict_last_binary 9 C fan nonconstant depends
  refine ⟨D, fanD, saved, ?_⟩
  intro x
  rw [agrees, evals]
  simp [fullEdge, extend, deletedEdge]

end PEqualNP.Outside.L_meta_2592.Restriction
