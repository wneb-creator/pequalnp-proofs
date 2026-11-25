import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4721

-- The circuit simplifier and nine-input lower bound follow L_meta_2917 and L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace BranchGraph

variable {V : Type*} [DecidableEq V]

def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, G.Adj a b

omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w} := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab

lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w} ↔ G.Adj u w := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, by simp, w, by simp, h⟩

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

section FiniteGraph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ v ∉ removed)

lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u := by
  intro v membership
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at membership ⊢
  exact ⟨membership.1, fun vIn => membership.2 (h vIn)⟩

lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w := by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B) := by
    ext z
    simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => ⟨⟨hz.1, fun zIn => hz.2 (h zIn)⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [e u, e w, same]

def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group, ∀ w ∈ group, (neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w

end FiniteGraph

end BranchGraph

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

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

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ Nat

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

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

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


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


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


theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]


end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

lemma Least.hcl {m f gs o} (L : Least m f gs o) : CleanL m gs := L.1
lemma Least.hev {m f gs o} (L : Least m f gs o) (x : Fin m → Bool) : vl gs x o = f x := L.2.1 x
lemma Least.hmin {m f gs o} (L : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length := L.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ gs.length ≤ C.gates.length ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · simpa [hacc] using elim_len n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ gs.length ≤ C.gates.length := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, clen, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  have short := Nat.find_min' existsAdmissible (show admissible gs.length from ⟨gs,o,clean,count,he,rfl⟩)
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb, by omega⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end LocalSection1

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]


end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm

theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p, Reads gs p w := by
  by_cases isInput : w < n
  · let v : Fin n := ⟨w, isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p := w - n
    have wire : w = n + p := by dsimp [p]; omega
    have pLt : p < gs.length := by omega
    have notOut : out ≠ n + p := by omega
    obtain ⟨q, _, read⟩ := least.live nonconstant p pLt notOut
    exact ⟨q, wire.symm ▸ read⟩

theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]

theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length := by
  obtain ⟨p, g, hit, reads⟩ := least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound := (List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p, g, hit, reads, by omega⟩

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact PEqualNP.Outside.L_meta_4721.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have := b.isLt; omega))
  · simp [predecessors, internal]

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩

private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w, x w = true → w = u ∨ w = v) :
    edgeValue G x = false := by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s, t, es, hs, ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es

private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a && b) := by
  cases a <;> cases b
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u := j) (v := j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput, h.ne.symm])

private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i ≠ j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u ∨ k = v)) a b) = (a || b) := by
  have hu : pairInput i j (fun k => decide (k = u ∨ k = v)) a b u = true := by
    simp [pairInput, hiu.ne.symm, huj]
  have hv : pairInput i j (fun k => decide (k = u ∨ k = v)) a b v = true := by
    simp [pairInput, hvi, hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput, hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu

theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool, ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False := by
  obtain ⟨outerA, ha⟩ := factors (fun _ => false)
  obtain ⟨outerO, ho⟩ := factors (fun k => decide (k = u ∨ k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False := by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f, hf⟩ := cut_factors hcl cut out (fun k => k = i ∨ k = j) base controlled
  refine ⟨f, fun a b => ?_⟩
  have agree : ∀ k, ¬ (k = i ∨ k = j) → pairInput i j base a b k = base k := by
    intro k hk
    simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j, G.Adj i j → ∃ u v,
      G.Adj i u ∧ G.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adjacent
  obtain ⟨u, v, hiu, hjv, huj, hvi, huv⟩ := witnesses i j adjacent
  have iFirst := (mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst := (mem_firstInputGroup clean out live cut j).mp jIn
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))

end PetersenFirstGroup

namespace PetersenNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)


def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)


lemma noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true ↔ ∃ a b, (a, b) ∈ es ∧ x a = true ∧ x b = true := by
  simp only [edgeFun, List.any_eq_true, Bool.and_eq_true, Prod.exists]


def graph (es : Edges) (noSelf : ∀ e ∈ es, e.1 ≠ e.2) : SimpleGraph Vertex where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => noSelf (v, v) he rfl) (fun he => noSelf (v, v) he rfl)⟩

end PetersenNine

open PetersenNine

def petersenGraph : SimpleGraph Vertex := graph edges noLoops

def petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S := by
  constructor
  · intro h
    obtain ⟨a, b, edge, ha, hb⟩ := (edgeFun_true edges _).mp h
    exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, Or.inl edge⟩
  · rintro ⟨a, ha, b, hb, adjacent⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, decide_eq_true ha, decide_eq_true hb⟩
    · exact ⟨b, a, edge, decide_eq_true hb, decide_eq_true ha⟩

theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex, petersenGraph.Adj i j →
      ∃ u v, petersenGraph.Adj i u ∧ petersenGraph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ petersenGraph.Adj u v := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length), w ≠ (⟨out, outValid⟩ : Fin (n + gs.length)) → ∃ v, readEdge gs w v := by
  intro w notOutput
  have notSame : w.val ≠ out := fun eq => notOutput (Fin.ext eq)
  obtain ⟨p, g, atSlot, reads, bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p, bound⟩, p, g, atSlot, rfl, reads⟩

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]

theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]

theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  change (_ ↔ decode (code I) O)
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n), vl gs (setInput S) out.val = true ↔ BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code, decode, factors⟩ := finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

abbrev petersenF := edgeFun edges

private theorem petersen_dependency_samples : ∀ v : Vertex, ∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w)))) ≠ petersenF (fun i => decide (i = w)) := by
  decide +kernel

theorem petersen_depends (v : Vertex) : Dep petersenF v := by
  obtain ⟨w, hw⟩ := petersen_dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

theorem petersen_nonconstant : ∃ x y : Vertex → Bool, petersenF x ≠ petersenF y :=
  dep_nc (petersen_depends 0)

private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true := by
  decide +kernel

theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y, petersenF (Function.update x v b) ≠ petersenF (Function.update y v b) := by
  obtain ⟨no, yes⟩ := petersen_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩


lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9, petersenGraph.Adj u v ∧ x u = true ∧ x v = true := by
  change PetersenNine.edgeFun PetersenNine.edges x = true ↔ _
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, adjacent, ha, hb⟩
    change (a, b) ∈ PetersenNine.edges ∨ (b, a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenNine

def cube (i j k : Vertex) (m u : Nat) (b : Bool) (v : Vertex) : Bool :=
  if v = k then b else if v = i then u.testBit 0 else if v = j then u.testBit 1 else m.testBit v.val

def witnessTable : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,57,0,53,53,57,0,0,0,549,0,2085,8229,549,0,1061,0,0,16421,2085,0,165,293,0,0,165,0,53,0,57,0,53,0,0,0,0,53,0,0,53,0,0,57,57,0,1061,0,0,16421,0,0,0,1061,0,0,1061,0,293,165,0,0,0,0,549,0,165,4133,165,1061,0,0,0,0,53,0,57,57,53,0,0,0,0,0,0,0,0,0,0,0,53,0,0,57,0,0,53,57,0,16421,0,101,0,4133,0,1061,0,101,293,0,0,4133,0,0,549,0,0,293,0,16421,0,0,0,8229,4133,293,53,0,53,0,0,0,0,0,57,0,0,101,0,0,4133,2085,0,0,549,0,2085,101,0,293,101,0,0,0,549,0,2085,8229,549,0,1061,0,57,0,0,53,0,0,57,53,0,0,0,0,0,0,0,0,0,0,0,53,0,0,57,0,0,53,57,8229,0,0,101,0,0,0,101,0,549,16421,0,101,0,0,0,101,165,0,549,0,0,0,0,0,16421,8229,0,53,0,53,0,57,0,0,0,0,2085,0,165,0,165,8229,4133,0,0,16421,2085,0,165,293,0,0,165,16421,0,101,0,4133,0,1061,0,101,0,57,0,0,53,0,0,57,53,0,0,0,0,0,0,0,0,0,57,0,53,0,0,0,0,0,53,293,0,101,0,8229,0,0,1061,101,0,1061,0,0,165,0,0,0,165,0,0,1061,0,2085,1061,0,0,0,0,0,53,0,53,57,57,0,0,0,57,0,53,0,57,0,0,0,293,0,0,4133,0,0,549,0,0,8229,0,0,101,0,0,0,101,0,53,0,57,0,0,0,0,0,57,0,0,0,0,0,0,0,0,0,549,0,0,8229,0,0,0,549,0,16421,549,0,165,0,0,0,0,101,293,0,101,2085,0,549,0,0,0,4133,0,0,101,0,0,101,0,0,0,57,0,0,57,0,0,53,53,293,0,16421,0,0,0,8229,4133,293,549,16421,0,101,0,0,0,101,165,293,0,101,0,8229,0,0,1061,101,549,0,0,8229,0,0,0,549,0,0,0,0,0,0,0,0,0,0,0,8229,0,0,0,0,0,165,101,53,0,57,0,0,0,0,0,53,53,0,0,57,0,0,57,53,0,0,1061,0,0,16421,0,0,0,1061,57,0,57,0,0,0,0,0,53,0,549,0,0,0,0,0,16421,8229,0,1061,0,0,165,0,0,0,165,16421,549,0,165,0,0,0,0,101,0,8229,0,0,0,0,0,165,101,0,0,0,0,0,0,0,0,0,0,2085,16421,0,0,165,0,0,293,0,53,0,57,0,57,0,0,0,0,0,1061,0,293,165,0,0,0,0,0,101,0,0,4133,2085,0,0,0,57,0,57,0,53,0,0,0,0,0,1061,0,2085,1061,0,0,0,293,0,101,2085,0,549,0,0,0,57,0,53,0,0,0,0,0,57,0,2085,16421,0,0,165,0,0,293,0,0,0,0,0,0,0,0,0,0,0,4133,0,0,293,293,0,0,0,549,0,165,4133,165,1061,0,0,549,0,2085,101,0,293,101,0,0,0,2085,0,165,0,165,8229,4133,0,0,0,57,0,57,53,53,0,0,4133,0,0,101,0,0,101,0,0,57,0,0,53,0,0,53,57,0,0,57,0,53,0,53,0,0,0,0,0,4133,0,0,293,293,0,0,0,0,0,0,0,0,0,0,0]

def witness (i j k : Vertex) : Nat := witnessTable[i.val * 81 + j.val * 9 + k.val]?.getD 0

def bad (i j k : Vertex) : Prop := witness i j k ≠ 0

def response (i j k : Vertex) (m u : Nat) : Bool × Bool :=
  (petersenF (cube i j k m u false), petersenF (cube i j k m u true))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma witness_valid : ∀ i j k : Vertex, witness i j k ≠ 0 →
    let w := witness i j k - 1
    let a := response i j k (w / 64) (w % 4)
    let b := response i j k (w / 64) (w / 4 % 4)
    let c := response i j k (w / 64) (w / 16 % 4)
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by decide +kernel

lemma excludes_tie {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (out : Fin (9 + gs.length)) (hout : out.val = o)
    (live : ∀ w : Fin (9 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i j k : Vertex)
    (tie : firstInputBoundary L.hcl out live i = firstInputBoundary L.hcl out live j)
    (later : firstInputBoundary L.hcl out live i < firstInputBoundary L.hcl out live k) :
    ¬ bad i j k := by
  intro tested
  let label := firstInputBoundary L.hcl out live
  let cut := label i
  have stop : FirstBranchRoute.Terminal (readEdge gs) out cut :=
    FirstBranchRoute.first_stops _ _ _ _ _
  let w := witness i j k - 1
  let m := w / 64
  let bit (u : Nat) := vl gs (cube i j k m u false) cut.val
  have eqbit (u : Nat) (b : Bool) : vl gs (cube i j k m u b) cut.val = bit u := by
    apply agree_on_input_ancestors L.hcl
    intro s path
    have prior : label s ≤ cut :=
      FirstBranchRoute.ancestor_first_le _ _ (read_order L.hcl) live path stop
    have ne : s ≠ k := fun e => (not_lt_of_ge (e ▸ prior)) later
    simp [cube, ne]
  have same (u v : Nat) (h : bit u = bit v) (b : Bool) :
      petersenF (cube i j k m u b) = petersenF (cube i j k m v b) := by
    let group := firstInputGroup L.hcl out live cut
    have memI : i ∈ group := (mem_firstInputGroup _ _ _ _ _).2 rfl
    have memJ : j ∈ group := (mem_firstInputGroup _ _ _ _ _).2 tie.symm
    obtain ⟨f, hf⟩ := PetersenCutIndependent.cut_factors L.hcl cut out
      (fun z => z ∈ group) (cube i j k m v b) (firstInputGroup_controlled L.hcl out live cut)
    have hu := hf (cube i j k m u b) (by
      intro z hz
      have ni : z ≠ i := fun e => hz (e ▸ memI)
      have nj : z ≠ j := fun e => hz (e ▸ memJ)
      simp [cube, ni, nj])
    have hv := hf (cube i j k m v b) (fun _ _ => rfl)
    rw [hout, L.hev] at hu hv
    rw [← hu, ← hv, eqbit, eqbit, h]
  have resp (u v : Nat) (h : bit u = bit v) : response i j k m u = response i j k m v :=
    Prod.ext (same u v h false) (same u v h true)
  obtain ⟨ab, bc, ac⟩ := witness_valid i j k tested
  let a := w % 4
  let b := w / 4 % 4
  let c := w / 16 % 4
  have one : bit a ≠ bit b := fun h => ab (resp a b h)
  have two : bit b ≠ bit c := fun h => bc (resp b c h)
  have three : bit a ≠ bit c := fun h => ac (resp a c h)
  cases ha : bit a <;> cases hb : bit b <;> cases hc : bit c <;> simp_all

def cuts : List (Finset Vertex) :=
  [{1,4,7,8}, {2,4,5,6}, {0,3,6,7}]

def maskSet (m : BitVec 9) : Finset Vertex := Finset.univ.filter fun i => m.getLsbD i.val

lemma represented (s : Finset Vertex) : ∃ m, maskSet m = s := by
  let bits := List.ofFn (fun i : Vertex => decide (i ∈ s))
  let m : BitVec 9 := (BitVec.ofBoolListLE bits).cast (by simp [bits])
  refine ⟨m,?_⟩
  ext i
  simp only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and,m,BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE,bits]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt] <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cover_shapes (s : Finset Vertex) (card : s.card ≤ 5)
    (covers : ∀ e ∈ edges, e.1 ∈ s ∨ e.2 ∈ s) : sᶜ ∈ cuts ∧ s.card = 5 := by
  obtain ⟨m,rfl⟩ := represented s
  have hh : ∀ m : BitVec 9, (maskSet m).card ≤ 5 →
      edges.all (fun e => decide (e.1 ∈ maskSet m ∨ e.2 ∈ maskSet m)) = true →
      (maskSet m)ᶜ ∈ cuts ∧ (maskSet m).card = 5 := by decide +kernel
  exact hh m card (List.all_eq_true.mpr fun e he => decide_eq_true (covers e he))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pair_check :
    ∀ i j k : Vertex, i ≠ j → petersenGraph.Adj i k → petersenGraph.Adj j k →
      witness i j k ≠ 0 := by
  change ∀ i j k : Vertex, i ≠ j → ((i,k) ∈ edges ∨ (k,i) ∈ edges) →
    ((j,k) ∈ edges ∨ (k,j) ∈ edges) → witness i j k ≠ 0
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cut_check :
    ∀ t ∈ cuts, ∀ i ∉ t, ∀ j ∈ t, ¬petersenGraph.Adj i j →
      ∃ k ∈ t, petersenGraph.Adj i k ∧ witness i j k ≠ 0 := by
  intro t ht
  simp only [cuts,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl <;> unfold petersenGraph graph <;> decide +kernel

lemma terminal_class {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (bound : nonNotCount gs ≤ 13) :
    ∃ t ∈ cuts, ∀ v ∈ t, PetersenScratch.occurrences v (PetersenCutFormula.wireFormula 0 gs o) ≤ 1 := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  have valid := least_petersen_output_valid L
  let out : Fin (9 + gs.length) := ⟨o,valid⟩
  have live := least_read_edge_live L petersen_nonconstant petersen_depends petersen_restrict_nonconstant valid
  let label := firstInputBoundary L.hcl out live
  let bs : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x out.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x o = _
    rw [L.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have indep (r) := firstInputGroup_independent L.hcl out live (predecessors_nodup L petersen_nonconstant)
    petersenGraph computes petersen_graph_alternate_neighbors r
  have diff (i j : Vertex) (e : petersenGraph.Adj i j) : label i ≠ label j := by
    intro h
    exact indep (label i) i ((mem_firstInputGroup _ _ _ _ _).2 rfl)
      j ((mem_firstInputGroup _ _ _ _ _).2 h.symm) e
  have marked (S : Finset Vertex) : vl gs (setInput S) out.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) o = true ↔ _
    rw [L.hev]
    exact petersen_graph_marked_edges S
  have leout (v : Vertex) : label v ≤ out := wire_le_output L.hcl out live _
  have branch (v : Vertex) (h : label v ≠ out) : label v ∈ bs := by
    have stop := FirstBranchRoute.first_stops (readEdge gs) out (read_order L.hcl) live (inputWire gs v)
    exact in_circuit_branches.mpr (stop.resolve_left h)
  let s := Finset.univ.filter fun i : Vertex => ∃ k, petersenGraph.Adj i k ∧ label i < label k
  have smem (i : Vertex) : i ∈ s ↔ ∃ k, petersenGraph.Adj i k ∧ label i < label k := by simp [s]
  have contained : s.image label ⊆ bs := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, _, lt⟩ := (smem v).mp hv
    exact branch v (ne_of_lt (lt_of_lt_of_le lt (leout k)))
  have inject : Set.InjOn label (s : Set Vertex) := by
    intro i hi j hj same
    by_contra ne
    obtain ⟨k, e, lk⟩ := (smem i).mp hi
    obtain ⟨l, f, ll⟩ := (smem j).mp hj
    have stop := FirstBranchRoute.first_stops (readEdge gs) out (read_order L.hcl) live (inputWire gs i)
    have twin := circuit_branch_class_twins L.hcl out live petersenGraph marked (label i) (leout i)
      stop (indep (label i))
    have im := (class_mem label (label i) i).mpr rfl
    have jm := (class_mem label (label i) j).mpr same.symm
    have km : k ∈ BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) i := by
      simp [BranchGraph.neighborsAfter, e, classes_before_mem, lk.le]
    have lm : l ∈ BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) j := by
      rw [← same] at ll
      simp [BranchGraph.neighborsAfter, f, classes_before_mem, ll.le]
    have sameNeighbors := twin i im j jm ⟨k, km⟩ ⟨l, lm⟩
    change BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) i =
      BranchGraph.neighborsAfter petersenGraph (classesBefore label (label i)) j at sameNeighbors
    rw [sameNeighbors] at km
    have jk := (Finset.mem_filter.mp km).2.1
    exact excludes_tie L out rfl live i j k same lk (pair_check i j k ne e jk)
  have cardImage := Finset.card_image_of_injOn inject
  have bb := branching_budget L.hcl valid (fun w hw hne => by
    let wire : Fin (9 + gs.length) := ⟨w, hw⟩
    obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
    exact ⟨p, g, hg, hw'⟩)
    (bs.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bb
  have total := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at total
  have small : bs.card ≤ 5 := by omega
  have smallS : s.card ≤ 5 := by
    rw [← cardImage]
    exact (Finset.card_le_card contained).trans small
  have covers : ∀ e ∈ edges, e.1 ∈ s ∨ e.2 ∈ s := by
    intro e he
    have adj : petersenGraph.Adj e.1 e.2 := Or.inl he
    rcases lt_or_gt_of_ne (diff _ _ adj) with h | h
    · exact Or.inl ((smem _).mpr ⟨_, adj, h⟩)
    · exact Or.inr ((smem _).mpr ⟨_, adj.symm, h⟩)
  obtain ⟨shape, sc⟩ := cover_shapes s smallS covers
  have allBranches : s.image label = bs := Finset.eq_of_subset_of_card_le contained (by omega)
  refine ⟨sᶜ, shape, ?_⟩
  intro j hj
  have last : label j = out := by
    by_contra h
    have bj := branch j h
    rw [← allBranches] at bj
    obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp bj
    have na : ¬petersenGraph.Adj i j := fun a => diff i j a eq
    obtain ⟨k, hk, e, tested⟩ := cut_check _ shape i (by simpa using hi) j hj na
    have lt : label i < label k := by
      rcases lt_or_gt_of_ne (diff i k e) with l | l
      · exact l
      · exact False.elim ((Finset.mem_compl.mp hk) ((smem k).mpr ⟨i, e.symm, l⟩))
    exact excludes_tie L out rfl live i j k eq lt tested
  have occ := firstInputBoundary_occurrences_le_one L.hcl out live (predecessors_nodup L petersen_nonconstant) 0 j
  change PetersenScratch.occurrences j (PetersenCutFormula.wireFormula 0 gs (label j).val) ≤ 1 at occ
  rwa [last] at occ

namespace CoverCheck

abbrev M := BitVec 7

def raw : List M := [66, 68, 8, 16, 32]
def profiles : List M := [102, 74, 84, 56]
def cells : List (M × M) :=
  [(102,1),(102,8),(102,16),(74,1),(74,4),(74,16),(74,32),(84,1),(84,2),(84,8),(84,32),(56,1),(56,2),(56,4),(56,64)]

def hit (cell : M × M) (z : M) : Bool :=
  (cell.1 &&& z) == 0 && (cell.2 &&& z) != 0

def key (z : M) : M := if z.toNat ≤ (~~~z).toNat then z else ~~~z

lemma key_flip (z : M) : key (~~~z) = key z := by
  exact (show ∀ a : M, key (~~~a) = key a by decide +kernel) z

def seeds : List M := raw.map key
def lits (xs : List M) := xs ++ xs.map (fun z => ~~~z)
def products (xs : List M) := (lits xs).flatMap fun a =>
  (lits xs).map fun b => key (a &&& b)

def Builds : List M → List M → Prop
  | _, [] => True
  | xs, a :: tail => a ∈ products xs ∧ Builds (a :: xs) tail

def unseen (xs wanted : List M) := (wanted.filter (fun a => !(xs.contains a))).dedup

def candidates (xs need : List M) (fuel : Nat) : List M :=
  if need.length < fuel then (products xs).eraseDups
  else need.filter fun a => (products xs).contains a

lemma candidate_mem {xs need : List M} {fuel : Nat} {a : M}
    (prod : a ∈ products xs) (room : need.length < fuel ∨ a ∈ need) :
    a ∈ candidates xs need fuel := by
  unfold candidates
  split
  · simpa using prod
  · rename_i tight
    exact List.mem_filter.mpr ⟨room.resolve_left tight, List.contains_iff_mem.mpr prod⟩

def weCan (wanted : List M) : Nat → List M → Bool
  | fuel, xs =>
    let need := unseen xs wanted
    if need.isEmpty then true else if need.length > fuel then false else
      match fuel with
      | 0 => false
      | k + 1 =>
        (candidates xs need fuel).any fun a =>
          !(xs.contains a) && (need.length < fuel || need.contains a) && weCan wanted k (a :: xs)

lemma mem_unseen {a : M} {xs wanted : List M} :
    a ∈ unseen xs wanted ↔ a ∈ wanted ∧ a ∉ xs := by simp [unseen]

lemma distinct_unseen (xs wanted : List M) : (unseen xs wanted).Nodup := by
  exact List.nodup_dedup _

lemma count_unseen {xs wanted tail : List M} (hall : ∀ a ∈ wanted, a ∈ xs ∨ a ∈ tail) :
    (unseen xs wanted).length ≤ tail.length := by
  have subset : (unseen xs wanted).toFinset ⊆ tail.toFinset := by
    intro a ha
    obtain ⟨hw, hnot⟩ := mem_unseen.mp (List.mem_toFinset.mp ha)
    exact List.mem_toFinset.mpr ((hall _ hw).resolve_left hnot)
  exact (List.toFinset_card_of_nodup (distinct_unseen xs wanted)) ▸
    ((Finset.card_le_card subset).trans (List.toFinset_card_le _))

lemma builds_mono {xs ys tail : List M} (inc : ∀ a ∈ xs, a ∈ ys) (b : Builds xs tail) : Builds ys tail := by
  induction tail generalizing xs ys with
  | nil => trivial
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := b
    have li : ∀ b ∈ lits xs, b ∈ lits ys := by
      intro b bh
      simp only [lits, List.mem_append, List.mem_map] at *
      rcases bh with h | ⟨c,h,rfl⟩
      · exact Or.inl (inc _ h)
      · exact Or.inr ⟨_,inc _ h,rfl⟩
    refine ⟨?_, ih (fun z h => ?_) ht⟩
    · unfold products at *
      simp only [List.mem_flatMap, List.mem_map] at ha ⊢
      obtain ⟨x,hx,y,hy,e⟩ := ha
      exact ⟨x,li _ hx,y,li _ hy,e⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (inc _ h)

lemma weCan_ok_aux {wanted xs tail : List M} (fuel : Nat) (h : Builds xs tail)
    (small : tail.length ≤ fuel) (hall : ∀ a ∈ wanted, a ∈ xs ∨ a ∈ tail) :
    weCan wanted fuel xs = true := by
  induction tail generalizing fuel xs with
  | nil =>
    have empty : unseen xs wanted = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro a ha
      have hh := mem_unseen.mp ha
      simpa using (hall _ hh.1).resolve_left hh.2)
    cases fuel <;> simp [weCan, empty]
  | cons a tail ih =>
    obtain ⟨prod, run⟩ := h
    by_cases already : a ∈ xs
    · apply ih fuel (builds_mono (fun z hz => (List.mem_cons.mp hz).elim (fun e => e ▸ already) id) run) (by simpa using Nat.le_trans (Nat.le_succ _) small)
      intro z hz
      rcases hall z hz with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl already
        · exact Or.inr h
    · cases fuel with
      | zero => simp at small
      | succ k =>
        have le := (count_unseen hall).trans small
        rw [weCan]
        split
        · rfl
        · rw [if_neg (by omega)]
          apply List.any_eq_true.mpr
          have room : (unseen xs wanted).length < k+1 ∨ a ∈ unseen xs wanted := by
            by_contra! no
            have notWanted : a ∉ wanted := fun h => no.2 (mem_unseen.mpr ⟨h, already⟩)
            have shorter := count_unseen (xs := xs) (wanted := wanted) (tail := tail) (by
              intro z hz
              rcases hall z hz with h | h
              · exact Or.inl h
              · exact Or.inr ((List.mem_cons.mp h).resolve_left (fun e => notWanted (e ▸ hz))))
            simp only [List.length_cons] at small
            omega
          refine ⟨a, candidate_mem prod room, ?_⟩
          have rest := ih k run (by simpa using small) (by
            intro z hz
            rcases hall z hz with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl List.mem_cons_self
              · exact Or.inr h)
          simpa [already, rest] using room

def options (c : M × M) : List M :=
  match c.1.toNat, c.2.toNat with
  | 102, 1 => [1,9,17,25]
  | 102, 8 => [8,9,24,25]
  | 102, 16 => [16,17,24,25]
  | 74, 1 => [1,5,17,21,33,37,49,53]
  | 74, 4 => [4,5,20,21,36,37,52,53]
  | 74, 16 => [16,17,20,21,48,49,52,53]
  | 74, 32 => [32,33,36,37,48,49,52,53]
  | 84, 1 => [1,3,9,11,33,35,41,43]
  | 84, 2 => [2,3,10,11,34,35,42,43]
  | 84, 8 => [8,9,10,11,40,41,42,43]
  | 84, 32 => [32,33,34,35,40,41,42,43]
  | 56, 1 => [1,3,5,7,65,67,69,71]
  | 56, 2 => [2,3,6,7,66,67,70,71]
  | 56, 4 => [4,5,6,7,68,69,70,71]
  | 56, 64 => [64,65,66,67,68,69,70,71]
  | _, _ => []

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma every_option : ∀ c ∈ cells, ∀ z : M, hit c z = true → z ∈ options c := by
  have checked : cells.all (fun c => decide (∀ z : M, hit c z = true → z ∈ options c)) = true := by
    decide +kernel
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp checked c hc)

lemma member_head {xs : List α} {c : α} (h : xs.head? = some c) : c ∈ xs := by
  obtain ⟨tail,rfl⟩ := List.head?_eq_some_iff.mp h
  exact List.mem_cons_self

def remaining (chosen : List M) := cells.filter fun c => !(chosen.any (hit c))

def solve : Nat → List M → Bool
  | fuel, chosen =>
    let wanted := chosen.map key
    if 9 < chosen.length + (unseen seeds wanted).length then false else
      match (remaining chosen).head? with
      | none => weCan wanted (9-chosen.length) seeds
      | some c => match fuel with
        | 0 => false
        | k+1 => (options c).any fun z => solve k (z :: chosen)

lemma solve_ok (tail blocks : List M) (run : Builds seeds tail)
    (bound : tail.length + blocks.length ≤ 9)
    (attain : ∀ z ∈ blocks, key z ∈ seeds ∨ key z ∈ tail)
    (cover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true)
    (fuel : Nat) (chosen : List M) (nd : chosen.Nodup)
    (sub : ∀ z ∈ chosen, z ∈ blocks) (enough : blocks.length ≤ fuel + chosen.length) :
    solve fuel chosen = true := by
  have size_of_chosen (ys : List M) (distinct : ys.Nodup) (included : ∀ z ∈ ys, z ∈ blocks) :
      ys.length ≤ blocks.length := by
    rw [← List.toFinset_card_of_nodup distinct]
    have subset : ys.toFinset ⊆ blocks.toFinset := by
      intro z hz; exact List.mem_toFinset.mpr (included _ (List.mem_toFinset.mp hz))
    exact (Finset.card_le_card subset).trans (List.toFinset_card_le _)
  have keys_of_chosen (ys : List M) (included : ∀ z ∈ ys, z ∈ blocks) :
      ∀ a ∈ ys.map key, a ∈ seeds ∨ a ∈ tail := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact attain _ (included _ hz)
  have cut (ys : List M) (distinct : ys.Nodup) (included : ∀ z ∈ ys, z ∈ blocks) :
      ¬ 9 < ys.length + (unseen seeds (ys.map key)).length := by
    have := size_of_chosen ys distinct included
    have := count_unseen (keys_of_chosen ys included)
    omega
  have done (ys : List M) (distinct : ys.Nodup) (included : ∀ z ∈ ys, z ∈ blocks) :
      weCan (ys.map key) (9-ys.length) seeds = true := by
    have := size_of_chosen ys distinct included
    exact weCan_ok_aux _ run (by omega) (keys_of_chosen ys included)
  have uncovered {ys : List M} {c} (hc : (remaining ys).head? = some c) :
      ∃ z ∈ blocks, hit c z = true ∧ z ∉ ys := by
    obtain ⟨hc1,hc2⟩ := List.mem_filter.mp (member_head hc)
    obtain ⟨z,hz,yes⟩ := cover _ hc1
    refine ⟨z,hz,yes,fun zz => ?_⟩
    have on : ys.any (hit c) = true := List.any_eq_true.mpr ⟨z,zz,yes⟩
    simp [on] at hc2
  induction fuel generalizing chosen with
  | zero =>
    rw [solve, if_neg (cut _ nd sub)]
    split
    · exact done _ nd sub
    · rename_i c hc
      obtain ⟨z,hz,yes,nz⟩ := uncovered hc
      have distinct := List.nodup_cons.mpr ⟨nz,nd⟩
      have big := size_of_chosen (z :: chosen) distinct (by
        intro x hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hz
        · exact sub _ hm)
      simp only [List.length_cons] at big
      omega
  | succ k ih =>
    rw [solve, if_neg (cut _ nd sub)]
    split
    · exact done _ nd sub
    · rename_i c hc
      obtain ⟨z,hz,yes,nz⟩ := uncovered hc
      apply List.any_eq_true.mpr
      refine ⟨z, every_option c (List.mem_filter.mp (member_head hc)).1 z yes, ?_⟩
      apply ih (z :: chosen) (List.nodup_cons.mpr ⟨nz,nd⟩)
      · intro x hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hz
        · exact sub _ hm
      · simp only [List.length_cons]
        omega

end CoverCheck

namespace Probes
open CoverCheck

abbrev Term := Fin 4
abbrev Row := Fin 9
abbrev V := Row → Fin 5 → Bool

def pick (t : Term) := t.succ
def active (v : V) : Finset Term := Finset.univ.filter fun t => v 7 (pick t)
def pack {n : Nat} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)
lemma pack_bit {n : Nat} (f : Fin n → Bool) (i : Fin n) : (pack f).getLsbD i.val = f i := by
  simp only [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt] <;> simp
def regular (r : Fin 7) : Row := ⟨r.val, by omega⟩
def mask (v : V) : M := pack (fun i => v (regular i) 0)
def roots : List (Finset Term) := (List.finRange 4).map fun t => {t}
def joins (xs : List (Finset Term)) : List (Finset Term) :=
  xs.flatMap fun a => xs.map fun b => a ∪ b
def Joined : List (Finset Term) → List (Finset Term) → Prop
  | _, [] => True
  | xs, a :: tail => a ∈ joins xs ∧ Joined (a :: xs) tail
def twoOK : Bool :=
  (joins roots).all fun a =>
    (joins (a :: roots)).all fun b => !((b :: a :: roots).contains Finset.univ)
lemma two_checked : twoOK = true := by decide +kernel
lemma three_joins {js : List (Finset Term)} (h : Joined roots js)
    (mem : Finset.univ ∈ js.reverse ++ roots) : 3 ≤ js.length := by
  by_contra! small
  rcases js with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · exact (show Finset.univ ∉ roots by decide) (by simpa using mem)
  · obtain ⟨ha,_⟩ := h
    exact (show ∀ a ∈ joins roots, Finset.univ ∉ a :: roots by decide) a ha (by simpa using mem)
  · obtain ⟨ha,hb,_⟩ := h
    have checked := List.all_eq_true.mp (List.all_eq_true.mp two_checked a ha) b hb
    have yes : (b :: a :: roots).contains Finset.univ = true :=
      List.contains_iff_mem.mpr (by simpa using mem)
    change (!(List.contains (b :: a :: roots) Finset.univ)) = true at checked
    rw [yes] at checked
    contradiction
  · simp only [List.length_cons] at small
    omega

def Signed (ps : List M) (v : V) : Prop := key (mask v) ∈ ps.reverse ++ seeds

def Safe (ps bs : List M) (js : List (Finset Term)) (add : Bool) (v : V) : Prop :=
  (∀ t : Term, t ∉ active v → ∀ r : Row, v r (pick t) = v r 0) ∧
  (active v = ∅ → Signed ps v) ∧
  (active v ≠ ∅ → active v ∈ js.reverse ++ roots) ∧
  (active v ≠ ∅ → add = false → v 8 0 = false) ∧
  (∀ t ∈ active v, ∃ qs : List M, (∀ z ∈ qs, z ∈ bs) ∧ ∀ r : Fin 7,
    v (regular r) (pick t) =
      (v (regular r) 0 || !(qs.any fun z => z.getLsbD r.val)))

lemma safe_mono {ps bs js add v ps' bs' js' add'} (h : Safe ps bs js add v)
    (p : ∀ x ∈ ps, x ∈ ps') (b : ∀ x ∈ bs, x ∈ bs') (j : ∀ x ∈ js, x ∈ js')
    (a : add = true → add' = true) : Safe ps' bs' js' add' v := by
  obtain ⟨same,pure,mixed,noAdd,filters⟩ := h
  refine ⟨same,fun e => ?_,fun e => ?_,fun e h' => ?_,fun t ht => ?_⟩
  · have hp := pure e
    simp only [Signed, List.mem_append, List.mem_reverse] at hp ⊢
    exact hp.imp (p _) id
  · have hj := mixed e
    simp only [List.mem_append, List.mem_reverse] at hj ⊢
    exact hj.imp (j _) id
  · apply noAdd e
    cases he : add
    · rfl
    · have ah := a he
      simp [h'] at ah
  · obtain ⟨qs,hs,hq⟩ := filters t ht
    exact ⟨qs, fun z hz => b _ (hs z hz), hq⟩

def actOr (x y : V) : V := fun r t => x r t || y r t
def actFilter (x y : V) : V := fun r t => x r t && ! y r t

lemma mixed_join {ps bs js d x y}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y ≠ ∅)
    (dis : Disjoint (active x) (active y)) :
    let z := actOr x y
    Safe ps bs (js ++ [active z]) d z := by
  let z := actOr x y
  have cap : active z = active x ∪ active y := by ext t; simp [active,z,actOr]
  have nz : active z ≠ ∅ := by rw [cap]; simp [nx]
  refine ⟨?_,fun e => (nz e).elim,fun _ => by simp,fun _ no => ?_,?_⟩
  · intro t ht r
    change t ∉ active z at ht
    rw [cap, Finset.mem_union, not_or] at ht
    simp [actOr,hx.1 _ ht.1 r,hy.1 _ ht.2 r]
  · simp [actOr, hx.2.2.2.1 nx no, hy.2.2.2.1 ny no]
  · intro t ht
    change t ∈ active z at ht
    rw [cap, Finset.mem_union] at ht
    rcases ht with ht | ht
    · obtain ⟨qs,ss,eq⟩ := hx.2.2.2.2 t ht
      have absent : t ∉ active y := Finset.disjoint_left.mp dis ht
      refine ⟨qs,ss, fun r => ?_⟩
      simp only [actOr,eq r,hy.1 _ absent _]
      ac_rfl
    · obtain ⟨qs,ss,eq⟩ := hy.2.2.2.2 t ht
      have absent : t ∉ active x := fun h => Finset.disjoint_left.mp dis h ht
      refine ⟨qs,ss, fun r => ?_⟩
      simp only [actOr,eq r,hx.1 _ absent _]
      ac_rfl

lemma add_pure {ps bs js d x y}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y = ∅) :
    Safe ps bs js true (actOr x y) := by
  have cap : active (actOr x y) = active x := by
    ext t; have := Finset.notMem_empty t; rw [← ny] at this
    simp_all [active,actOr]
  refine ⟨?_,fun e => (nx (cap.symm.trans e)).elim,
    fun _ => cap ▸ hx.2.2.1 nx, fun _ no => by contradiction,?_⟩
  · intro t ht r
    rw [cap] at ht
    simp [actOr,hx.1 _ ht r,hy.1 t (by simp [ny]) r]
  · intro t ht
    rw [cap] at ht
    obtain ⟨qs,ss,eq⟩ := hx.2.2.2.2 t ht
    refine ⟨qs,ss, fun r => ?_⟩
    simp only [actOr,eq r,hy.1 t (by simp [ny]) _]
    ac_rfl

lemma filter_pure {ps bs js d x y}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y = ∅) :
    Safe ps (mask y :: bs) js d (actFilter x y) := by
  have cap : active (actFilter x y) = active x := by
    ext t; have := Finset.notMem_empty t; rw [← ny] at this
    simp_all [active,actFilter]
  refine ⟨?_,fun e => (nx (cap.symm.trans e)).elim,
    fun _ => cap ▸ hx.2.2.1 nx, fun _ no => ?_,?_⟩
  · intro t ht r
    rw [cap] at ht
    simp [actFilter,hx.1 _ ht r,hy.1 t (by simp [ny]) r]
  · simp [actFilter,hx.2.2.2.1 nx no]
  · intro t ht
    rw [cap] at ht
    obtain ⟨qs,ss,eq⟩ := hx.2.2.2.2 t ht
    refine ⟨mask y :: qs, ?_, fun r => ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ss _ hz)
    simp only [actFilter,eq r,hy.1 t (by simp [ny]) _,List.any_cons,mask,pack_bit]
    cases x (regular r) 0 <;> cases y (regular r) 0 <;> cases qs.any (fun z => z.getLsbD r.val) <;> rfl

end Probes

namespace Probes
open CoverCheck

def negVal (a : Bool) (b : Bool) := xor a b
def gateB (o a b : Bool) := if o then a || b else a && b
def bin (o sa sb a b : Bool) := xor (gateB o (xor a sa) (xor b sb)) (gateB o sa sb)
def combine (o sa sb : Bool) (x y : V) : V := fun r t => bin o sa sb (x r t) (y r t)
lemma bin_cases : ∀ o sa sb : Bool,
    (∀ a b, bin o sa sb a b = (a || b)) ∨
    (∀ a b, bin o sa sb a b = (a && b)) ∨
    (∀ a b, bin o sa sb a b = (a && !b)) ∨
    (∀ a b, bin o sa sb a b = (b && !a)) := by decide
lemma bin_sym (o sa sb a b : Bool) : bin o sa sb a b = bin o sb sa b a := by
  cases o <;> cases sa <;> cases sb <;> cases a <;> cases b <;> rfl
lemma bin_two (o sa sb : Bool) (h1 : bin o sa sb true false = true)
    (h2 : bin o sa sb false true = true) : ∀ a b, bin o sa sb a b = (a || b) := by
  exact (show ∀ o sa sb, bin o sa sb true false = true → bin o sa sb false true = true →
    ∀ a b, bin o sa sb a b = (a || b) by decide) _ _ _ h1 h2
lemma bin_one (o sa sb : Bool) (h1 : bin o sa sb true false = true) :
    (∀ a b, bin o sa sb a b = (a || b)) ∨ (∀ a b, bin o sa sb a b = (a && !b)) := by
  exact (show ∀ o sa sb, bin o sa sb true false = true →
    (∀ a b, bin o sa sb a b = (a || b)) ∨ (∀ a b, bin o sa sb a b = (a && !b)) by decide) _ _ _ h1

lemma both_lits {u : M} {xs : List M} (h : key u ∈ xs) :
    u ∈ lits xs ∧ ~~~u ∈ lits xs := by
  have put (v : M) (hv : v ∈ xs) : v ∈ lits xs ∧ ~~~v ∈ lits xs :=
    ⟨List.mem_append_left _ hv, List.mem_append_right _ (List.mem_map.mpr ⟨v,hv,rfl⟩)⟩
  unfold key at h
  split at h
  · exact put _ h
  · obtain ⟨ht,hu⟩ := put _ h
    exact ⟨by simpa using hu,ht⟩

lemma pack_op {f : Bool → Bool → Bool} {op : M → M → M}
    (point : ∀ a b : M, ∀ i : Fin 7, (op a b).getLsbD i.val = f (a.getLsbD i.val) (b.getLsbD i.val))
    (x y : V) : mask (fun r t => f (x r t) (y r t)) = op (mask x) (mask y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 7 := ⟨i,hi⟩
  change (pack _).getLsbD r.val = (op _ _).getLsbD r.val
  simp only [point _ _ r, mask, pack_bit]

lemma bin_product {xs : List M} {x y : V} (o sa sb : Bool)
    (hx : key (mask x) ∈ xs) (hy : key (mask y) ∈ xs) :
    key (mask (combine o sa sb x y)) ∈ products xs := by
  obtain ⟨x1,x0⟩ := both_lits hx
  obtain ⟨y1,y0⟩ := both_lits hy
  have prod (a b : M) (ha : a ∈ lits xs) (hb : b ∈ lits xs) :
      key (a &&& b) ∈ products xs := by
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
  rcases bin_cases o sa sb with h | h | h | h
  · have op : mask (combine o sa sb x y) = mask x ||| mask y := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := (· || ·)) (op := (· ||| ·)) (by simp) x y
    rw [op, ← key_flip, BitVec.not_or]
    exact prod _ _ x0 y0
  · have op : mask (combine o sa sb x y) = mask x &&& mask y := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := (· && ·)) (op := (· &&& ·)) (by simp) x y
    rw [op]
    exact prod _ _ x1 y1
  · have op : mask (combine o sa sb x y) = mask x &&& ~~~mask y := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := fun a b => a && !b)
        (op := fun a b => a &&& ~~~b) (by simp) x y
    rw [op]
    exact prod _ _ x1 y0
  · have op : mask (combine o sa sb x y) = mask y &&& ~~~mask x := by
      unfold combine
      simp_rw [h]
      exact pack_op (f := fun a b => b && !a)
        (op := fun a b => b &&& ~~~a) (by simp) x y
    rw [op]
    exact prod _ _ y1 x0

lemma builds_snoc {xs tail : List M} (h : Builds xs tail) (a : M)
    (ha : a ∈ products (tail.reverse ++ xs)) : Builds xs (tail ++ [a]) := by
  induction tail generalizing xs with
  | nil => exact ⟨by simpa using ha, trivial⟩
  | cons b tail ih => exact ⟨h.1, ih h.2 (by simpa using ha)⟩
lemma joined_snoc {xs tail : List (Finset Term)} (h : Joined xs tail) (a : Finset Term)
    (ha : a ∈ joins (tail.reverse ++ xs)) : Joined xs (tail ++ [a]) := by
  induction tail generalizing xs with
  | nil => exact ⟨by simpa using ha, trivial⟩
  | cons b tail ih => exact ⟨h.1, ih h.2 (by simpa using ha)⟩

abbrev Ledger := List M × List M × List (Finset Term) × Bool
def AllSafe (l : Ledger) (v : V) := Safe l.1 l.2.1 l.2.2.1 l.2.2.2 v
def Valid (l : Ledger) (n : Nat) : Prop :=
  Builds seeds l.1 ∧ Joined roots l.2.2.1 ∧
  (∀ z ∈ l.2.1, key z ∈ l.1.reverse ++ seeds) ∧
  l.1.length + l.2.1.length + l.2.2.1.length + l.2.2.2.toNat ≤ n

def StepOK (l : Ledger) (n : Nat) (z : V) : Prop :=
  ∃ l' : Ledger, Valid l' (n+1) ∧ AllSafe l' z ∧ ∀ v, AllSafe l v → AllSafe l' v

lemma pure_step {ps bs js d n} (valid : Valid (ps,bs,js,d) n) {x y : V}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x = ∅) (ny : active y = ∅) (o sa sb : Bool)
    (nz : active (combine o sa sb x y) = ∅) :
    StepOK (ps,bs,js,d) n (combine o sa sb x y) := by
  let z := combine o sa sb x y
  let m := key (mask z)
  have prod := bin_product o sa sb (hx.2.1 nx) (hy.2.1 ny)
  obtain ⟨build,joined,attain,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  refine ⟨(ps ++ [m],bs,js,d), ⟨builds_snoc build m prod,joined,?_,?_⟩,?_,?_⟩
  · intro a ha
    simpa [List.mem_append, or_assoc] using (show key a = m ∨ _ from Or.inr (attain a ha))
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Prod.fst, Prod.snd]
    omega
  · refine ⟨fun t _ r => ?_,fun _ => ?_,fun hn => (hn nz).elim,fun hn => (hn nz).elim,
      fun t ht => False.elim (by rw [nz] at ht; simpa using ht)⟩
    · simp [combine, hx.1 t (by simp [nx]) r, hy.1 t (by simp [ny]) r]
    · simp [Signed,m,z]
  · intro v h
    exact safe_mono h (fun _ ht => List.mem_append_left _ ht) (fun _ ht => ht) (fun _ ht => ht) id

lemma join_step {ps bs js d n} (valid : Valid (ps,bs,js,d) n) {x y : V}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y ≠ ∅) (dis : Disjoint (active x) (active y)) :
    StepOK (ps,bs,js,d) n (actOr x y) := by
  have cap : active (actOr x y) = active x ∪ active y := by ext t; simp [active,actOr]
  obtain ⟨build,joined,attain,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  refine ⟨(ps,bs,js ++ [active (actOr x y)],d), ⟨build,joined_snoc joined _ ?_,attain,?_⟩,
    mixed_join hx hy nx ny dis,?_⟩
  · rw [cap]
    exact List.mem_flatMap.mpr ⟨_,hx.2.2.1 nx,List.mem_map.mpr ⟨_,hy.2.2.1 ny,rfl⟩⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Prod.fst, Prod.snd]
    omega
  · intro v h
    exact safe_mono h (fun _ ht => ht) (fun _ ht => ht) (fun _ ht => List.mem_append_left _ ht) id

lemma unary_step {ps bs js d n} (valid : Valid (ps,bs,js,d) n) {x y : V}
    (hx : Safe ps bs js d x) (hy : Safe ps bs js d y)
    (nx : active x ≠ ∅) (ny : active y = ∅) :
    StepOK (ps,bs,js,d) n (actOr x y) ∧ StepOK (ps,bs,js,d) n (actFilter x y) := by
  obtain ⟨build,joined,attain,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  constructor
  · refine ⟨(ps,bs,js,true), ⟨build,joined,attain,?_⟩,add_pure hx hy nx ny,?_⟩
    · change ps.length + bs.length + js.length + 1 ≤ n + 1
      omega
    · intro v h
      exact safe_mono h (fun _ ht => ht) (fun _ ht => ht) (fun _ ht => ht) (fun _ => rfl)
  · refine ⟨(ps,mask y :: bs,js,d), ⟨build,joined,?_,?_⟩,filter_pure hx hy nx ny,?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy.2.1 ny
      · exact attain z hz
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.succ_le_succ cost
    · intro v h
      exact safe_mono h (fun _ ht => ht) (fun _ ht => List.mem_cons_of_mem _ ht) (fun _ ht => ht) id

lemma one_step {l n} (valid : Valid l n) {x y : V} (hx : AllSafe l x) (hy : AllSafe l y)
    (o sa sb : Bool) (nx : active x ≠ ∅) (ny : active y = ∅)
    (cap : active (combine o sa sb x y) = active x ∪ active y) :
    StepOK l n (combine o sa sb x y) := by
  obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr nx
  have hyt : t ∉ active y := by simp [ny]
  have hzt : t ∈ active (combine o sa sb x y) := cap ▸ Finset.mem_union_left _ ht
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at ht hyt hzt
  have good : bin o sa sb true false = true := by simpa [combine,ht,hyt] using hzt
  rcases bin_one o sa sb good with h | h
  · have eq : combine o sa sb x y = actOr x y := by funext r t; exact h _ _
    rw [eq]
    exact (unary_step valid hx hy nx ny).1
  · have eq : combine o sa sb x y = actFilter x y := by funext r t; exact h _ _
    rw [eq]
    exact (unary_step valid hx hy nx ny).2

lemma binary_step {l n} (valid : Valid l n) {x y : V} (hx : AllSafe l x) (hy : AllSafe l y)
    (o sa sb : Bool) (dis : Disjoint (active x) (active y))
    (cap : active (combine o sa sb x y) = active x ∪ active y) :
    StepOK l n (combine o sa sb x y) := by
  by_cases nx : active x = ∅
  · by_cases ny : active y = ∅
    · exact pure_step valid hx hy nx ny o sa sb (by simpa [nx,ny] using cap)
    · have eq : combine o sa sb x y = combine o sb sa y x := by funext r t; exact bin_sym .. 
      rw [eq] at cap ⊢
      exact one_step valid hy hx o sb sa ny nx (cap.trans (Finset.union_comm ..))
  · by_cases ny : active y = ∅
    · exact one_step valid hx hy o sa sb nx ny cap
    obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr nx
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr ny
    have hyt := Finset.disjoint_left.mp dis ht
    have hxu := Finset.disjoint_right.mp dis hu
    have hzt : t ∈ active (combine o sa sb x y) := cap ▸ Finset.mem_union_left _ ht
    have hzu : u ∈ active (combine o sa sb x y) := cap ▸ Finset.mem_union_right _ hu
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at ht hu hyt hxu hzt hzu
    have h := bin_two o sa sb (by simpa [combine,ht,hyt] using hzt) (by simpa [combine,hu,hxu] using hzu)
    have eq : combine o sa sb x y = actOr x y := by funext r t; exact h _ _
    rw [eq]
    exact join_step valid hx hy nx ny dis

end Probes

namespace Probes
open CoverCheck PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenNine
open PetersenScratch (occurrences)
open PetersenCutFormula (wireFormula)

def perm (h : Fin 3) : Vertex → Vertex :=
  [![0,1,2,3,4,5,6,7,8], ![0,5,8,3,4,1,7,6,2], ![1,0,5,8,6,2,4,7,3]].getD h.val id

def term (h : Fin 3) (t : Term) := perm h (![1,4,7,8] t)
def fixture (h : Fin 3) (r : Row) (u : Fin 5) (i : Vertex) : Bool :=
  let bits : Nat := ([0,1,4,8,32,64,5,69,33].getD r.val 0) ||| ([0,2,16,128,256].getD u.val 0)
  (List.finRange 9).any fun v => (perm h v == i) && bits.testBit v.val

def inp (h : Fin 3) (i : Vertex) : V := fun r u => xor (fixture h r u i) (fixture h 7 0 i)
def aim (h : Fin 3) : V := fun r u => xor (petersenF (fixture h r u)) (petersenF (fixture h 7 0))
def layoutOK (h : Fin 3) (s : Finset Vertex) : Prop := ∀ t, term h t ∈ s
lemma layout_exists (s : Finset Vertex) (hs : s ∈ cuts) : ∃ h, layoutOK h s := by
  simp only [cuts,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl <;> unfold layoutOK <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fixture_delta : ∀ h t i, (inp h i 7 (pick t)).toNat = if i = term h t then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma initial_safe (h : Fin 3) (i : Vertex) : AllSafe ([],[],[],false) (inp h i) := by
  let x := inp h i
  have samples : ∀ h i,
      (∀ t, t ∉ active (inp h i) → ∀ r, inp h i r (pick t) = inp h i r 0) ∧
      (active (inp h i) = ∅ → Signed [] (inp h i)) ∧
      (active (inp h i) ≠ ∅ → active (inp h i) ∈ roots ∧ inp h i 8 0 = false) ∧
      (∀ t ∈ active (inp h i), ∀ r : Fin 7, inp h i (regular r) (pick t) = true) := by
    unfold Signed
    decide +kernel
  obtain ⟨a,b,c,d⟩ := samples h i
  exact ⟨a,b,fun e => (c e).1,fun e _ => (c e).2,fun t ht =>
    ⟨[],by simp,fun r => by simp [d _ ht r]⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aim_samples : ∀ h, active (aim h) = Finset.univ ∧ aim h 8 0 = true ∧
    (∀ r : Fin 7, aim h (regular r) 0 = false) ∧
    (∀ t : Term, ∀ r : Fin 7, aim h (regular r) (pick t) = (profiles.getD t.val 0).getLsbD r.val) := by
  decide +kernel

def sense (gs : List Gate) (h : Fin 3) (w : Nat) : V := fun r u =>
  xor (vl gs (fixture h r u) w) (vl gs (fixture h 7 0) w)

lemma sense_input (gs : List Gate) (h : Fin 3) (w : Nat) (hw : w < 9) :
    sense gs h w = inp h ⟨w,hw⟩ := by
  funext r u; simp [sense,inp,vl_input _ _ _ hw]

lemma sense_not {gs : List Gate} (clean : CleanL 9 gs) (h : Fin 3)
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not) (args : g.inputs = [a]) :
    sense gs h (9+p) = sense gs h a := by
  funext r u
  simp only [sense,vl_gate gs clean _ _ g hg, op,args,List.map_cons,List.map_nil,GateOp.eval,List.head?_cons,Option.getD_some]
  cases vl gs (fixture h r u) a <;> cases vl gs (fixture h 7 0) a <;> rfl

lemma sense_bin {gs : List Gate} (clean : CleanL 9 gs) (h : Fin 3)
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and ∨ g.op = .or)
    (args : g.inputs = [a,b]) :
    ∃ o sa sb, sense gs h (9+p) = combine o sa sb (sense gs h a) (sense gs h b) := by
  let sa := vl gs (fixture h 7 0) a
  let sb := vl gs (fixture h 7 0) b
  rcases op with e | e
  · refine ⟨false,sa,sb,?_⟩
    funext r u
    simp only [sense,combine,bin,gateB,sa,sb,vl_gate gs clean _ _ g hg,e,args,List.map_cons,List.map_nil,GateOp.eval]
    cases vl gs (fixture h r u) a <;> cases vl gs (fixture h r u) b <;>
      cases vl gs (fixture h 7 0) a <;> cases vl gs (fixture h 7 0) b <;> rfl
  · refine ⟨true,sa,sb,?_⟩
    funext r u
    simp only [sense,combine,bin,gateB,sa,sb,vl_gate gs clean _ _ g hg,e,args,List.map_cons,List.map_nil,GateOp.eval]
    cases vl gs (fixture h r u) a <;> cases vl gs (fixture h r u) b <;>
      cases vl gs (fixture h 7 0) a <;> cases vl gs (fixture h 7 0) b <;> rfl

lemma local_flip (o sa sb a b : Bool) :
    (bin o sa sb a b).toNat ≤ a.toNat + b.toNat := by
  exact (show ∀ o sa sb a b : Bool, (bin o sa sb a b).toNat ≤ a.toNat + b.toNat by decide) o sa sb a b 

lemma sum_le {l : List Nat} {f g : Nat → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma sum_lt {l : List Nat} {f g : Nat → Nat} {a : Nat} (ha : a ∈ l)
    (h : ∀ b ∈ l, f b ≤ g b) (strict : f a < g a) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have tail (x) (hx : x ∈ l) := h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | later
    · exact Nat.add_lt_add_of_lt_of_le strict (sum_le tail)
    · exact Nat.add_lt_add_of_le_of_lt (h _ List.mem_cons_self) (ih later tail)

lemma exact_occ {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (h : Fin 3) (t : Term) (single : occurrences (term h t) (wireFormula 0 gs o) ≤ 1) :
    ∀ w, w < 9 + gs.length →
      (sense gs h w 7 (pick t)).toNat = occurrences (term h t) (wireFormula 0 gs w) := by
  let f (w : Nat) := (sense gs h w 7 (pick t)).toNat
  let g (w : Nat) := occurrences (term h t) (wireFormula 0 gs w)
  have step {p : Nat} {G : Gate} (hg : gs[p]? = some G) : f (9+p) ≤ (G.inputs.map f).sum := by
    rcases L.hcl p G hg with ⟨op,a,_,args⟩ | ⟨op,a,b,_,_,args⟩
    · simp [f,sense_not L.hcl h hg op args, args]
    · obtain ⟨op',sa,sb,sz⟩ := sense_bin L.hcl h hg op args
      simpa [f,sz,args,combine] using local_flip op' sa sb
        (sense gs h a 7 (pick t)) (sense gs h b 7 (pick t))
  have count {p : Nat} {G : Gate} (hg : gs[p]? = some G) : g (9+p) = (G.inputs.map g).sum :=
    PetersenCutFormula.wireFormula_count_gate 0 L.hcl _ hg
  have upper (w : Nat) (hw : w < 9 + gs.length) : f w ≤ g w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases input : w < 9
      · change (sense gs h w 7 (pick t)).toNat ≤ _
        rw [sense_input _ _ _ input,fixture_delta]
        exact le_of_eq (PetersenCutFormula.wireFormula_count_input 0 gs _ ⟨w,input⟩).symm
      · obtain ⟨p,rfl⟩ : ∃ p, w = 9+p := ⟨w-9,by omega⟩
        have hp : p < gs.length := by omega
        have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
        rw [count hg]
        exact (step hg).trans (sum_le fun a ha => ih a ((L.hcl _ _ hg).lt _ ha) (by have := (L.hcl _ _ hg).lt _ ha; omega))
  have output : sense gs h o = aim h := by funext r u; simp [sense,aim,L.hev]
  have onset : t ∈ active (aim h) := by simp [(aim_samples h).1]
  have doneAt : f o = g o := by
    have on : aim h 7 (pick t) = true := (Finset.mem_filter.mp onset).2
    have yes : f o = 1 := by simp [f,output,on]
    have := upper o (least_petersen_output_valid L)
    change g o ≤ 1 at single
    omega
  have live := least_read_edge_live L petersen_nonconstant petersen_depends petersen_restrict_nonconstant
    (least_petersen_output_valid L)
  intro w hw
  change f w = g w
  induction rank : 9 + gs.length - w using Nat.strong_induction_on generalizing w with
  | ind m ih =>
    apply le_antisymm (upper w hw)
    by_contra! lower
    by_cases out : w = o
    · subst w; omega
    · let wire : Fin (9 + gs.length) := ⟨w,hw⟩
      obtain ⟨v,p,G,hg,eq,inside⟩ := live wire (fun e => out (congrArg Fin.val e))
      have before := (L.hcl p G hg).lt _ inside
      change w < 9+p at before
      have endBound : 9+p < 9+gs.length := by have := v.isLt; omega
      have next := ih (9+gs.length-(9+p)) (by omega) (9+p) endBound rfl
      have strict := sum_lt inside (fun a ha => upper a (by have := (L.hcl _ _ hg).lt _ ha; omega)) lower
      have := step hg
      rw [count hg] at next
      omega

lemma binary_caps {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (h : Fin 3) (single : ∀ t, occurrences (term h t) (wireFormula 0 gs o) ≤ 1)
    {p a b : Nat} {G : Gate} (hg : gs[p]? = some G) (args : G.inputs = [a,b]) :
    Disjoint (active (sense gs h a)) (active (sense gs h b)) ∧
      active (sense gs h (9+p)) = active (sense gs h a) ∪ active (sense gs h b) := by
  have endBound : 9+p < 9+gs.length := by have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have ha : a < 9+p := (L.hcl p G hg).lt a (by simp [args])
  have hb : b < 9+p := (L.hcl p G hg).lt b (by simp [args])
  have cnt (t : Term) :
      (sense gs h (9+p) 7 (pick t)).toNat =
      (sense gs h a 7 (pick t)).toNat + (sense gs h b 7 (pick t)).toNat := by
    have matched := exact_occ L h t (single t)
    rw [matched _ endBound, matched _ (ha.trans endBound), matched _ (hb.trans endBound)]
    simpa [args] using PetersenCutFormula.wireFormula_count_gate 0 L.hcl (term h t) hg
  constructor
  · apply Finset.disjoint_left.mpr
    intro t ht hu
    have eq := cnt t
    simp only [active,Finset.mem_filter,Finset.mem_univ,true_and] at ht hu
    rw [ht,hu] at eq
    cases e : sense gs h (9+p) 7 (pick t) <;> simp [e] at eq
  · ext t
    have eq := cnt t
    simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    cases ea : sense gs h a 7 (pick t) <;> cases eb : sense gs h b 7 (pick t) <;>
      cases ec : sense gs h (9+p) 7 (pick t) <;> simp_all

lemma ledger_for_circuit {gs : List Gate} {o : Nat} (L : Least 9 petersenF gs o)
    (h : Fin 3) (single : ∀ t, occurrences (term h t) (wireFormula 0 gs o) ≤ 1) :
    ∃ l, Valid l (nonNotCount gs) ∧ AllSafe l (aim h) := by
  have pref (p : Nat) (hp : p ≤ gs.length) : ∃ l, Valid l (nonNotCount (gs.take p)) ∧
      ∀ w < 9+p, AllSafe l (sense gs h w) := by
    induction p with
    | zero =>
      refine ⟨([],[],[],false), ⟨trivial,trivial,by simp,by simp [nonNotCount]⟩,?_⟩
      intro w hw
      rw [sense_input _ _ _ (by omega)]
      exact initial_safe h _
    | succ p ih =>
      have before : p < gs.length := by omega
      have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem before
      obtain ⟨l, valid, safe⟩ := ih (by omega)
      have takeEq : gs.take (p+1) = gs.take p ++ [gs[p]] := List.take_succ_eq_append_getElem before
      have size : nonNotCount (gs.take (p+1)) = nonNotCount (gs.take p) +
          (if isNotGate gs[p].op then 0 else 1) := by
        rw [takeEq]
        unfold nonNotCount
        rw [List.countP_append]
        congr 1
        cases hb : isNotGate gs[p].op <;> simp [hb]
      rcases L.hcl p gs[p] hg with ⟨op,a,ha,args⟩ | ⟨op,a,b,ha,hb,args⟩
      · refine ⟨l,?_,?_⟩
        · rw [size, op]
          simpa [isNotGate] using valid
        · intro w hw
          by_cases old : w < 9+p
          · exact safe w old
          · have eq : w = 9+p := by omega
            rw [eq,sense_not L.hcl h hg op args]
            exact safe a ha
      · obtain ⟨oo,sa,sb,sz⟩ := sense_bin L.hcl h hg op args
        obtain ⟨dis,cap⟩ := binary_caps L h single hg args
        rw [sz] at cap
        obtain ⟨l',valid',safe',keep⟩ := binary_step valid (safe _ ha) (safe _ hb) oo sa sb dis cap
        refine ⟨l',?_,?_⟩
        · rcases op with op | op <;> rw [size, op] <;> simpa [isNotGate] using valid'
        · intro w hw
          by_cases old : w < 9+p
          · exact keep _ (safe w old)
          · have eq : w = 9+p := by omega
            rwa [eq,sz]
  obtain ⟨l,valid,all⟩ := pref gs.length le_rfl
  refine ⟨l,by simpa using valid,?_⟩
  have output : sense gs h o = aim h := by funext r u; simp [sense,aim,L.hev]
  rw [←output]
  exact all _ (least_petersen_output_valid L)

end Probes

namespace Probes
open CoverCheck

set_option maxRecDepth 20000 in
lemma cell_witness : ∀ c ∈ cells, ∃ t : Term, ∃ r : Fin 7,
    c = (profiles.getD t.val 0, (1 : M) <<< r.val) ∧ c.1.getLsbD r.val = false := by
  have checked : cells.all (fun c => decide (∃ t : Term, ∃ r : Fin 7,
    c = (profiles.getD t.val 0, (1 : M) <<< r.val) ∧ c.1.getLsbD r.val = false)) = true := by
    decide +kernel
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp checked c hc)

lemma hit_spec : ∀ a z : M, ∀ r : Fin 7, z.getLsbD r.val = true →
    (∀ i : Fin 7, a.getLsbD i.val = true → z.getLsbD i.val = false) →
    hit (a,(1 : M) <<< r.val) z = true := by
  intro a z r yes good
  have zero : a &&& z = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := good ⟨i,hi⟩
    cases h : a.getLsbD i <;> simp_all
  unfold hit
  simp only [zero,beq_self_eq_true,true_and]
  have law : ∀ v : M, ∀ j : Fin 7, v.getLsbD j.val = true →
      (((1 : M) <<< j.val) &&& v != 0) = true := by decide +kernel
  exact law z r yes

lemma output_cover {ps bs js d} {h : Fin 3} (safe : Safe ps bs js d (aim h)) :
    ∀ c ∈ cells, ∃ z ∈ bs, hit c z = true := by
  intro c hc
  obtain ⟨t,r,eq,neg⟩ := cell_witness c hc
  obtain ⟨all,on,baseline,probe⟩ := aim_samples h
  obtain ⟨qs,inside,values⟩ := safe.2.2.2.2 t (by simp [all])
  have required (j : Fin 7) :
      (profiles.getD t.val 0).getLsbD j.val = !(qs.any fun z => z.getLsbD j.val) := by
    simpa [baseline j, probe t j] using values j
  rw [eq] at neg ⊢
  have has : (qs.any fun z => z.getLsbD r.val) = true := by
    have e := required r
    simp_all
  obtain ⟨z,zIn,yes⟩ := List.any_eq_true.mp has
  refine ⟨z,inside z zIn,hit_spec _ _ _ yes ?_⟩
  intro j one
  have eq := required j
  by_contra! nz
  have nz' : z.getLsbD j.val = true := Bool.ne_false_iff.mp nz
  have hit' := List.any_eq_true.mpr (show ∃ x ∈ qs, x.getLsbD j.val = true from ⟨z,zIn,nz'⟩)
  rw [one, hit'] at eq
  contradiction

set_option maxHeartbeats 2000000 in
lemma no_ledger {l n} {h : Fin 3} (bound : n ≤ 13) (valid : Valid l n)
    (safe : AllSafe l (aim h)) : solve 9 [] ≠ false := by
  obtain ⟨ps,bs,js,d⟩ := l
  obtain ⟨build,joined,outputs,cost⟩ := valid
  change ps.length + bs.length + js.length + d.toNat ≤ n at cost
  change Builds seeds ps at build
  change Joined roots js at joined
  change ∀ z ∈ bs, key z ∈ ps.reverse ++ seeds at outputs
  change Safe ps bs js d (aim h) at safe
  have nonempty : active (aim h) ≠ ∅ := by
    rw [(aim_samples h).1]
    decide
  have mem := safe.2.2.1 nonempty
  rw [(aim_samples h).1] at mem
  have jc : 3 ≤ js.length := three_joins joined mem
  have dtrue : d = true := by
    cases h' : d
    · have no := safe.2.2.2.1 nonempty h'
      simp [(aim_samples h).2.1] at no
    · rfl
  rw [dtrue] at cost
  change ps.length + bs.length + js.length + 1 ≤ n at cost
  have witness : solve 9 [] = true := solve_ok ps bs build (by omega) (by
    intro z hz
    simpa [List.mem_append,or_comm] using outputs z hz) (output_cover safe) 9 []
      (by simp) (by simp) (by simp; omega)
  intro check
  exact Bool.false_ne_true (check.symm.trans witness)

end Probes

open CircuitProof PetersenNine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace CoverCheck

lemma split_solve (k : Nat) (xs : List M) (c : M × M) (next : List M)
    (hc : (remaining xs).head? = some c) (eq : options c = next)
    (h : (next.any fun z => solve k (z :: xs)) = false) : solve (k+1) xs = false := by
  rw [solve]
  split
  · rfl
  · rw [hc]
    simpa only [eq] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_8_1 : solve 6 [16,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_8_1 : solve 6 [17,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_8_1 : solve 6 [24,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_8_1 : solve 6 [25,8,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_8_1 : solve 7 [8,1] = false := by
  apply split_solve 6 [8,1] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_8_1, reject_17_8_1, reject_24_8_1, reject_25_8_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_9_1 : solve 6 [16,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_9_1 : solve 6 [17,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_9_1 : solve 6 [24,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_9_1 : solve 6 [25,9,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_1 : solve 7 [9,1] = false := by
  apply split_solve 6 [9,1] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_9_1, reject_17_9_1, reject_24_9_1, reject_25_9_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_24_1 : solve 6 [4,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_24_1 : solve 6 [5,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_24_1 : solve 6 [20,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_24_1 : solve 6 [21,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_24_1 : solve 6 [36,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_24_1 : solve 6 [37,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_24_1 : solve 6 [52,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_24_1 : solve 6 [53,24,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_1 : solve 7 [24,1] = false := by
  apply split_solve 6 [24,1] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_24_1, reject_5_24_1, reject_20_24_1, reject_21_24_1, reject_36_24_1, reject_37_24_1, reject_52_24_1, reject_53_24_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_25_1 : solve 6 [4,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25_1 : solve 6 [5,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_25_1 : solve 6 [20,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25_1 : solve 6 [21,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_25_1 : solve 6 [36,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25_1 : solve 6 [37,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_25_1 : solve 6 [52,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25_1 : solve 6 [53,25,1] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_1 : solve 7 [25,1] = false := by
  apply split_solve 6 [25,1] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_25_1, reject_5_25_1, reject_20_25_1, reject_21_25_1, reject_36_25_1, reject_37_25_1, reject_52_25_1, reject_53_25_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1 : solve 8 [1] = false := by
  apply split_solve 7 [1] (102,8) [8,9,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_8_1, reject_9_1, reject_24_1, reject_25_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_16_9 : solve 6 [1,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_16_9 : solve 6 [5,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_16_9 : solve 6 [17,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_16_9 : solve 6 [21,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_16_9 : solve 6 [33,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_16_9 : solve 6 [37,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_16_9 : solve 6 [49,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_16_9 : solve 6 [53,16,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_9 : solve 7 [16,9] = false := by
  apply split_solve 6 [16,9] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_16_9, reject_5_16_9, reject_17_16_9, reject_21_16_9, reject_33_16_9, reject_37_16_9, reject_49_16_9, reject_53_16_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_17_9 : solve 6 [4,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_17_9 : solve 6 [5,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_17_9 : solve 6 [20,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_17_9 : solve 6 [21,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_17_9 : solve 6 [36,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_17_9 : solve 6 [37,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_17_9 : solve 6 [52,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_17_9 : solve 6 [53,17,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_9 : solve 7 [17,9] = false := by
  apply split_solve 6 [17,9] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_17_9, reject_5_17_9, reject_20_17_9, reject_21_17_9, reject_36_17_9, reject_37_17_9, reject_52_17_9, reject_53_17_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_24_9 : solve 6 [1,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_24_9 : solve 6 [5,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_24_9 : solve 6 [17,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_24_9 : solve 6 [21,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_24_9 : solve 6 [33,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_24_9 : solve 6 [37,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_24_9 : solve 6 [49,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_24_9 : solve 6 [53,24,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_9 : solve 7 [24,9] = false := by
  apply split_solve 6 [24,9] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_24_9, reject_5_24_9, reject_17_24_9, reject_21_24_9, reject_33_24_9, reject_37_24_9, reject_49_24_9, reject_53_24_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_25_9 : solve 6 [1,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25_9 : solve 6 [5,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_25_9 : solve 6 [17,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25_9 : solve 6 [21,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_25_9 : solve 6 [33,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25_9 : solve 6 [37,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_25_9 : solve 6 [49,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25_9 : solve 6 [53,25,9] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_9 : solve 7 [25,9] = false := by
  apply split_solve 6 [25,9] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_25_9, reject_5_25_9, reject_17_25_9, reject_21_25_9, reject_33_25_9, reject_37_25_9, reject_49_25_9, reject_53_25_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9 : solve 8 [9] = false := by
  apply split_solve 7 [9] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_9, reject_17_9, reject_24_9, reject_25_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_8_17 : solve 6 [4,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_8_17 : solve 6 [5,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_8_17 : solve 6 [20,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_8_17 : solve 6 [21,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_8_17 : solve 6 [36,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_8_17 : solve 6 [37,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_8_17 : solve 6 [52,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_8_17 : solve 6 [53,8,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_8_17 : solve 7 [8,17] = false := by
  apply split_solve 6 [8,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_8_17, reject_5_8_17, reject_20_8_17, reject_21_8_17, reject_36_8_17, reject_37_8_17, reject_52_8_17, reject_53_8_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_9_17 : solve 6 [4,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_9_17 : solve 6 [5,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_9_17 : solve 6 [20,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_9_17 : solve 6 [21,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_9_17 : solve 6 [36,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_9_17 : solve 6 [37,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_9_17 : solve 6 [52,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_9_17 : solve 6 [53,9,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_17 : solve 7 [9,17] = false := by
  apply split_solve 6 [9,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_9_17, reject_5_9_17, reject_20_9_17, reject_21_9_17, reject_36_9_17, reject_37_9_17, reject_52_9_17, reject_53_9_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_24_17 : solve 6 [4,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_24_17 : solve 6 [5,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_24_17 : solve 6 [20,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_24_17 : solve 6 [21,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_24_17 : solve 6 [36,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_24_17 : solve 6 [37,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_24_17 : solve 6 [52,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_24_17 : solve 6 [53,24,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_17 : solve 7 [24,17] = false := by
  apply split_solve 6 [24,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_24_17, reject_5_24_17, reject_20_24_17, reject_21_24_17, reject_36_24_17, reject_37_24_17, reject_52_24_17, reject_53_24_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_25_17 : solve 6 [4,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25_17 : solve 6 [5,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_25_17 : solve 6 [20,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25_17 : solve 6 [21,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_25_17 : solve 6 [36,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25_17 : solve 6 [37,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_25_17 : solve 6 [52,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25_17 : solve 6 [53,25,17] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_17 : solve 7 [25,17] = false := by
  apply split_solve 6 [25,17] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_25_17, reject_5_25_17, reject_20_25_17, reject_21_25_17, reject_36_25_17, reject_37_25_17, reject_52_25_17, reject_53_25_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17 : solve 8 [17] = false := by
  apply split_solve 7 [17] (102,8) [8,9,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_8_17, reject_9_17, reject_24_17, reject_25_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_1_25 : solve 6 [4,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_1_25 : solve 6 [5,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_1_25 : solve 6 [20,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_1_25 : solve 6 [21,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_1_25 : solve 6 [36,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_1_25 : solve 6 [37,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_1_25 : solve 6 [52,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_1_25 : solve 6 [53,1,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_25 : solve 7 [1,25] = false := by
  apply split_solve 6 [1,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_1_25, reject_5_1_25, reject_20_1_25, reject_21_1_25, reject_36_1_25, reject_37_1_25, reject_52_1_25, reject_53_1_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_5_25 : solve 6 [16,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_5_25 : solve 6 [17,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_5_25 : solve 6 [20,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_5_25 : solve 6 [21,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_48_5_25 : solve 6 [48,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_5_25 : solve 6 [49,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_5_25 : solve 6 [52,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_5_25 : solve 6 [53,5,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25 : solve 7 [5,25] = false := by
  apply split_solve 6 [5,25] (74,16) [16,17,20,21,48,49,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_5_25, reject_17_5_25, reject_20_5_25, reject_21_5_25, reject_48_5_25, reject_49_5_25, reject_52_5_25, reject_53_5_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_17_25 : solve 6 [4,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_17_25 : solve 6 [5,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_17_25 : solve 6 [20,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_17_25 : solve 6 [21,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_17_25 : solve 6 [36,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_17_25 : solve 6 [37,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_17_25 : solve 6 [52,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_17_25 : solve 6 [53,17,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_25 : solve 7 [17,25] = false := by
  apply split_solve 6 [17,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_17_25, reject_5_17_25, reject_20_17_25, reject_21_17_25, reject_36_17_25, reject_37_17_25, reject_52_17_25, reject_53_17_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_32_21_25 : solve 6 [32,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_21_25 : solve 6 [33,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_21_25 : solve 6 [36,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_21_25 : solve 6 [37,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_48_21_25 : solve 6 [48,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_21_25 : solve 6 [49,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_21_25 : solve 6 [52,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_21_25 : solve 6 [53,21,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25 : solve 7 [21,25] = false := by
  apply split_solve 6 [21,25] (74,32) [32,33,36,37,48,49,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_32_21_25, reject_33_21_25, reject_36_21_25, reject_37_21_25, reject_48_21_25, reject_49_21_25, reject_52_21_25, reject_53_21_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_33_25 : solve 6 [4,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_33_25 : solve 6 [5,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_33_25 : solve 6 [20,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_33_25 : solve 6 [21,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_33_25 : solve 6 [36,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_33_25 : solve 6 [37,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_33_25 : solve 6 [52,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_33_25 : solve 6 [53,33,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_25 : solve 7 [33,25] = false := by
  apply split_solve 6 [33,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_33_25, reject_5_33_25, reject_20_33_25, reject_21_33_25, reject_36_33_25, reject_37_33_25, reject_52_33_25, reject_53_33_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_37_25 : solve 6 [16,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_37_25 : solve 6 [17,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_37_25 : solve 6 [20,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_37_25 : solve 6 [21,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_48_37_25 : solve 6 [48,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_37_25 : solve 6 [49,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_37_25 : solve 6 [52,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_37_25 : solve 6 [53,37,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25 : solve 7 [37,25] = false := by
  apply split_solve 6 [37,25] (74,16) [16,17,20,21,48,49,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_37_25, reject_17_37_25, reject_20_37_25, reject_21_37_25, reject_48_37_25, reject_49_37_25, reject_52_37_25, reject_53_37_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_4_49_25 : solve 6 [4,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_49_25 : solve 6 [5,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_20_49_25 : solve 6 [20,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_49_25 : solve 6 [21,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_36_49_25 : solve 6 [36,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_49_25 : solve 6 [37,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_52_49_25 : solve 6 [52,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_49_25 : solve 6 [53,49,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_25 : solve 7 [49,25] = false := by
  apply split_solve 6 [49,25] (74,4) [4,5,20,21,36,37,52,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_4_49_25, reject_5_49_25, reject_20_49_25, reject_21_49_25, reject_36_49_25, reject_37_49_25, reject_52_49_25, reject_53_49_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_53_25 : solve 6 [1,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_3_53_25 : solve 6 [3,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_53_25 : solve 6 [9,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_11_53_25 : solve 6 [11,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_53_25 : solve 6 [33,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_35_53_25 : solve 6 [35,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_41_53_25 : solve 6 [41,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_43_53_25 : solve 6 [43,53,25] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25 : solve 7 [53,25] = false := by
  apply split_solve 6 [53,25] (84,1) [1,3,9,11,33,35,41,43] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_53_25, reject_3_53_25, reject_9_53_25, reject_11_53_25, reject_33_53_25, reject_35_53_25, reject_41_53_25, reject_43_53_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25 : solve 8 [25] = false := by
  apply split_solve 7 [25] (74,1) [1,5,17,21,33,37,49,53] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1_25, reject_5_25, reject_17_25, reject_21_25, reject_33_25, reject_37_25, reject_49_25, reject_53_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checked : solve 9 [] = false := by
  apply split_solve 8 [] (102,1) [1,9,17,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_1, reject_9, reject_17, reject_25]

end CoverCheck


def prependNots (pins : List ℕ) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.not, [0]⟩ :: ⟨GateOp.not, pins⟩ :: C.gates, C.output⟩

lemma prependNots_eval (pins : List ℕ) (C : Circuit) (x : Fin 9 → Bool) :
    (prependNots pins C).eval (List.ofFn x) =
      let w := List.ofFn x ++ [!x 0]
      C.eval (w ++ [GateOp.not.eval (pins.map fun i => w.getD i false)]) := by
  have hzero : (List.ofFn x).getD 0 false = x 0 := getD_ofFn 9 x false (0 : Fin 9)
  simp only [prependNots, Circuit.eval, Circuit.wires, List.foldl_cons, List.map_cons,
    List.map_nil, GateOp.eval, List.headD_cons, hzero]

lemma prependNots_fanInTwo (pins : List ℕ) (C : Circuit) (hlen : pins.length ≤ 2)
    (hfan : FanInTwo C) : FanInTwo (prependNots pins C) := by
  intro g hg
  change g ∈ (⟨GateOp.not, [0]⟩ : Gate) :: ⟨GateOp.not, pins⟩ :: C.gates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  rcases List.mem_cons.mp hg with rfl | hg
  · simpa using hlen
  · exact hfan g hg

lemma petersen_binary_bound (C : Circuit) (hfan : FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = petersenF x)
    (small : nonNotCount C.gates ≤ 13) : False := by
  obtain ⟨gs, o, L, budget, _⟩ := Readers.least_with_budget C hfan computes petersen_nonconstant
  have bound := budget.trans small
  obtain ⟨s, hs, once⟩ := terminal_class L bound
  obtain ⟨h, hh⟩ := Probes.layout_exists s hs
  obtain ⟨l, valid, safe⟩ := Probes.ledger_for_circuit L h (fun t => once _ (hh t))
  exact Probes.no_ledger bound valid safe CoverCheck.checked


open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
-- Adapt the boundary argument of L_meta_2770 to four branching wires.
theorem fourForksOfBudget {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (budget : nonNotCount gs ≤ 13) : (circuitBranchWires (n := 10) gs).card ≤ 4 := by
  classical
  let branches := circuitBranchWires (n := 10) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
      let wire : Fin (10 + gs.length) := ⟨w, hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at count
  change branches.card ≤ 4
  omega

theorem normalizedCuts {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ 4) :
    ∃ label : Fin n → Fin 5,
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ i, label i = 4 → firstInputBoundary clean out live i = out) ∧
      (∀ k : Fin 5, ∃ code : (Fin n → Bool) → Bool,
        (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
        (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → vl gs x out.val = vl gs y out.val)) := by
  classical
  let branches := circuitBranchWires (n := n) gs
  change branches.card ≤ 4 at hcard
  let cuts := insert out branches
  have small : cuts.card ≤ 5 := (Finset.card_insert_le ..).trans (by omega)
  let boundary := firstInputBoundary clean out live
  have mem (i : Fin n) : boundary i ∈ cuts := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let embed := (cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin 5 :=
    ⟨5 - cuts.card + (embed c).val, by have := (embed c).isLt; omega⟩
  have strict : StrictMono rank := by
    intro c d hcd
    have he := embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change 5 - cuts.card + (embed c).val < 5 - cuts.card + (embed d).val
    omega
  let loc (i : Fin n) : cuts := ⟨boundary i, mem i⟩
  let label (i : Fin n) := rank (loc i)
  have eqv (i j : Fin n) : label i = label j ↔ boundary i = boundary j := by
    change rank (loc i) = rank (loc j) ↔ (loc i).val = (loc j).val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  have last (i : Fin n) (h : label i = 4) : boundary i = out := by
    by_contra bad
    let top : cuts := ⟨out, Finset.mem_insert_self _ _⟩
    have lt : rank (loc i) < rank top := strict (lt_of_le_of_ne
      (show loc i ≤ top from wire_le_output clean out live _)
      (fun hh => bad (congrArg Subtype.val hh)))
    change label i < rank top at lt
    rw [h] at lt
    exact (by omega)
  refine ⟨label, eqv, last, ?_⟩
  intro k
  by_cases used : ∃ z, label z = k
  · obtain ⟨z, rfl⟩ := used
    let c := boundary z
    have term : FirstBranchRoute.Terminal (readEdge gs) out c :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs z)
    refine ⟨fun x => vl gs x c.val, ?_, ?_⟩
    · intro x y hxy
      apply agree_on_input_ancestors clean
      intro i path
      apply hxy i
      exact strict.monotone (show loc i ≤ loc z from
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path term)
    · intro x y hxy heq
      have blocked := firstInputGroup_controlled clean out live c
      rcases blocked with atOut | apart
      · simpa only [atOut] using heq
      · apply circuit_cut_agreement clean c out x y heq
        intro i hi
        apply apart i
        apply (mem_firstInputGroup clean out live c i).mpr
        exact (eqv i z).mp (by_contra fun ne => hi (hxy i ne))
  · refine ⟨fun _ => false, fun _ _ _ => rfl, ?_⟩
    intro x y hxy _
    have : x = y := funext (fun i => hxy i (fun h => used ⟨i,h⟩))
    rw [this]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Suffix2770

def F (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def plug (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x

lemma plug_list (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (plug x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ_last]
  simp [plug]
  rfl

def runStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def before : Fin 9 → ℕ := ![10,1,2,5,1,1,2,4,8]
def after : Fin 9 → ℕ := ![11,3,6,13,17,33,66,132,264]
def maskBits (m : Nat) (j : Fin 9) := m.testBit j.val
def embed (x : Fin 9 → Bool) := plug x (x 0 || x 3)

lemma rawPairs : ∀ i : Fin 9, let a := maskBits (before i); let b := maskBits (after i)
    (∀ j : Fin 10, j ≠ i.castSucc → embed a j = embed b j) ∧ F a ≠ F b := by decide +kernel

def nonNot : GateOp → Bool
  | .not => false
  | _ => true

def binary (gs : List Gate) := gs.countP (fun g => nonNot g.op)

lemma budget (gs : List Gate)
    (fan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    binary gs + gs.countP (fun g => g.op.eval [false]) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ih' := ih (fun q hq => fan q (List.mem_cons_of_mem _ hq))
    have hg := fan g List.mem_cons_self
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    unfold binary at ih' ⊢
    have one : (if nonNot g.op then 1 else 0) + (if g.op.eval [false] then 1 else 0) = 1 := by
      rcases hg with ho | ho | ho <;> rw [ho] <;> rfl
    simp only [List.countP_cons, List.length_cons]
    split_ifs at one ⊢ <;> omega

lemma suffix_shape
    (hBound : ∀ B : Circuit, FanInTwo B → circuitFun 9 B = F → 14 ≤ binary B.gates)
    (C : Circuit) (hfan : FanInTwo C) (hlen : C.gates.length = 15)
    (first : C.gates[0]? = some ⟨.or, [0,3]⟩)
    (nots : 1 ≤ C.gates.countP (fun g => g.op.eval [false])) (hfun : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ binary D.gates ≤ 13 ∧ D.gates.length = 14 ∧
      (∀ x : Fin 9 → Bool, circuitFun 10 D (embed x) = F x) ∧
      ∀ i : Fin 10, ∃ p q : Fin 10 → Bool, (∀ j, j ≠ i → p j = q j) ∧
          circuitFun 10 D p ≠ circuitFun 10 D q := by
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil => contradiction
  | cons g gs =>
    change (g :: gs)[0]? = _ at first
    simp only [List.getElem?_cons_zero,Option.some.injEq] at first
    subst g
    let D : Circuit := ⟨gs,out⟩
    have hfd : FanInTwo D := fun a ha => hfan a (List.mem_cons_of_mem _ ha)
    have hs : gs.length = 14 := by change (Gate.mk .or [0,3] :: gs).length = 15 at hlen; simpa using hlen
    have hn : 1 ≤ gs.countP (fun g => g.op.eval [false]) := by
      change 1 ≤ (Gate.mk .or [0,3] :: gs).countP _ at nots
      simpa [List.countP_cons,GateOp.eval] using nots
    have hb : binary gs ≤ 13 := by
      have := budget gs (fun a ha => (hfd a ha).1)
      omega
    have seed (x : Fin 9 → Bool) : runStep (List.ofFn x) ⟨.or,[0,3]⟩ = List.ofFn (embed x) := by
      rw [embed,plug_list]; simp [runStep,GateOp.eval,List.getD]
    have valid (x : Fin 9 → Bool) : circuitFun 10 D (embed x) = F x := by
      have hx := congrFun hfun x
      change (gs.foldl runStep (runStep (List.ofFn x) ⟨.or,[0,3]⟩)).getD out false = F x at hx
      rw [seed] at hx
      exact hx
    refine ⟨D, hfd, hb, hs, valid, ?_⟩
    intro i
    by_cases hlt : i.val < 9
    · let v : Fin 9 := ⟨i.val,hlt⟩
      have hi : i = v.castSucc := Fin.ext rfl
      obtain ⟨hp,hd⟩ := rawPairs v
      exact ⟨embed (maskBits (before v)), embed (maskBits (after v)), by simpa only [hi] using hp,
        by simpa only [valid] using hd⟩
    · have last : i = Fin.last 9 := Fin.ext (by have := i.isLt; change i.val = 9; omega)
      subst i
      by_contra! hind
      let a : Gate := ⟨.not,[0]⟩
      let E : Circuit := ⟨a :: gs,out⟩
      have fan : FanInTwo E := by
        intro q hq
        change q ∈ a :: gs at hq
        rcases List.mem_cons.mp hq with rfl | hmem
        · simp [a]
        · exact hfd q hmem
      have start (x : Fin 9 → Bool) : runStep (List.ofFn x) a = List.ofFn (plug x (!x 0)) := by
        rw [plug_list]
        simp [runStep, a, GateOp.eval, List.getD]
      have he (x : Fin 9 → Bool) : circuitFun 9 E x = F x := by
        have hx := hind (plug x (!x 0)) (embed x) (by
          intro j hj
          refine Fin.lastCases ?_ (fun j => ?_) j hj
          · exact fun h => (h rfl).elim
          · simp [embed,plug])
        change (gs.foldl runStep (runStep (List.ofFn x) a)).getD out false = F x
        rw [start]
        exact hx.trans (valid x)
      have bad := hBound E fan (funext he)
      change 14 ≤ binary (a :: gs) at bad
      have same : binary (a :: gs) = binary gs := by unfold binary; rw [List.countP_cons]; rfl
      rw [same] at bad
      omega

def cofactorNo (i : Fin 10) (b : Bool) : Nat :=
  if b then ![1,2,4,8,16,32,64,128,256,1] i else 0

def cofactorYes (i : Fin 10) (b : Bool) : Nat :=
  if b then ![3,3,6,11,17,33,66,131,259,3] i else ![6,12,3,3,3,3,3,3,3,6] i

lemma cofactorPairs : ∀ (i : Fin 10) (b : Bool),
    let p := maskBits (cofactorNo i b)
    let q := maskBits (cofactorYes i b)
    embed p i = b ∧ embed q i = b ∧ F p ≠ F q := by decide +kernel

lemma suffix_data
    (hBound : ∀ B : Circuit, FanInTwo B → circuitFun 9 B = F → 14 ≤ binary B.gates)
    (C : Circuit) (hfan : FanInTwo C) (hlen : C.gates.length = 15)
    (first : C.gates[0]? = some ⟨.or, [0,3]⟩)
    (nots : 1 ≤ C.gates.countP (fun g => g.op.eval [false])) (hfun : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ binary D.gates ≤ 13 ∧ D.gates.length = 14 ∧
      (∀ x : Fin 10 → Bool, x 9 = (x 0 || x 3) →
        circuitFun 10 D x = F (fun i : Fin 9 => x i.castSucc)) ∧
      (∀ i : Fin 10, ∃ p q : Fin 10 → Bool, (∀ j, j ≠ i → p j = q j) ∧
          circuitFun 10 D p ≠ circuitFun 10 D q) ∧
      (∀ (i : Fin 10) (b : Bool), ∃ p q : Fin 10 → Bool,
          circuitFun 10 D (Function.update p i b) ≠ circuitFun 10 D (Function.update q i b)) := by
  obtain ⟨D, fan, hb, len, agree, dep⟩ := suffix_shape hBound C hfan hlen first nots hfun
  refine ⟨D, fan, hb, len, ?_, dep, ?_⟩
  · intro x hx
    have heq : embed (fun i : Fin 9 => x i.castSucc) = x := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · change Fin.lastCases (motive := fun _ => Bool) (x 0 || x 3) (fun i : Fin 9 => x i.castSucc) (Fin.last 9) = x 9
        rw [Fin.lastCases_last]; exact hx.symm
      · simp [embed, plug]
    exact heq ▸ agree (fun i : Fin 9 => x i.castSucc)
  · intro i b
    let p := maskBits (cofactorNo i b)
    let q := maskBits (cofactorYes i b)
    obtain ⟨hp, hq, hf⟩ := cofactorPairs i b
    refine ⟨embed p, embed q, ?_⟩
    have ep : Function.update (embed p) i b = embed p := hp ▸ Function.update_eq_self _ _
    have eq : Function.update (embed q) i b = embed q := hq ▸ Function.update_eq_self _ _
    simpa only [ep, eq, agree] using hf

end Suffix2770

namespace Conflict2770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof PetersenCutFormula PetersenCutIndependent PetersenFirstGroup PetersenCutTrace PetersenScratch

def pairs : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)]

def value (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def contexts (e : Fin 10 × Fin 10) : Nat × Nat :=
  match e.1.val, e.2.val with
  | 0, 1 => (520, 616)
  | 1, 2 => (0, 192)
  | 2, 3 => (513, 897)
  | 0, 5 => (520, 650)
  | 1, 6 => (0, 260)
  | 2, 7 => (0, 34)
  | 5, 7 => (0, 260)
  | 3, 8 => (513, 581)
  | 5, 8 => (0, 192)
  | _, _ => (0, 34)

def bits (v : Nat) (i : Fin 10) := v.testBit i.val

theorem checkedContexts : ∀ e ∈ pairs, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (bits (contexts e).1) a b
    let xo := pairInput e.1 e.2 (bits (contexts e).2) a b
    xa 9 = (xa 0 || xa 3) ∧ value xa = (a && b) ∧
      xo 9 = (xo 0 || xo 3) ∧ value xo = (a || b) := by
  decide +kernel

theorem boundaryConflict {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool, x 9 = (x 0 || x 3) → vl gs x out.val = value x)
    (e : Fin 10 × Fin 10) (he : e ∈ pairs) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 10, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin 10 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor (bits (contexts e).1)
  obtain ⟨fo, ho⟩ := factor (bits (contexts e).2)
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h := checkedContexts e he a b
    exact (ha a b).trans ((computes _ h.1).trans h.2.1)
  · intro a b
    have h := checkedContexts e he a b
    exact (ho a b).trans ((computes _ h.2.2.1).trans h.2.2.2)

end Conflict2770
namespace Suffix2770
lemma binary_eq (gs : List Gate) : binary gs = nonNotCount gs := by
  change List.countP (fun g : Gate => nonNot g.op) gs = List.countP (fun g : Gate => !(isNotGate g.op)) gs
  congr 1
  funext g
  cases g.op <;> rfl

lemma lower (B : Circuit) (fan : FanInTwo B) (hfun : circuitFun 9 B = F) : 14 ≤ binary B.gates := by
  rw [binary_eq]
  by_contra! small
  apply petersen_binary_bound B fan _ (by omega)
  intro x
  have hx := congrFun hfun x
  simpa only [circuitFun,F,petersenF,edgeFun,edges,List.any_cons,List.any_nil,
    Bool.or_false,Bool.or_assoc] using hx

lemma dep_of_pair {n : ℕ} {H : (Fin n → Bool) → Bool} {i : Fin n}
    (hd : ∃ p q : Fin n → Bool, (∀ j, j ≠ i → p j = q j) ∧ H p ≠ H q) : Dep H i := by
  obtain ⟨p,q,ha,hf⟩ := hd
  have ne : p i ≠ q i := by
    intro hp
    have eq : p = q := funext (fun j => by
      by_cases h : j = i
      · simpa only [h] using hp
      · exact ha j h)
    exact hf (congrArg H eq)
  have hi : (!p i) = q i := by cases hp : p i <;> cases hq : q i <;> simp_all
  have up : Function.update p i (!p i) = q := by
    funext j
    by_cases h : j = i
    · simpa only [h, Function.update_self] using hi
    · simpa only [Function.update_of_ne h] using ha j h
  exact ⟨p, by simpa only [up] using hf.symm⟩


end Suffix2770


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 4000000 in
lemma rankCheck :
    ∀ v1 : Fin 5,
    ∀ v2 : Fin 5,
      v1 ≠ v2 →
    ∀ v5 : Fin 5,
      (v1 = v5 → ¬ (v1 < v2 ∧ v1 < v2)) →
      (v2 = v5 → ¬ (v2 < v1 ∧ v2 < v1)) →
    ∀ v7 : Fin 5,
      v2 ≠ v7 →
      v5 ≠ v7 →
      (v1 = v2 → ¬ (v1 < v7 ∧ v1 < v7)) →
      (v1 = v5 → ¬ (v1 < v7 ∧ v1 < v7)) →
      (v1 = v7 → ¬ (v1 < v2 ∧ v1 < v2)) →
      (v1 = v7 → ¬ (v1 < v5 ∧ v1 < v5)) →
      (v2 = v5 → ¬ (v2 < v7 ∧ v2 < v7)) →
      (v2 = v7 → ¬ (v2 < v1 ∧ v2 < v1)) →
      (v2 = v7 → ¬ (v2 < v5 ∧ v2 < v5)) →
      (v5 = v7 → ¬ (v5 < v2 ∧ v5 < v2)) →
    ∀ v6 : Fin 5,
      v1 ≠ v6 →
      (v1 = v2 → ¬ (v1 < v6 ∧ v1 < v6)) →
      (v1 = v5 → ¬ (v1 < v6 ∧ v1 < v6)) →
      (v1 = v6 → ¬ (v1 < v2 ∧ v1 < v2)) →
      (v1 = v7 → ¬ (v1 < v6 ∧ v1 < v6)) →
      (v2 = v6 → ¬ (v2 < v1 ∧ v2 < v1)) →
      (v2 = v6 → ¬ (v2 < v7 ∧ v2 < v7)) →
      (v5 = v6 → ¬ (v5 < v1 ∧ v5 < v1)) →
      (v5 = v6 → ¬ (v5 < v7 ∧ v5 < v7)) →
      (v6 = v7 → ¬ (v6 < v1 ∧ v6 < v1)) →
      (v6 = v7 → ¬ (v6 < v2 ∧ v6 < v2)) →
      (v6 = v7 → ¬ (v6 < v5 ∧ v6 < v5)) →
    ∀ v8 : Fin 5,
      v5 ≠ v8 →
      v6 ≠ v8 →
      (v1 = v5 → ¬ (v1 < v8 ∧ v1 < v8)) →
      (v1 = v6 → ¬ (v1 < v8 ∧ v1 < v8)) →
      (v1 = v8 → ¬ (v1 < v2 ∧ v1 < v2)) →
      (v1 = v8 → ¬ (v1 < v5 ∧ v1 < v5)) →
      (v1 = v8 → ¬ (v1 < v6 ∧ v1 < v6)) →
      (v2 = v5 → ¬ (v2 < v8 ∧ v2 < v8)) →
      (v2 = v6 → ¬ (v2 < v8 ∧ v2 < v8)) →
      (v2 = v8 → ¬ (v2 < v1 ∧ v2 < v1)) →
      (v2 = v8 → ¬ (v2 < v5 ∧ v2 < v5)) →
      (v2 = v8 → ¬ (v2 < v6 ∧ v2 < v6)) →
      (v2 = v8 → ¬ (v2 < v7 ∧ v2 < v7)) →
      (v5 = v6 → ¬ (v5 < v8 ∧ v5 < v8)) →
      (v5 = v7 → ¬ (v5 < v8 ∧ v5 < v8)) →
      (v5 = v8 → ¬ (v5 < v6 ∧ v5 < v6)) →
      (v5 = v8 → ¬ (v5 < v7 ∧ v5 < v7)) →
      (v6 = v7 → ¬ (v6 < v8 ∧ v6 < v8)) →
      (v6 = v8 → ¬ (v6 < v1 ∧ v6 < v1)) →
      (v6 = v8 → ¬ (v6 < v5 ∧ v6 < v5)) →
      (v7 = v8 → ¬ (v7 < v2 ∧ v7 < v2)) →
      (v7 = v8 → ¬ (v7 < v5 ∧ v7 < v5)) →
      (v7 = v8 → ¬ (v7 < v6 ∧ v7 < v6)) →
    ∀ v0 : Fin 5,
      v0 ≠ v1 →
      v0 ≠ v5 →
      (v0 = v1 → ¬ (v0 < v5 ∧ v0 < v5)) →
      (v0 = v1 → ¬ (v0 < v6 ∧ v0 < v6)) →
      (v0 = v2 → ¬ (v0 < v1 ∧ v0 < v1)) →
      (v0 = v2 → ¬ (v0 < v5 ∧ v0 < v5)) →
      (v0 = v5 → ¬ (v0 < v1 ∧ v0 < v1)) →
      (v0 = v5 → ¬ (v0 < v7 ∧ v0 < v7)) →
      (v0 = v6 → ¬ (v0 < v1 ∧ v0 < v1)) →
      (v0 = v7 → ¬ (v0 < v5 ∧ v0 < v5)) →
      (v0 = v8 → ¬ (v0 < v1 ∧ v0 < v1)) →
      (v0 = v8 → ¬ (v0 < v5 ∧ v0 < v5)) →
      (v1 = v2 → ¬ (v1 < v0 ∧ v1 < v0)) →
      (v1 = v5 → ¬ (v1 < v0 ∧ v1 < v0)) →
      (v1 = v6 → ¬ (v1 < v0 ∧ v1 < v0)) →
      (v1 = v8 → ¬ (v1 < v0 ∧ v1 < v0)) →
      (v2 = v5 → ¬ (v2 < v0 ∧ v2 < v0)) →
      (v5 = v7 → ¬ (v5 < v0 ∧ v5 < v0)) →
      (v5 = v8 → ¬ (v5 < v0 ∧ v5 < v0)) →
    ∀ v3 : Fin 5,
      v2 ≠ v3 →
      v3 ≠ v8 →
      (v1 = v2 → ¬ (v1 < v3 ∧ v1 < v3)) →
      (v1 = v3 → ¬ (v1 < v2 ∧ v1 < v2)) →
      (v1 = v3 → ¬ (v1 < v8 ∧ v1 < v8)) →
      (v1 = v8 → ¬ (v1 < v3 ∧ v1 < v3)) →
      (v2 = v3 → ¬ (v2 < v7 ∧ v2 < v7)) →
      (v2 = v3 → ¬ (v2 < v8 ∧ v2 < v8)) →
      (v2 = v5 → ¬ (v2 < v3 ∧ v2 < v3)) →
      (v2 = v7 → ¬ (v2 < v3 ∧ v2 < v3)) →
      (v2 = v8 → ¬ (v2 < v3 ∧ v2 < v3)) →
      (v3 = v5 → ¬ (v3 < v2 ∧ v3 < v2)) →
      (v3 = v5 → ¬ (v3 < v8 ∧ v3 < v8)) →
      (v3 = v6 → ¬ (v3 < v8 ∧ v3 < v8)) →
      (v3 = v7 → ¬ (v3 < v2 ∧ v3 < v2)) →
      (v3 = v8 → ¬ (v3 < v2 ∧ v3 < v2)) →
      (v3 = v8 → ¬ (v3 < v6 ∧ v3 < v6)) →
      (v5 = v8 → ¬ (v5 < v3 ∧ v5 < v3)) →
      (v6 = v8 → ¬ (v6 < v3 ∧ v6 < v3)) →
      (v0 = v3 → ¬ (v0 < v2 ∧ v0 < v5)) →
      (v0 = v3 → ¬ (v0 < v1 ∧ v0 < v8)) →
    ∀ v4 : Fin 5,
      (v0 = v4 → ¬ (v0 < v1 ∧ v0 < v1)) →
      (v0 = v4 → ¬ (v0 < v5 ∧ v0 < v5)) →
      (v1 = v4 → ¬ (v1 < v0 ∧ v1 < v0)) →
      (v1 = v4 → ¬ (v1 < v6 ∧ v1 < v6)) →
      (v2 = v4 → ¬ (v2 < v3 ∧ v2 < v3)) →
      (v2 = v4 → ¬ (v2 < v7 ∧ v2 < v7)) →
      (v3 = v4 → ¬ (v3 < v2 ∧ v3 < v2)) →
      (v3 = v4 → ¬ (v3 < v8 ∧ v3 < v8)) →
      (v4 = v5 → ¬ (v4 < v0 ∧ v4 < v0)) →
      (v4 = v5 → ¬ (v4 < v7 ∧ v4 < v7)) →
      (v4 = v6 → ¬ (v4 < v1 ∧ v4 < v1)) →
      (v4 = v6 → ¬ (v4 < v8 ∧ v4 < v8)) →
      (v4 = v7 → ¬ (v4 < v2 ∧ v4 < v2)) →
      (v4 = v7 → ¬ (v4 < v5 ∧ v4 < v5)) →
      (v4 = v8 → ¬ (v4 < v3 ∧ v4 < v3)) →
      (v4 = v8 → ¬ (v4 < v6 ∧ v4 < v6)) →
    ∀ v9 : Fin 5,
    v4 = 4 ∧ v6 = 4 ∧ v7 = 4 := by decide +kernel

open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup

namespace Boundary
abbrev Row := Fin 10 → Bool
abbrev coord := Conflict2770.bits
def valid (x : Row) := x 9 = (x 0 || x 3)
def sameOff (i j : Fin 10) (a b : Nat) : Prop :=
  ∀ z : Fin 10, z ≠ i → z ≠ j → coord a z = coord b z

def separates (a b : Nat) : Prop := valid (coord a) ∧ valid (coord b) ∧
  Conflict2770.value (coord a) ≠ Conflict2770.value (coord b)

-- Each successive pair of rows must give different output bits. Between pairs,
-- only later inputs change, so a single boundary bit cannot separate all three pairs.
def witness (i j k l : Fin 10) (a b c d e f : Nat) : Prop :=
  separates a b ∧ separates c d ∧ separates e f ∧
  sameOff i j a b ∧ sameOff i j c d ∧ sameOff i j e f ∧
  sameOff k l b c ∧ sameOff k l d e ∧ sameOff k l f a

def Cut (label : Fin 10 → Fin 5) (t : Fin 5) : Prop :=
  ∃ code : Row → Bool,
    (∀ x y, (∀ i, label i ≤ t → x i = y i) → code x = code y) ∧
    (∀ x y, valid x → valid y → (∀ i, label i ≠ t → x i = y i) →
      code x = code y → Conflict2770.value x = Conflict2770.value y)

lemma obstruction (label : Fin 10 → Fin 5) (cuts : ∀ t, Cut label t)
    (i j k l : Fin 10) (a b c d e f : Nat) (w : witness i j k l a b c d e f)
    (eq : label i = label j) : ¬ (label i < label k ∧ label i < label l) := by
  rintro ⟨hk, hl⟩
  obtain ⟨code,low,high⟩ := cuts (label i)
  obtain ⟨ab,cd,ef,ab',cd',ef',bc,de,fa⟩ := w
  have early {x y} (h : sameOff k l x y) : code (coord x) = code (coord y) :=
    low _ _ (fun z hz => h z (fun he => (he ▸ hz).not_gt hk) (fun he => (he ▸ hz).not_gt hl))
  have diff {x y} (s : separates x y) (h : sameOff i j x y) : code (coord x) ≠ code (coord y) :=
    fun same => s.2.2 (high _ _ s.1 s.2.1
      (fun z hz => h z (fun he => hz (he ▸ rfl)) (fun he => hz (he ▸ eq.symm))) same)
  have h1 := diff ab ab'
  have h2 := diff cd cd'
  have h3 := diff ef ef'
  rw [←early bc] at h2
  rw [←early de,early fa] at h3
  exact (show ∀ x y z : Bool, x ≠ y → y ≠ z → z ≠ x → False by decide) _ _ _ h1 h2 h3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma lastRanks (label : Fin 10 → Fin 5)
    (conf : ∀ q ∈ Conflict2770.pairs, label q.1 ≠ label q.2) (cuts : ∀ t, Cut label t) :
    label 4 = 4 ∧ label 6 = 4 ∧ label 7 = 4 := by
  let dif (i j : Fin 10) (h : (i,j) ∈ Conflict2770.pairs) := conf (i,j) h
  let rule (i j k l : Fin 10) (a b c d e f : Nat)
      (w : witness i j k l a b c d e f) := obstruction label cuts i j k l a b c d e f w
  exact rankCheck
    (label 1)
    (label 2)
    (dif 1 2 (by decide))
    (label 5)
    (rule 1 5 2 2 306 274 278 276 276 310 (by unfold witness separates sameOff valid; decide))
    (rule 2 5 1 1 308 276 278 274 274 310 (by unfold witness separates sameOff valid; decide))
    (label 7)
    (dif 2 7 (by decide))
    (dif 5 7 (by decide))
    (rule 1 2 7 7 775 773 901 897 897 903 (by unfold witness separates sameOff valid; decide))
    (rule 1 5 7 7 618 616 744 712 712 746 (by unfold witness separates sameOff valid; decide))
    (rule 1 7 2 2 899 897 901 773 773 903 (by unfold witness separates sameOff valid; decide))
    (rule 1 7 5 5 714 712 744 616 616 746 (by unfold witness separates sameOff valid; decide))
    (rule 2 5 7 7 805 773 901 897 897 933 (by unfold witness separates sameOff valid; decide))
    (rule 2 7 1 1 406 402 402 278 276 404 (by unfold witness separates sameOff valid; decide))
    (rule 2 7 5 5 716 712 744 616 616 748 (by unfold witness separates sameOff valid; decide))
    (rule 5 7 2 2 929 897 901 773 773 933 (by unfold witness separates sameOff valid; decide))
    (label 6)
    (dif 1 6 (by decide))
    (rule 1 2 6 6 654 650 714 712 712 718 (by unfold witness separates sameOff valid; decide))
    (rule 1 5 6 6 682 650 714 712 712 746 (by unfold witness separates sameOff valid; decide))
    (rule 1 6 2 2 338 274 278 276 276 342 (by unfold witness separates sameOff valid; decide))
    (rule 1 7 6 6 682 554 618 616 616 746 (by unfold witness separates sameOff valid; decide))
    (rule 2 6 1 1 716 712 714 650 650 718 (by unfold witness separates sameOff valid; decide))
    (rule 2 6 7 7 837 773 901 897 897 965 (by unfold witness separates sameOff valid; decide))
    (rule 5 6 1 1 744 712 714 650 650 746 (by unfold witness separates sameOff valid; decide))
    (rule 5 6 7 7 618 554 682 650 650 746 (by unfold witness separates sameOff valid; decide))
    (rule 6 7 1 1 744 616 618 554 554 746 (by unfold witness separates sameOff valid; decide))
    (rule 6 7 2 2 961 897 901 773 773 965 (by unfold witness separates sameOff valid; decide))
    (rule 6 7 5 5 714 650 682 554 554 746 (by unfold witness separates sameOff valid; decide))
    (label 8)
    (dif 5 8 (by decide))
    (dif 6 8 (by decide))
    (rule 1 5 8 8 54 52 308 276 276 310 (by unfold witness separates sameOff valid; decide))
    (rule 1 6 8 8 707 705 961 897 897 963 (by unfold witness separates sameOff valid; decide))
    (rule 1 8 2 2 306 50 54 52 52 310 (by unfold witness separates sameOff valid; decide))
    (rule 1 8 5 5 278 276 308 52 52 310 (by unfold witness separates sameOff valid; decide))
    (rule 1 8 6 6 906 650 714 712 712 970 (by unfold witness separates sameOff valid; decide))
    (rule 2 5 8 8 54 50 306 274 274 310 (by unfold witness separates sameOff valid; decide))
    (rule 2 6 8 8 709 705 961 897 897 965 (by unfold witness separates sameOff valid; decide))
    (rule 2 8 1 1 308 52 54 50 50 310 (by unfold witness separates sameOff valid; decide))
    (rule 2 8 5 5 278 274 306 50 50 310 (by unfold witness separates sameOff valid; decide))
    (rule 2 8 6 6 901 897 961 705 705 965 (by unfold witness separates sameOff valid; decide))
    (rule 2 8 7 7 837 581 709 705 705 965 (by unfold witness separates sameOff valid; decide))
    (rule 5 6 8 8 737 705 961 897 897 993 (by unfold witness separates sameOff valid; decide))
    (rule 5 7 8 8 180 52 308 276 276 436 (by unfold witness separates sameOff valid; decide))
    (rule 5 8 6 6 929 897 961 705 705 993 (by unfold witness separates sameOff valid; decide))
    (rule 5 8 7 7 872 616 744 712 712 1000 (by unfold witness separates sameOff valid; decide))
    (rule 6 7 8 8 709 581 837 773 773 965 (by unfold witness separates sameOff valid; decide))
    (rule 6 8 1 1 968 712 714 650 650 970 (by unfold witness separates sameOff valid; decide))
    (rule 6 8 5 5 340 276 308 116 116 372 (by unfold witness separates sameOff valid; decide))
    (rule 7 8 2 2 961 705 709 581 581 965 (by unfold witness separates sameOff valid; decide))
    (rule 7 8 5 5 968 712 744 616 616 1000 (by unfold witness separates sameOff valid; decide))
    (rule 7 8 6 6 901 773 837 581 581 965 (by unfold witness separates sameOff valid; decide))
    (label 0)
    (dif 0 1 (by decide))
    (dif 0 5 (by decide))
    (rule 0 1 5 5 587 585 617 616 616 619 (by unfold witness separates sameOff valid; decide))
    (rule 0 1 6 6 651 650 714 713 713 715 (by unfold witness separates sameOff valid; decide))
    (rule 0 2 1 1 653 649 651 650 650 655 (by unfold witness separates sameOff valid; decide))
    (rule 0 2 5 5 589 585 617 616 616 621 (by unfold witness separates sameOff valid; decide))
    (rule 0 5 1 1 681 649 651 650 650 683 (by unfold witness separates sameOff valid; decide))
    (rule 0 5 7 7 617 616 744 713 713 745 (by unfold witness separates sameOff valid; decide))
    (rule 0 6 1 1 617 616 618 554 554 619 (by unfold witness separates sameOff valid; decide))
    (rule 0 7 5 5 651 650 682 554 554 683 (by unfold witness separates sameOff valid; decide))
    (rule 0 8 1 1 905 649 651 650 650 907 (by unfold witness separates sameOff valid; decide))
    (rule 0 8 5 5 841 585 617 616 616 873 (by unfold witness separates sameOff valid; decide))
    (rule 1 2 0 0 654 650 651 649 649 655 (by unfold witness separates sameOff valid; decide))
    (rule 1 5 0 0 682 650 651 649 649 683 (by unfold witness separates sameOff valid; decide))
    (rule 1 6 0 0 715 713 713 651 650 714 (by unfold witness separates sameOff valid; decide))
    (rule 1 8 0 0 906 650 651 649 649 907 (by unfold witness separates sameOff valid; decide))
    (rule 2 5 0 0 620 616 617 585 585 621 (by unfold witness separates sameOff valid; decide))
    (rule 5 7 0 0 745 713 713 617 616 744 (by unfold witness separates sameOff valid; decide))
    (rule 5 8 0 0 872 616 617 585 585 873 (by unfold witness separates sameOff valid; decide))
    (label 3)
    (dif 2 3 (by decide))
    (dif 3 8 (by decide))
    (rule 1 2 3 3 583 581 589 585 585 591 (by unfold witness separates sameOff valid; decide))
    (rule 1 3 2 2 587 585 589 581 581 591 (by unfold witness separates sameOff valid; decide))
    (rule 1 3 8 8 651 649 905 897 897 907 (by unfold witness separates sameOff valid; decide))
    (rule 1 8 3 3 899 897 905 649 649 907 (by unfold witness separates sameOff valid; decide))
    (rule 2 3 7 7 781 773 901 897 897 909 (by unfold witness separates sameOff valid; decide))
    (rule 2 3 8 8 653 649 905 897 897 909 (by unfold witness separates sameOff valid; decide))
    (rule 2 5 3 3 613 581 589 585 585 621 (by unfold witness separates sameOff valid; decide))
    (rule 2 7 3 3 717 713 713 589 581 709 (by unfold witness separates sameOff valid; decide))
    (rule 2 8 3 3 901 897 905 649 649 909 (by unfold witness separates sameOff valid; decide))
    (rule 3 5 2 2 617 585 589 581 581 621 (by unfold witness separates sameOff valid; decide))
    (rule 3 5 8 8 681 649 905 897 897 937 (by unfold witness separates sameOff valid; decide))
    (rule 3 6 8 8 589 581 837 773 773 845 (by unfold witness separates sameOff valid; decide))
    (rule 3 7 2 2 905 897 901 773 773 909 (by unfold witness separates sameOff valid; decide))
    (rule 3 8 2 2 841 585 589 581 581 845 (by unfold witness separates sameOff valid; decide))
    (rule 3 8 6 6 905 897 961 713 713 969 (by unfold witness separates sameOff valid; decide))
    (rule 5 8 3 3 929 897 905 649 649 937 (by unfold witness separates sameOff valid; decide))
    (rule 6 8 3 3 961 897 905 713 713 969 (by unfold witness separates sameOff valid; decide))
    (rule 0 3 2 5 617 616 616 609 581 589 (by unfold witness separates sameOff valid; decide))
    (rule 0 3 1 8 651 650 904 897 897 905 (by unfold witness separates sameOff valid; decide))
    (label 4)
    (rule 0 4 1 1 665 649 651 650 650 667 (by unfold witness separates sameOff valid; decide))
    (rule 0 4 5 5 601 585 617 616 616 633 (by unfold witness separates sameOff valid; decide))
    (rule 1 4 0 0 666 650 651 649 649 667 (by unfold witness separates sameOff valid; decide))
    (rule 1 4 6 6 666 650 714 712 712 730 (by unfold witness separates sameOff valid; decide))
    (rule 2 4 3 3 597 581 589 585 585 605 (by unfold witness separates sameOff valid; decide))
    (rule 2 4 7 7 789 773 901 897 897 917 (by unfold witness separates sameOff valid; decide))
    (rule 3 4 2 2 601 585 589 581 581 605 (by unfold witness separates sameOff valid; decide))
    (rule 3 4 8 8 665 649 905 897 897 921 (by unfold witness separates sameOff valid; decide))
    (rule 4 5 0 0 632 616 617 585 585 633 (by unfold witness separates sameOff valid; decide))
    (rule 4 5 7 7 632 616 744 712 712 760 (by unfold witness separates sameOff valid; decide))
    (rule 4 6 1 1 728 712 714 650 650 730 (by unfold witness separates sameOff valid; decide))
    (rule 4 6 8 8 721 705 961 897 897 977 (by unfold witness separates sameOff valid; decide))
    (rule 4 7 2 2 913 897 901 773 773 917 (by unfold witness separates sameOff valid; decide))
    (rule 4 7 5 5 728 712 744 616 616 760 (by unfold witness separates sameOff valid; decide))
    (rule 4 8 3 3 913 897 905 649 649 921 (by unfold witness separates sameOff valid; decide))
    (rule 4 8 6 6 913 897 961 705 705 977 (by unfold witness separates sameOff valid; decide))
    (label 9)
end Boundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open PetersenCutFormula PetersenScratch Suffix2770

def counted (g : Gate) := g.op.eval [false]

lemma withFirst (gs : List Gate) (o : Nat) (cl : CleanL 10 gs)
    (good : ∀ x : Fin 9 → Bool, vl gs (embed x) o = F x) : 13 ≤ nonNotCount gs := by
  let g : Gate := ⟨.or,[0,3]⟩
  let C : Circuit := ⟨g :: gs,o⟩
  have hf : FanInTwo C := by
    intro q h
    change q ∈ g :: gs at h
    rcases List.mem_cons.mp h with rfl | member
    · simp [g]
    · exact (clean_nok _ _ cl q member).1
  have he : circuitFun 9 C = F := by
    funext x
    have seed : runStep (List.ofFn x) g = List.ofFn (embed x) := by
      rw [embed,plug_list]; simp [g, runStep, GateOp.eval,List.getD]
    change (gs.foldl runStep (runStep (List.ofFn x) g)).getD o false = _
    rw [seed]
    exact good x
  have h := lower C hf he
  rw [binary_eq] at h
  have eq : nonNotCount C.gates = nonNotCount gs + 1 := by
    simp [C,g,nonNotCount,List.countP_cons,isNotGate]
  omega

def WeightOK (gs : List Gate) (o v : Nat) (w : Nat → Nat) : Prop :=
  (∀ j < 10, w j = if j = v then 1 else 0) ∧
  (∀ (i : Fin gs.length), w (10+i.val) = ((gs.get i).inputs.map w).sum) ∧ w o ≤ 1

lemma assemble (gs : List Gate) (o : Nat) (ho : o < 10 + gs.length) (cl : CleanL 10 gs)
    (len : gs.length ≤ 14) (binaryCount : nonNotCount gs = 13)
    (good : ∀ x : Fin 9 → Bool, vl gs (embed x) o = F x)
    (weights : ∀ v ∈ [4,6,7], ∃ w, WeightOK gs o v w) :
    ∃ D : Circuit, FanInTwo D ∧ NestedCover.ReadsBack 10 D ∧ D.gates.length = 14 ∧
      D.gates.countP counted = 1 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) = F x) ∧
      ∀ v ∈ [4,6,7], ∃ w, WeightOK D.gates D.output v w := by
  have fan : FanInTwo ⟨gs,o⟩ := fun q h => (clean_nok _ _ cl q h).1
  have back : NestedCover.ReadsBack 10 ⟨gs,o⟩ := by
    intro i hi
    change ∀ j ∈ (gs.getD i _).inputs, j < 10+i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact (cl i gs[i] (List.getElem?_eq_getElem hi)).lt
  have eval (x : Fin 9 → Bool) : (Circuit.mk gs o).eval (List.ofFn x ++ [x 0 || x 3]) = F x := by
    rw [←plug_list]
    exact good x
  have cnt := budget gs (fun q h => (fan q h).1)
  rw [binary_eq,binaryCount] at cnt
  change 13 + gs.countP counted = gs.length at cnt
  by_cases eq : gs.length = 14
  · exact ⟨⟨gs,o⟩,fan,back,eq,by change gs.countP counted = 1; omega,eval,weights⟩
  have old : gs.length = 13 := by omega
  let pad : Gate := ⟨.not,[]⟩
  let D : Circuit := ⟨gs ++ [pad],o⟩
  have hfan : FanInTwo D := by
    intro q h
    change q ∈ gs ++ [pad] at h
    rcases List.mem_append.mp h with h | h
    · exact fan q h
    · have he : q = pad := List.mem_singleton.mp h
      simp [he,pad]
  have lengthD : D.gates.length = 14 := by simp [D,old]
  refine ⟨D,hfan,?_,lengthD,?_,?_,?_⟩
  · intro i hi
    change ∀ j ∈ ((gs ++ [pad]).getD i _).inputs, j < 10+i
    rw [List.getD_eq_getElem?_getD]
    by_cases h : i < gs.length
    · rw [List.getElem?_append_left h,List.getElem?_eq_getElem h]
      exact (cl i gs[i] (List.getElem?_eq_getElem h)).lt
    · have ie : i = gs.length := by omega
      simp [ie,List.getElem?_append_right,pad]
  · change (gs ++ [pad]).countP counted = 1
    have h : gs.countP counted = 0 := by omega
    simp [List.countP_append,h,List.countP_cons,pad,counted,GateOp.eval]
  · intro x
    let w := List.ofFn x ++ [x 0 || x 3]
    change (wiresFrom (gs ++ [pad]) w).getD o false = _
    rw [wiresFrom_append,getD_wiresFrom]
    · exact eval x
    · simpa [w,length_wiresFrom] using ho
  · intro v hv
    obtain ⟨w,initial,steps,final⟩ := weights v hv
    let w' (j : Nat) := if j < 10+gs.length then w j else 0
    refine ⟨w',fun j hj => (if_pos (by omega : j < 10+gs.length)).trans (initial j hj),?_,?_⟩
    · intro i
      by_cases h : i.val < gs.length
      · let k : Fin gs.length := ⟨i.val,h⟩
        have gateEq : D.gates.get i = gs.get k :=
          Option.some.inj ((List.getElem?_eq_getElem i.isLt).symm.trans
            ((List.getElem?_append_left h).trans (List.getElem?_eq_getElem h)))
        rw [gateEq]
        change (if 10+i.val < 10+gs.length then w _ else 0) = _
        rw [if_pos (by omega),steps k]
        congr 1
        apply List.map_congr_left
        intro j hj
        exact (if_pos ((cl i.val (gs.get k) (List.getElem?_eq_getElem h)).lt j hj |>.trans (by omega))).symm
      · have ie : i.val = gs.length := by have := i.isLt; omega
        have gateEq : D.gates.get i = pad := by
          apply Option.some.inj
          have hi := (List.getElem?_eq_getElem i.isLt).symm
          exact hi.trans (by change (gs ++ [pad])[i.val]? = _; simp [ie,List.getElem?_append_right])
        rw [gateEq]
        simp [ie,w',pad]
    · exact (show w' o = w o from if_pos ho) ▸ final

lemma normalSuffix (C : Circuit) (hf : FanInTwo C) (len : C.gates.length = 15)
    (first : C.gates[0]? = some ⟨.or,[0,3]⟩) (one : C.gates.countP counted = 1)
    (compute : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ NestedCover.ReadsBack 10 D ∧ D.gates.length = 14 ∧
      D.gates.countP counted = 1 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) = F x) ∧
      ∀ v ∈ [4,6,7], ∃ w, WeightOK D.gates D.output v w := by
  obtain ⟨D,fan,binCap,sz,agree,pairs,still⟩ :=
    suffix_data lower C hf len first (le_of_eq one.symm) compute
  have dep (i : Fin 10) := dep_of_pair (pairs i)
  have nc := dep_nc (dep 0)
  obtain ⟨gs,o,L,bound,lengthBound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have ho : o < 10 + gs.length := by
    by_contra! bad
    obtain ⟨x,y,h⟩ := L.ncv nc
    exact h ((vl_beyond gs x o bad).trans (vl_beyond gs y o bad).symm)
  let out : Fin (10+gs.length) := ⟨o,ho⟩
  have live := least_read_edge_live L nc dep still ho
  rw [binary_eq] at binCap
  have cap := bound.trans binCap
  have branches := fourForksOfBudget L.hcl out live cap
  obtain ⟨label,loc,last,codes⟩ := normalizedCuts L.hcl out live branches
  have computes (x : Fin 10 → Bool) (hx : Boundary.valid x) :
      vl gs x out.val = Conflict2770.value x := (L.hev x).trans (agree x hx)
  have ranks := Boundary.lastRanks label (fun e he eq => Conflict2770.boundaryConflict L.hcl out live
    (predecessors_nodup L nc) computes e he ((loc _ _).mp eq)) (by
      intro t
      obtain ⟨code,lo,hi⟩ := codes t
      exact ⟨code, lo, fun x y vx vy rest same =>
        (computes x vx).symm.trans ((hi x y rest same).trans (computes y vy))⟩)
  have good (x : Fin 9 → Bool) : vl gs (embed x) o = F x := by
    have hx : Boundary.valid (embed x) := by rfl
    exact computes (embed x) hx
  apply assemble gs o ho L.hcl (by omega) (Nat.le_antisymm cap (withFirst gs o L.hcl good)) good
  intro v hv
  have short (i : Fin 10) (hi : label i = 4) : ∃ w, WeightOK gs o i.val w := by
    let w (a : Nat) := occurrences i (wireFormula i gs a)
    refine ⟨w,?_,?_,?_⟩
    · intro j hj
      have he := wireFormula_count_input i gs i ⟨j,hj⟩
      simpa only [Fin.ext_iff] using he
    · intro j
      exact wireFormula_count_gate i L.hcl i (List.getElem?_eq_getElem j.isLt)
    · have h := firstInputBoundary_occurrences_le_one L.hcl out live (predecessors_nodup L nc) i i
      rw [last i hi] at h
      exact h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact short 4 ranks.1
  · exact short 6 ranks.2.1
  · exact short 7 ranks.2.2

end PEqualNP.Outside.L_meta_4721

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_4721 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.gates.length = (15 : ℕ) → x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false]) x1.gates = (1 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6) = ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (PEqualNP.MetaComplexity.tableIndex x6 / (64 : ℕ)) (0 : ℕ)).testBit (PEqualNP.MetaComplexity.tableIndex x6 % (64 : ℕ))) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x7 ∧ x7.gates.length = (14 : ℕ) ∧ List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op.eval [Bool.false]) x7.gates = (1 : ℕ) ∧ (∀ (x8 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ))]) = ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (PEqualNP.MetaComplexity.tableIndex x8 / (64 : ℕ)) (0 : ℕ)).testBit (PEqualNP.MetaComplexity.tableIndex x8 % (64 : ℕ))) ∧ ∀ x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], ∃ (x10 : ℕ → ℕ), (∀ x11 < (10 : ℕ), x10 x11 = if x11 = x8 then (1 : ℕ) else (0 : ℕ)) ∧ (∀ (x11 : Fin x7.gates.length), x10 ((10 : ℕ) + ↑x11) = (List.map x10 (x7.gates.get x11).inputs).sum) ∧ x10 x7.output ≤ (1 : ℕ) := by
  intro C fan len first one agrees
  have table : ∀ x : Fin 9 → Bool, ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (PEqualNP.MetaComplexity.tableIndex x / (64 : ℕ)) (0 : ℕ)).testBit (PEqualNP.MetaComplexity.tableIndex x % (64 : ℕ)) = PEqualNP.Outside.L_meta_4721.Suffix2770.F x := by decide +kernel
  obtain ⟨D,ff,back,size,cn,ag,ws⟩ := PEqualNP.Outside.L_meta_4721.normalSuffix C fan len first one
    (funext fun x => (agrees x).trans (table x))
  exact ⟨D,ff,back,size,cn,fun x => (ag x).trans (table x).symm,ws⟩
