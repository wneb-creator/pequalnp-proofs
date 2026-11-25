import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3885
-- The binary gate bound is due to MohammadESteitieh in L-meta-2917.
namespace Binary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
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
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y
theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
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
    exact least_gate_inputs_nodup least nonnull _
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
lemma reject_8_1 : solve 7 [8,1] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_1 : solve 7 [9,1] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_1 : solve 7 [24,1] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_1 : solve 7 [25,1] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1 : solve 8 [1] = false := by
  apply split_solve 7 [1] (102,8) [8,9,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_8_1, reject_9_1, reject_24_1, reject_25_1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_16_9 : solve 7 [16,9] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_9 : solve 7 [17,9] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_9 : solve 7 [24,9] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_9 : solve 7 [25,9] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9 : solve 8 [9] = false := by
  apply split_solve 7 [9] (102,16) [16,17,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_16_9, reject_17_9, reject_24_9, reject_25_9]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_8_17 : solve 7 [8,17] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_9_17 : solve 7 [9,17] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_24_17 : solve 7 [24,17] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_25_17 : solve 7 [25,17] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17 : solve 8 [17] = false := by
  apply split_solve 7 [17] (102,8) [8,9,24,25] (by decide +kernel) (by decide +kernel)
  simp only [List.any_cons, List.any_nil, Bool.false_or, reject_8_17, reject_9_17, reject_24_17, reject_25_17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_1_25 : solve 7 [1,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_5_25 : solve 7 [5,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_17_25 : solve 7 [17,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_21_25 : solve 7 [21,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_33_25 : solve 7 [33,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_37_25 : solve 7 [37,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_49_25 : solve 7 [49,25] = false := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reject_53_25 : solve 7 [53,25] = false := by
  decide +kernel
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
lemma petersen_binary_bound (C : Circuit) (hfan : FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = petersenF x)
    (small : nonNotCount C.gates ≤ 13) : False := by
  obtain ⟨gs, o, L, budget⟩ := Readers.least_with_budget C hfan computes petersen_nonconstant
  have bound := budget.trans small
  obtain ⟨s, hs, once⟩ := terminal_class L bound
  obtain ⟨h, hh⟩ := Probes.layout_exists s hs
  obtain ⟨l, valid, safe⟩ := Probes.ledger_for_circuit L h (fun t => once _ (hh t))
  exact Probes.no_ledger bound valid safe CoverCheck.checked
end Binary
-- The live wire and restriction proofs follow PressF10 in L-meta-1667 and odinfree in L-meta-2149.
-- The rectangle argument uses the one-fork lemma from JLDC in L-meta-2303.
-- If the first gate negates an input, fourteen binary gates leave no further negations.
-- All nine positive inputs must then be live. The negated input can be unused.
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero∧a≠one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (target : Sig) : Nat → Nat → Finset Sig → Prop:=fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)),(proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target}:=fun M stop unary binary => @stop  h0
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
theorem Live.induct {target : Sig} {M : (Nat → Nat → Finset Sig → Prop)} {k t S} (h : Live target k t S)
  (stop : proper target → M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → Live target k t (insert (neg a) U) → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → Live target k t (insert (bin d a b) U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S∧M k t S)
  (fun h0 => ⟨@Live.stop target  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
theorem Live.recurse {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig) (proof : Live target k t S),Prop}
  (stop : ∀ (h0 : proper target),M 0 0 {target} (@Live.stop target  h0))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@Live.unary target k t U a h0 h1 h2))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@Live.binary target k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h : Live target k t S) : M k t S h:=by
  have r:=Live.induct (M:=fun k t S => ∀ hh : Live target k t S,M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h
theorem Live.zeroSet {T t S} (h : Live T 0 t S) : S={T}:=by
  have hh:=h (fun k _ W => k=0 → W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live target k t S) : t ≤ k∧S.card+t ≤ k+1:=by
  induction h using Live.recurse with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop:=v ∈ w∨¬proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma bin_laws (a : Sig) :
    bin false a one=a∧bin true a zero=a ∧
    bin false a zero=zero∧bin true a one=one ∧
    bin false a a=a∧bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
lemma neg_laws : neg zero=one∧neg one=zero:=by simp [neg,zero,one]
lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a=zero∨a=one∨a ∈ w∧proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w,proper a∧z=neg a) ∨
  (∃ d a b,a ∈ w∧b ∈ w∧proper a∧proper b∧a≠b∧z=bin d a b)
lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b)∨witness w (bin d a b):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z∨witness w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧Live target k' t' S'∧∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w∨a=z:=by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (neg a)
        have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U:=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U):=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
lemma bit_zero (i) : bit i zero=false:=by simp [bit,zero]
lemma bit_one (i) : bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type):=R → Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat:=(xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool∨Constant v
def supply {R} (pool xs : List (Wire R)):=∀ a ∈ xs,Available pool a
def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop:=fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
theorem Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots:=fun M start one two => @start
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank):=fun M start one two => @one p bank a (h0 M start one two) h1
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank):=fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
theorem Reach.induct {R} {roots : List (Wire R)} {M : (Nat → List (Wire R) → Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},Reach roots p bank → M p bank → Available bank a → M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),Reach roots p bank → M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank∧M p bank)
  (⟨@Reach.start R roots  ,@start  ⟩)
  (@fun p bank a h0 h1 => ⟨@Reach.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
  (@fun p bank a b op h0 h1 h2 => ⟨@Reach.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
theorem Reach.recurse {R} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)) (proof : Reach roots p bank),Prop}
  (start : M 0 roots (@Reach.start R roots  ))
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a),M (p+1) (inv a :: bank) (@Reach.one R roots p bank a h0 h2))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a) (h3 : Available bank b),M (p+1) (combine op a b :: bank) (@Reach.two R roots p bank a b op h0 h2 h3))
  {p bank} (h : Reach roots p bank) : M p bank h:=by
  have r:=Reach.induct (M:=fun p bank => ∀ hh : Reach roots p bank,M p bank hh) h
    (fun  _ => @start  )
    (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
    (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
  exact r h
def kept {α : Type} (save : Bool) (x : α) (xs : List α):=if save then x::xs else xs
def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop:=fun s ws =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → M s xs → M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),M s (inv a :: kept save a rest) → M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) →
  M s ws
theorem Run.stop {R} {goal : Wire R}   : Run goal 0 [goal]:=fun M stop perm one two => @stop
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
theorem Run.induct {R} {goal : Wire R} {M : (Nat → List (Wire R) → Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → Run goal s xs → M s xs → M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),Run goal s (inv a :: kept save a rest) → M s (inv a :: kept save a rest) → M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),Run goal s (combine op a b :: kept ka a (kept kb b rest)) → M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws∧M s ws)
  (⟨@Run.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
theorem Run.recurse {R} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)) (proof : Run goal s ws),Prop}
  (stop : M 0 [goal] (@Run.stop R goal  ))
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) (ih : M s xs h1),M s zs (@Run.perm R goal s xs zs h0 h1))
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) h0),M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) h0),M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
  {s ws} (h : Run goal s ws) : M s ws h:=by
  have r:=Run.induct (M:=fun s ws => ∀ hh : Run goal s ws,M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a+mass xs:=by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs):=by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a):=by
  obtain ⟨v,rfl⟩:=h
  exact ⟨!v,rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b):=by
  obtain ⟨v,rfl⟩:=h
  obtain ⟨w,rfl⟩:=g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a∨Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b):=by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next,Reach roots q next∧Available next (inv a) ∧
        (∀ v,Available bank v → Available next v)∧q+cost a ≤ p+1+cost (inv a):=by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩
theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next,Reach roots q next∧Available next (combine op a b) ∧
        (∀ v,Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b):=by
  classical
  by_cases c : Constant a∨Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a:=fun h => c (Or.inl h)
    have cb : ¬Constant b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a∨x∈xs:=by cases k <;> simp_all [kept]
theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next,Reach roots q next∧Available next goal∧q+mass ws ≤ p+s:=by
  classical
  induction h using Run.recurse generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a (kept kb b rest) ka
    have hlen':=mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)):=by
  cases k <;> simp [kept]
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)):=by
  induction h using Run.recurse with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih
theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs,Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L+mass (ws.map (restrictRows rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩:=contraction nc (restrict_run rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f)=f r:=by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v)=v:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f)=f:=by
  funext r
  exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a)=inv (observe a):=by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b)=combine d (observe a) (observe b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f=kept d (f a) (l.map f):=by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup:=by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [kept]
theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset=S) : Run (observe T) k (v.map observe):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=kept save a rest
    have er : rest.toFinset=U.erase a:=by simp [rest]
    have hm : a ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have ht : tail.toFinset=U:=by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=kept_nd save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=kept kb b rest
    let tail:=kept ka a mid
    have er : rest.toFinset=(U.erase a).erase b:=by simp [rest]
    have ar : a ∉ rest:=by simp [rest]
    have br : b ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have bm:=kept_nd kb b rest hr br
    have am : a ∉ mid:=by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd:=kept_nd ka a mid bm am
    have ht : tail.toFinset=U:=by
      change (kept ka a (kept kb b rest)).toFinset=U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f)=neg (table f):=by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g)=bin d (table f) (table g):=by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]
theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a)∨witness w (neg a):=by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z∨witness w z) (hs : ∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1∧Live T k' t' S'∧∀ a ∈ S',a ∈ w:=by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S,a ∈ bank.map table) :
    ∃ l v U,l ≤ p+k∧Live T l v U∧∀ a ∈ U,a ∈ roots.map table:=by
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S,k ≤ p∧Live T k t S∧∀ a ∈ S,a ∈ roots:=by
  have hm:=available_rep hit
  rw [table_observe] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩:=reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T≠bit s T) : ∃ a ∈ S,bit r a≠bit s a:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S,v ∈ roots) (r s : Row) (diff : bit r T≠bit s T)
    (isolated : ∀ v ∈ roots,v≠a → bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩:=live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def oldSeed : Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def sample (r : Row) (j : Fin 9):=bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
theorem edge_table : ∀ r : Row,bit r graph=edge (sample r):=by decide +kernel
theorem graph_proper : proper graph:=by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero)=inputs:=rfl
theorem sampled (r : Row) : List.ofFn (sample r)=inputs.map (bit r):=by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false:=by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l,execute gs ws=ws ++ l:=by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩:=ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def neighbor (i : Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
def rename (f : Row → Row) (a : Sig):=table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a)=bit (f r) a:=bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a)=restrictRows f (observe a):=by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a)=neg (rename f a):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a))=bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b)=bin d (rename f a) (rename f b):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b))=bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f):=by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero=zero∧rename f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)):=by
  have inj:=rename_inj f onto
  obtain ⟨fz,fo⟩:=rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.recurse with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T=true) (negRow : bit s T=false) :
    ∃ a ∈ S,bit r a=true∧bit s a=false:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩:=ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank,Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row,bit r T≠bit s T∧∀ v ∈ roots,v≠a → bit r v=bit s v
theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots,Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1):=by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩:=reach_live hp h ha
  have he : roots.toFinset=S:=by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:=essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v):=by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v:=by
    have avail : Available ([] : List (Wire Row)) (observe v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b)=mass a+mass b:=by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs,Constant x) :
    mass xs=xs.length:=by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T=G)
    (covered : ∀ a ∈ roots,Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles,Essential T roots a)
    (constant : ∀ a ∈ singles,Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L+singles.card):=by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live pT hh ha
  have subS : singles ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:=necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front:=singles.toList ++ (S \ singles).toList
  have nd : front.Nodup:=by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':=list_run run front nd fe
  have gc : restrictRows r (observe T)=observe G:=(observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)):=by
    simp only [front,List.map_append,mass_append]
    let xs:=(singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs,Constant v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs+_
    rw [sz]
    omega
  omega
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset:=by
  classical
  intro k t hk h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    have mem : T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      have nk:=kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len : (childOne ws a keep).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup:=by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_
      simp [ke]
    have sc:=(live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true∧bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws=BitVec.allOnes width:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩:=live_row_difference h (show bit (r i) T≠bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩:=mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n:=by
  apply cover_sound h rfl correct
  intro hh
  have eq:=of_decide_eq_true hh
  have bound:=(live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank,Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig):=a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m:=masked d a
  m==zero||m==d||(pool.map (masked d)).any (fun v => v==m)
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=masked d b) :
    restrictRows f (observe a)=restrictRows f (observe b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=zero) : restrictRows f (observe a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=d) : restrictRows f (observe a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool,Available bank (restrictRows f (observe a))
theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r,bit (f r) d=true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a=true) : Available bank (restrictRows f (observe a)):=by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice:=Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1&&(c.1==2||availableB d pool c.2.2)
theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r,bit (f r) d=true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c=true) :
    ∃ next,Reach roots (q+1) next∧poolSupply f next (choiceVal c :: pool):=by
  have ok : availableB d pool c.2.1=true∧(c.1==2||availableB d pool c.2.2)=true:=by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha:=availableB_sound dom hs ok.1
  let z:=restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank):=by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz':=Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w)=combine b (restrictRows f v) (restrictRows f w):=by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)
def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r,bit (f r) d=true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs=some result) :
    ∃ next,Reach roots (q+cs.length) next∧poolSupply f next result:=by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩:=pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩:=ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig):=masked d a==zero||masked d a==d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r,bit (f r) d=true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)):=by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)):=by
        have hh : masked d a=zero∨masked d a=d:=by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d))&&ws.all (availableB d pool)
theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs=some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws=true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
  obtain ⟨bank,hr,hs⟩:=makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:=cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b:=projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo:=count_constants dom ws
  have hu:=ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move:=Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row:=Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig):=(m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val)=bit (shifted d r) a:=by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y : Bool) : (p&&x||!p&&y)=(if p then x else y):=by cases p <;> simp
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a)=bit (rowMove m r) a:=by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row):=ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig):=ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a)=bit (movedRow ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a=rename (movedRow ms) a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig):=w==zero||w==one||roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w=true) :
    Available (roots.map observe) (observe w):=by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T==G&&raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G=true) :
    rename (movedRow ms) T=G ∧
    ∀ a ∈ raw,Available (base.map observe) (observe (rename (movedRow ms) a)):=by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G=true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G=true)
    (all : movedWord ms d=one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  have obs : restrictRows (movedRow ms) (observe T)=observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs=true) : Essential T roots a:=by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)
theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs=true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:=essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound:=(live_size run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G&&checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1==zero||movedWord ms a.1==one)
theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs=true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩:=map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat):=(selected m).map Prod.snd
def vertex (m j : Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x:=vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig):=T != zero&&T != one
theorem proper_of (T : Sig) (h : properB T=true) : proper T:=by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs:=graphPairs m hints
  properB (graphGoal m)&&checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L=true) :
    Lower (vars m) (graphGoal m) L:=by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  let count:=(xs.map Prod.fst).toFinset.card
  properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs&&decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior=true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩:=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  change (((properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old)&&properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps=true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L:=by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q):=by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1==q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1==q) e=true:=List.find?_some (p:=fun a : Nat × Nat => a.1==q) (a:=e) h
    have eq : e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (c : BoundPool) : Sig:=c.1
abbrev BoundPool.bound (c : BoundPool) : Nat:=c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat:=c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig:=c.2.2.2
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r,bit (f r) c.domain=true)∧¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws,Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank∧poolSupply f bank c.wires∧True
theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs=some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩:=by
  obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
  obtain ⟨bank,hr,hs⟩:=makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest,availableB c.domain c.wires a=true)
    (buy : if paid then choiceOK c.domain c.wires choice=true
       else availableB c.domain c.wires (choiceVal choice)=true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid
  let ws:=choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n=c.paid+paid.toNat) : False:=by
    have covered : supply out ((ws.map observe).map (restrictRows f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
      exact zs _ ha
    have b:=projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm:=count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩:=pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z:=choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires))&&(!extra||choiceOK c.domain c.wires op)
theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op=true) :
    Impossible T k (choiceVal op::rest).toFinset:=by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L=some c) : ValidPool raw T c:=by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h
    change some _=some c at h
    injection h with h
    subst c
    exact build_valid slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val=bit (r i) v:=by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals:=(ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i,bit (r i) T=true∧bit (s i) T=false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s):=by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor):=x.2=pairSig r s x.1
def dneg (x : Decor) : Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b)=if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x):=by
  change x.2=_ at h
  simp only [faithful,dneg,pairSig,ofRows_neg,h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y):=by
  change x.2=_ at hx
  change y.2=_ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor:=(zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j=(ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j=(ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws,faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws,faithful r s v) :
    ∀ v ∈ decodeBank n bits ws,faithful r s v:=by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:=List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
theorem coordinate1 : ∀ r : Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
theorem coordinate2 : ∀ r : Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
theorem coordinate3 : ∀ r : Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
theorem coordinate4 : ∀ r : Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
theorem coordinate5 : ∀ r : Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
theorem coordinate6 : ∀ r : Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
theorem coordinate7 : ∀ r : Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
theorem coordinate8 : ∀ r : Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9∧a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q,faithful (asRow p) (asRow q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:=selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m)=(liftGoal m v).getLsbD i.val:=by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val=((if m.testBit j then v j else 0) : Bits).getLsbD i.val:=bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v,faithful r s a) :
    (coverage d v).1=covered d (pairSig r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1)=column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)):=by
  cases keep
  · change (coverage d (ws.erase a)).1=takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)):=by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1=takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b : List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws:=choiceVal op::rest
  (links (keySet ws)).any (sameWords ws)||pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair:=Cov × Cov
def preCov (ws : List Decor) : CovPair:=(coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool):=if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d=coverage d ws:=by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb:=by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor):=codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice:=(op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1=choiceVal (movedChoice op a b):=by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b):=by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len>cap then true else
    let d:=len==cap
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb=true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz:=(live_size h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep:=cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap:=by omega
  rw [ce] at sep
  let d:=child.length==cap
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap)=(child.length==cap):=by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length=cap)) (pairSig r s) child=BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by simp [sep]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  have val:=moved_full op a b
  change z.1=_ at val
  change Live T k t child.toFinset at h
  have nd':=ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false&&evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false&&testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs&&testAll ctx bs
theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true∨testPair ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d=true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v↔(w=a∧k=true)∨w∈v:=by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k↔w∈v∧(w≠a∨k=true):=by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst∧(v≠a.1∨ka=true)∧(un=true∨v≠b.1∨kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset=(childOne (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset=(childTwo v b a d kb ka).toFinset:=by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws=true) :
    Impossible T cap (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap:=by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d=true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move):=inputs.all (fun a => movedWord p (movedWord q a)==a)
theorem composed_id {p q} (h : composedOK p q=true) (r : Row) :
    movedRow q (movedRow p r)=r:=by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T==T)&&composedOK p p.reverse&&composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run:=live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def IndexTree (α : Type):=List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α:=xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α:=List.append a b
def IndexTree.read {α} (tree : IndexTree α) (i : Nat):=(show List α from tree)[i]?
def IndexTree.values {α} (tree : IndexTree α) : List α:=tree
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
def Forest:=(Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat:=c.1
def Forest.cap (c : Forest) : Nat:=c.2.1
def Forest.samples (c : Forest) : Nat → Bits × Bits:=c.2.2.1
def Forest.cols (c : Forest) : IndexTree ColumnInfo:=c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat):=c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat → Packing:=c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat → Nat → Option (Nat × Nat):=c.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:=by
  have base:=raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha
def targetOf (g : Forest):=chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m)=(chartSamples m v).getLsbD i.val:=by
  by_cases e : m=1023
  · have u:=asRow_bit v i (0 : Fin 9)
    have w:=asRow_bit v i (1 : Fin 9)
    have h:=bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val=(v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val=(v 1).getLsbD i.val at w
    have seedEq : oldSeed=inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p=BitVec.allOnes 768) (hq : chartSamples m q=0) :
    properPairs (chartGoal m) (asRow p) (asRow q):=by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1==1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def storedDepth (_g : Forest) (depth : Nat):=depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw:=wiresOf g
  let (_,depth,_,_,_,_,_,data):=g.levels k
  let len:=10*storedDepth g depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i*width) width
  let stored:=recp &&& ((1 <<< len)-1)
  let ops:=stored
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid=some c) :
    ValidPool (vars g.mask) (targetOf g) c:=by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (earlier : ∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair=some out) :
    Impossible (targetOf g) k out.toFinset:=by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let values:=ws.map Prod.fst
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup&&!(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1,Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i=true) : Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN:=checked.1.1
  have hT : targetOf g ∉ stateSet g k i:=by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0:=by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset=S at h
    rw [h.zeroSet] at he
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n)&&block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true:=by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true:=by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1=true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2)==0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : checkedTables g top) :
    ∀ k ≤ top,∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1)&&sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws=true) : Impossible (targetOf g) k ws.toFinset:=by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask)=true) (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem lower_discard {mask cap prior ci hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck mask ci prior=true)
    (hp : properB (chartGoal mask)=true)
    (ess : checkEssential (chartGoal mask) (vars mask) (graphPairs mask hints)=true)
    (all : (graphPairs mask hints).map Prod.fst=vars mask)
    (nd : (vars mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (vars mask) (vars mask)=true) :
    Lower (vars mask) (chartGoal mask) (cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2)=true) :
    Known (extendKnown old L relabels):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known []:=by simp [Known]
def lanePlace (v : Nat) (upper : Nat):=2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v=lanePlace (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v=lanePlace (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v=lanePlace (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs=combineLanes (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs=combineLanes (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs=combineLanes (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat=combineLanes (fun _ => a) xs:=by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed : Nat):=((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i)=true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i:=by omega
      have ge : ¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne : a.toNat≠2^768-1:=by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
    have hi' : i < xs.length+1:=hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769:=by omega
      have di : 769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig:=Nat × Nat
abbrev PackedCov:=Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs)=combineLanes (fun x => column d (s x)) xs:=by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat):=c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a:=contextWire c i
  let b:=contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1==0)||f x)&&onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0:=by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1≠0:=by
        intro he
        have at0:=congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:=Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat):=b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i=packedSig (fun c => (contextWire c i).2) xs:=by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero||m==p.domain||(p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x=availableMasked p (masked p.domain x):=rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p+constantLoss p a keep:=by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un||kb) ≤
    (opKeep un ka kb a b ws).countP p:=by
  have h1:=lossBound p ws a ka
  have h2:=lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool:=BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p:=s.1
  let un:=op==2
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let z:=choiceVal (movedChoice op a b)
  let zm:=masked p.domain z
  let zc:=isMaskedConstant p.domain z
  let cm:=s.2.1 - constantLoss const a ka - constantLoss const b (un||kb)+zc.toNat
  let free:=zc||zm==masked p.domain a.1||zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true:=by
  let z:=choiceVal (movedChoice op a b)
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let free:=isMaskedConstant p.domain z||masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest:=opKeep (op==2) ka kb a b ws
  have ck:=keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav:=List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true:=by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat:=by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true:=by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const+if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true:=by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1:=by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  have closed:=fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length∧j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true:=by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n-(if ka then 0 else 1)-(if un||kb then 0 else 1))
  if len>k then true else
    let d:=len==k
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true:=by
  let len:=1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d:=len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)):=by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (makeBatch k n xs) i
    let b:=laneWire (makeBatch k n xs) j
    let cov:=if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.1 d) xs:=by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a=_:=laneWire_at k n xs hi
    have cb : b=_:=laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f:=batchMove b xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false&&batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0&&batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js&&batchRows b xs js
theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true:=by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true:=by
  have all:=batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q])=xs[q].2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T : Sig) (c : NodeContext) :=
  let ws:=c.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i=(prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)):=rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat),start ≤ i → i < start+n → nodeVerified g k i=true) :
    block g k start n=true:=by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar&&prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs:=contexts g k start n
  let b:=makeBatch k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true:=by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:=List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true:=by
  let xs:=contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true:=by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok:=rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true:=by
  apply makeBlock
  intro i lo hi
  let xs:=contexts g k start n
  have hm : contextOf g k i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ha : xs[q].2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d∧boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true:=by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v:=rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true∧boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d∧cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true:=by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v:=block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d∧listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat:=0xf
def g15l3 : Packing:=(1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo:=(.leaf [])
def g15autos : Array (List Nat):=Array.mk [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest:=⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat:=0x84001e90fd02fd01fa00
def g31l5 : Packing:=(3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat:=0x11a20bf
def g31l6 : Packing:=(1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest:=⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g111d6 (i : Nat) : Nat:=0x120ff
def g111l6 : Packing:=(1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits):=Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat):=Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest:=⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def key189l7 (i : Nat) : Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat:=0x82000f487f40bfa03fa00
def g189l6 : Packing:=(3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat:=0x1f5859bf
def g189l7 : Packing:=(1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits):=Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest:=⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def key191l10 (i : Nat) : Nat:=0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat:=0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat:=0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat:=0x2c
def g191d6 (i : Nat) : Nat:=0x47d6448788a00
def g191l6 : Packing:=(1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat:=0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing:=(28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat:=0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing:=(100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat:=0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing:=(12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat:=0x1f3c11ff
def g191l10 : Packing:=(1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits):=Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest:=⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def key383l12 (i : Nat) : Nat:=0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat:=0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat:=0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat:=0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat:=0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing:=(25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat:=0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing:=(91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat:=0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing:=(41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat:=0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing:=(6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat:=0x11b280e4ff
def g383l12 : Packing:=(1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits):=Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest:=⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1:=size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat):=[]
def known3:=extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3:=extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2:=size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat):=[]
def known7:=extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7:=extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true:=by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1=true:=s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0=true)
  · exact (rfl : block g15 1 0 0=true)
  · exact (rfl : block g15 2 0 0=true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15:=extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15:=extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3:=size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat):=[]
def known45:=extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45:=extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3:=size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat):=[]
def known51:=extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51:=extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true:=by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3=true:=(@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true:=by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1=true:=s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact (rfl : block g31 4 0 0=true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31:=extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31:=extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (mask:=47) (cap:=4) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47:=extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47:=extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (mask:=55) (cap:=4) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55:=extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55:=extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (mask:=63) (cap:=7) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63:=extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63:=extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1=true:=s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact (rfl : block g111 5 0 0=true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111:=extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111:=extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (mask:=119) (cap:=5) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119:=extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119:=extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3=true:=(@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1=true:=s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0=true)
  · exact (rfl : block g189 1 0 0=true)
  · exact (rfl : block g189 2 0 0=true)
  · exact (rfl : block g189 3 0 0=true)
  · exact (rfl : block g189 4 0 0=true)
  · exact (rfl : block g189 5 0 0=true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189:=extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189:=extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5:=size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat):=[]
def known250:=extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250:=extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (mask:=127) (cap:=8) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127:=extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127:=extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1=true:=s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28=true:=(@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100=true:=(@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12=true:=(@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1=true:=s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0=true)
  · exact (rfl : block g191 1 0 0=true)
  · exact (rfl : block g191 2 0 0=true)
  · exact (rfl : block g191 3 0 0=true)
  · exact (rfl : block g191 4 0 0=true)
  · exact (rfl : block g191 5 0 0=true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191:=extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191:=extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (mask:=251) (cap:=7) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251:=extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251:=extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (mask:=255) (cap:=11) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255:=extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255:=extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25=true:=(@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true:=by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91=true:=(@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true:=by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41=true:=(@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6=true:=(@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true:=by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1=true:=s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0=true)
  · exact (rfl : block g383 1 0 0=true)
  · exact (rfl : block g383 2 0 0=true)
  · exact (rfl : block g383 3 0 0=true)
  · exact (rfl : block g383 4 0 0=true)
  · exact (rfl : block g383 5 0 0=true)
  · exact (rfl : block g383 6 0 0=true)
  · exact (rfl : block g383 7 0 0=true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383:=extendKnown_ok valid255 low383 (by decide +kernel)
def deadsamples : Array (Bits × Bits) := #[(0xfffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000ffffffe00000000000007ffffff00000000000003ffffff80000000000001ffffffc0000007ffffffffffffe00000000000007ffffff,0xa8486415090c82a121905424320a8486415090c82a121905424320a8486415090c82a121905424320a8486415090c82a121905424320a8486415090c82a121905424320a8486415090c82a121905424320a8486415090c82a121905424320a84),(0xfffffffffe0000003ffffffffffffffffffffffffffc000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000000000ffffffe0000000000000000000000000000000003fffffffffffff,0x23780a046f01408de02811bc05023780a046f01408de02811bc05023780a046f01408de02811bc05023780a046f01408de02811bc05023780a046f01408de02811bc05023780a046f01408de02811bc05023780a046f01408de02811bc05023),(0xfff0000001ffffffc00000000000000000000000000000000000000000000001ffffffc0000007ffffff00000000000000000000000000000000000000003fffffffffffff000000000000000000000000000ffffffffffffffffffff8000000,0x6148184c29030985206130a40c26148184c29030985206130a40c26148184c29030985206130a40c26148184c29030985206130a40c26148184c29030985206130a40c26148184c29030985206130a40c26148184c29030985206130a40c2614),(0x7ffffff0000001ffffffc0000000000000000000000000000000000000000000000000000000000007ffffffffffffe0000000000000000000000000000000003ffffff8000000fffffffffffffc0000000000000,0xe926001d24c003a498007493000e926001d24c003a498007493000e926001d24c003a498007493000e926001d24c003a498007493000e926001d24c003a498007493000e926001d24c003a498007493000e926001d24c003a498007493000e9),(0x1ffffffc00000000000000000001fffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000,0x51259b2a24b36544966ca892cd951259b2a24b36544966ca892cd951259b2a24b36544966ca892cd951259b2a24b36544966ca892cd951259b2a24b36544966ca892cd951259b2a24b36544966ca892cd951259b2a24b36544966ca892cd9512),(0x3ffffff8000000ffffffe00000000000007ffffffffffffe0000000000000000000000000000000003ffffff80000000000001ffffffc00000000000000000001ffffffc0000000000000000000000000000000000000000,0x1b6124036c24806d84900db09201b6124036c24806d84900db09201b6124036c24806d84900db09201b6124036c24806d84900db09201b6124036c24806d84900db09201b6124036c24806d84900db09201b6124036c24806d84900db09201b),(0x3ffffff800000000000000000003ffffff8000000fffffffffffffc0000000000000000000000000000000000000000ffffffe00000000000000000000000000000000000000000000000,0x1dc84e43b909c87721390ee42721dc84e43b909c87721390ee42721dc84e43b909c87721390ee42721dc84e43b909c87721390ee42721dc84e43b909c87721390ee42721dc84e43b909c87721390ee42721dc84e43b909c87721390ee42721dc),(0xffffffe00000000000000000000fffffffffffffc00000000000000000000000000000000000000000000001ffffffffffffffffffff000000000000000000000000000000000000000000000000000000,0x9e0125b3c024b6780496cf0092d9e0125b3c024b6780496cf0092d9e0125b3c024b6780496cf0092d9e0125b3c024b6780496cf0092d9e0125b3c024b6780496cf0092d9e0125b3c024b6780496cf0092d9e0125b3c024b6780496cf0092d9e0),(0x3fffffffffffff00000000000003fffffffffffff000000000000000000000000000fffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000,0xe00081bc001037800206f00040de00081bc001037800206f00040de00081bc001037800206f00040de00081bc001037800206f00040de00081bc001037800206f00040de00081bc001037800206f00040de00081bc001037800206f00040de00)]
def deadcolumns : IndexTree ColumnInfo := (.fork 72 (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12)]) (.fork 2 (.leaf [(2,0,509,0,12),(4,0,507,0,12)]) (.leaf [(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12)]))) (.fork 4 (.leaf [(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11)]) (.fork 2 (.leaf [(132,0,379,0,11),(160,0,351,0,11)]) (.leaf [(192,0,319,0,11),(320,0,191,0,11),(0,64,189,258,10)])))) (.fork 9 (.fork 4 (.leaf [(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9)]) (.fork 2 (.leaf [(6,0,505,0,9),(8,16,486,1,9)]) (.leaf [(12,0,499,0,9),(32,128,347,4,9),(33,0,478,0,9)]))) (.fork 4 (.leaf [(65,0,446,0,9),(129,0,382,0,9),(130,0,381,0,9),(256,64,189,2,9)]) (.fork 2 (.leaf [(264,0,247,0,9),(288,0,223,0,9)]) (.leaf [(5,0,506,0,8),(9,0,486,0,8),(10,0,501,0,8)]))))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(36,0,347,0,8),(40,0,471,0,8),(257,0,254,0,8),(272,0,231,0,8)]) (.fork 2 (.leaf [(9,16,486,0,8),(19,0,492,0,8)]) (.leaf [(25,0,486,0,8),(36,128,347,0,8),(49,0,462,0,8)]))) (.fork 4 (.leaf [(67,0,444,0,8),(70,0,441,0,8),(134,0,377,0,8),(140,0,371,0,8)]) (.fork 2 (.leaf [(161,0,350,0,8),(164,0,347,0,8)]) (.leaf [(194,0,317,0,8),(258,64,189,0,8),(280,0,231,0,8)])))) (.fork 9 (.fork 4 (.leaf [(322,0,189,0,8),(328,0,183,0,8),(352,0,159,0,8),(416,0,95,0,8)]) (.fork 2 (.leaf [(1,2,440,68,7),(1,32,94,384,7)]) (.leaf [(2,1,460,48,7),(4,8,227,272,7),(8,256,151,96,7)]))) (.fork 4 (.leaf [(7,0,504,0,7),(14,0,497,0,7),(35,0,476,0,7),(56,0,455,0,7)]) (.fork 2 (.leaf [(74,0,437,0,7),(98,0,413,0,7)]) (.leaf [(133,0,378,0,7),(162,0,349,0,7),(268,0,243,0,7)])))))) (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(289,0,222,0,7),(296,0,215,0,7),(321,0,190,0,7),(324,0,187,0,7)]) (.fork 2 (.leaf [(83,0,428,0,7),(156,0,355,0,7)]) (.leaf [(177,0,334,0,7),(198,0,313,0,7),(344,0,167,0,7)]))) (.fork 4 (.leaf [(480,0,31,0,7),(5,2,440,64,6),(10,4,369,128,6),(34,1,460,16,6)]) (.fork 2 (.leaf [(40,256,151,64,6),(48,1,460,2,6)]) (.leaf [(68,8,163,272,6),(129,2,312,68,6),(129,32,94,256,6)])))) (.fork 9 (.fork 4 (.leaf [(130,4,369,8,6),(257,32,94,128,6),(11,16,484,0,5),(14,64,177,256,5)]) (.fork 2 (.leaf [(35,64,156,256,5),(35,128,344,4,5)]) (.leaf [(37,128,346,0,5),(44,128,339,0,5),(69,2,440,0,5)]))) (.fork 4 (.leaf [(74,4,305,128,5),(81,2,424,4,5),(88,256,135,32,5),(98,1,396,16,5)]) (.fork 2 (.leaf [(98,128,281,4,5),(133,2,312,64,5)]) (.leaf [(162,1,332,16,5),(193,2,312,4,5),(225,0,286,0,5)]))))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(266,64,181,0,5),(289,64,156,2,5),(321,32,30,128,5),(324,8,163,16,5)]) (.fork 2 (.leaf [(324,128,27,32,5),(385,32,94,0,5)]) (.leaf [(388,8,99,16,5),(39,0,344,0,4),(15,16,480,0,4)]))) (.fork 4 (.leaf [(39,128,344,0,4),(53,128,330,0,4),(85,2,424,0,4),(102,128,281,0,4)]) (.fork 2 (.leaf [(114,1,396,0,4),(120,256,135,0,4)]) (.leaf [(141,16,354,0,4),(154,4,353,0,4),(167,0,344,0,4)])))) (.fork 9 (.fork 4 (.leaf [(178,1,332,0,4),(197,2,312,0,4),(202,4,305,0,4),(206,0,305,0,4)]) (.fork 2 (.leaf [(232,256,23,0,4),(270,64,177,0,4)]) (.leaf [(275,64,172,0,4),(291,64,156,0,4),(297,16,198,0,4)]))) (.fork 4 (.leaf [(329,16,166,0,4),(334,0,177,0,4),(340,8,163,0,4),(356,128,27,0,4)]) (.fork 2 (.leaf [(390,64,57,0,4),(401,32,78,0,4)]) (.leaf [(404,8,99,0,4),(449,32,30,0,4),(481,0,30,0,4)])))))))
def deadautos : Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest:=⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def isNotT (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w∧proper a∧gv w g=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧gv w g=bin d a b):=by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a)∨∃ x,x∈w∧proper x∧neg a=neg x:=by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
    · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b)∨∃ d' x y,x∈w∧y∈w∧proper x∧proper y∧x≠y∧bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero∧bin true v zero=v:=fun v => ⟨(bin_laws v).2.2.1,(bin_laws v).2.1⟩
    have bone : ∀ v,bin false v one=v∧bin true v one=one:=fun v => ⟨(bin_laws v).1,(bin_laws v).2.2.2.1⟩
    rcases operand_cases ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [bin_comm]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [bin_comm]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases operand_cases hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a=b
        · subst b
          cases d
          · rw [(bin_laws a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(bin_laws a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩:=hg
  rcases ho with ho | ho | ho
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho,isNotT,ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,neg_laws.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)
lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a,a∈w∧proper a∧z=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧z=bin d a b))
    (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧t' ≤ t+isN.toNat∧Live target k' t' S'∧∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w∨a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩:=hwit
          subst z
          let U:=S.erase (neg a)
          have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U:=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩:=hwit
          subst z
          let U:=S.erase (bin d a b)
          have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U):=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
lemma extractT (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧t ≤ gs.countP (fun g => isNotT g.op)∧Live target k t S∧∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩:=pull_gateT (isNotT g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega
def ImpossibleT (T : Sig) (cap tmax : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → t ≤ tmax → ¬Live T k t S
theorem imp_to_impT {T cap tmax S} (h : Impossible T cap S) : ImpossibleT T cap tmax S :=
  fun k t hk _ => h k t hk
theorem rotate_excludedT {T n tmax} {ws : List Sig} (hi : ImpossibleT T n tmax ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : ImpossibleT T n tmax (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
  have run:=live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run
theorem enum_stepT {T : Sig} {cap tmax : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tmax > 0 → ∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleT T (cap-1) (if (childOne ws a keep).length=cap then 0 else tmax-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap-1) (if (childTwo ws a b d ka kb).length=cap then 0 else tmax)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleT T cap tmax ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [kept_fin,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len : (childOne ws a keep).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childOne ws a keep).length=cap then 0 else tmax - 1:=by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases hja : j=a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hab]
      · by_cases hjb : j=b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_; simp [ke]
    have sc:=(live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childTwo ws a b d ka kb).length=cap then 0 else tmax:=by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · exact ht
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
def separates (w : Sig) (p q : Row) := bit p w = true ∧ bit q w = false
def rectProtocol (T : Sig) (S : Finset Sig) : Prop :=
  ∃ f : Row → Row → Sig, (∀ p q, f p q ∈ S) ∧
    (∀ p q, separates T p q → separates (f p q) p q) ∧
    ∀ p q r s, f p q = f r s → f p s = f p q
def forkPick (d : Bool) (a b : Sig) (p q : Row) :=
  if (if d then bit p a else !(bit q a)) then a else b
lemma forkPick_mem (d a b p q) : forkPick d a b p q=a ∨ forkPick d a b p q=b := by
  cases d <;> cases hp : bit p a <;> cases hq : bit q a <;> simp [forkPick,hp,hq]
lemma forkPick_sep {d a b p q} (h : separates (bin d a b) p q) :
    separates (forkPick d a b p q) p q := by
  simp only [separates,bit_bin] at h
  cases d <;> cases hp : bit p a <;> cases hq : bit q a <;>
    simp_all [forkPick,separates]
lemma refine_protocol {T U a b d} (an : a ∉ U) (bn : b ∉ U)
    (h : rectProtocol T (insert (bin d a b) U)) :
    rectProtocol T (insert a (insert b U)) := by
  obtain ⟨f,mem,sep,rect⟩ := h
  let z := bin d a b
  let g := fun p q => if f p q=z then forkPick d a b p q else f p q
  have undo (p q) : (if g p q=a ∨ g p q=b then z else g p q) = f p q := by
    by_cases hz : f p q=z
    · simp only [g,hz,ite_true,if_pos (forkPick_mem d a b p q)]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have ha : f p q ≠ a := fun e => an (e ▸ hu)
      have hb : f p q ≠ b := fun e => bn (e ▸ hu)
      simp [g,hz,ha,hb]
  refine ⟨g,?_,?_,?_⟩
  · intro p q
    by_cases hz : f p q=z
    · rcases forkPick_mem d a b p q with e|e <;> simp [g,hz,e]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      simp only [g,if_neg hz]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
  · intro p q st
    by_cases hz : f p q=z
    · have hh : separates z p q := by rw [←hz]; exact sep p q st
      simpa [g,hz] using forkPick_sep (d:=d) (a:=a) (b:=b) hh
    · simpa [g,hz] using sep p q st
  · intro p q r s e
    have eo : f p q=f r s := by rw [← undo p q,← undo r s,e]
    have ec := rect p q r s eo
    by_cases hz : f p q=z
    · have ht : f r s=z := eo.symm.trans hz
      have ep : forkPick d a b p q=forkPick d a b r s := by simpa only [g,hz,ht,ite_true] using e
      simp only [g,ec,hz,ite_true]
      cases d
      · exact ep.symm
      · rfl
    · simp [g,ec,hz]
theorem tight_protocol {T k t S} (h : Live T k t S) (tight : k+1 ≤ S.card) :
    rectProtocol T S := by
  induction h using Live.recurse with
  | stop hp => exact ⟨fun _ _ => T,fun _ _ => Finset.mem_singleton_self _,fun _ _ => id,fun _ _ _ _ _ => rfl⟩
  | @unary k t U a hp hf tail ih =>
    have sz := (live_size (Live.unary hp hf tail)).2
    omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun m => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le (a:=a) (s:=insert b U)
    have y := Finset.card_insert_le (a:=b) (s:=U)
    have an : a ∉ U := by
      intro am
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at tight
      omega
    have bn : b ∉ U := by
      intro bm
      rw [Finset.insert_eq_of_mem bm] at tight x
      omega
    apply refine_protocol an bn
    apply ih
    rw [Finset.card_insert_of_notMem zu]
    omega
-- A wire is forced on a pair of rows when it is the only live wire that separates them.
def forcedPick (T : Sig) (S : Finset Sig) (w : Sig) (p q : Row) :=
  separates T p q ∧ ∀ v ∈ S, separates v p q → v=w
def clash (T : Sig) (S : Finset Sig) (a b : Sig) : Prop :=
  a∈S ∧ b∈S ∧ a≠b ∧ ∃ p u v q r s,
    forcedPick T S a p u ∧ forcedPick T S b p v ∧ forcedPick T S a r q ∧ forcedPick T S b s q
lemma protocol_consistent {T S a b} (h : rectProtocol T S) (c : clash T S a b) : False := by
  obtain ⟨f,mem,sep,rect⟩ := h
  obtain ⟨_,_,ne,p,u,v,q,r,s,w₁,w₂,w₃,w₄⟩ := c
  have pick {z x y} (w : forcedPick T S z x y) := w.2 _ (mem x y) (sep x y w.1)
  have A := rect p u r q ((pick w₁).trans (pick w₃).symm)
  have B := rect p v s q ((pick w₂).trans (pick w₄).symm)
  exact ne ((A.trans (pick w₁)).symm.trans (B.trans (pick w₂)))
lemma join_separates {a b d p q} (h : separates (bin d a b) p q) :
    separates a p q ∨ separates b p q := by
  rcases forkPick_mem d a b p q with e | e
  · exact Or.inl (e ▸ forkPick_sep h)
  · exact Or.inr (e ▸ forkPick_sep h)
def carrier (a b z w : Sig) := if w=a ∨ w=b then z else w
lemma transfer_forced {T U a b d w p q}
    (safe : w∈U → w≠a ∧ w≠b) (h : forcedPick T (insert a (insert b U)) w p q) :
    forcedPick T (insert (bin d a b) U) (carrier a b (bin d a b) w) p q := by
  refine ⟨h.1,?_⟩
  intro x hx sp
  rcases Finset.mem_insert.mp hx with rfl | hu
  · rcases join_separates sp with x | x
    · have eq := h.2 a (by simp) x
      simp [carrier,eq.symm]
    · have eq := h.2 b (by simp) x
      simp [carrier,eq.symm]
  · have eq := h.2 x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) sp
    subst x
    simp [carrier,(safe hu).1,(safe hu).2]
lemma forced_on_run {T k t S w p q} (run : Live T k t S) (m : t=0) (h : forcedPick T S w p q) :
    w∈S ∧ separates w p q := by
  obtain ⟨v,hv,sp⟩ := mono_row_difference run m h.1.1 h.1.2
  exact h.2 v hv sp ▸ And.intro hv sp
lemma gate_protocol (d : Bool) (a b : Sig) : rectProtocol (bin d a b) {a,b} := by
  refine ⟨forkPick d a b,?_,fun _ _ => forkPick_sep,?_⟩
  · intro p q
    rcases forkPick_mem d a b p q with e | e <;> simp [e]
  · intro p q r s eq
    cases d
    · exact eq.symm
    · rfl
lemma transfer_clash {T k t U a b d i j}
    (fresh : bin d a b∉insert a (insert b U)) (tail : Live T k t (insert (bin d a b) U)) (m : t=0)
    (si : i∈U → i≠a ∧ i≠b) (sj : j∈U → j≠a ∧ j≠b)
    (c : clash T (insert a (insert b U)) i j) :
    clash T (insert (bin d a b) U) (carrier a b (bin d a b) i) (carrier a b (bin d a b) j) := by
  let z := bin d a b
  obtain ⟨im,jm,ne,p,u,v,q,r,s,w₁,w₂,w₃,w₄⟩ := c
  have a₁ := transfer_forced (d:=d) si w₁
  have a₂ := transfer_forced (d:=d) sj w₂
  have a₃ := transfer_forced (d:=d) si w₃
  have a₄ := transfer_forced (d:=d) sj w₄
  refine ⟨(forced_on_run tail m a₁).1,(forced_on_run tail m a₂).1,?_,p,u,v,q,r,s,a₁,a₂,a₃,a₄⟩
  intro same
  by_cases hI : i=a ∨ i=b <;> by_cases hJ : j=a ∨ j=b
  · have gateForced {w x y} (sw : w∈U → w≠a ∧ w≠b) (old : forcedPick T (insert a (insert b U)) w x y)
        (ab : w=a ∨ w=b) : forcedPick z {a,b} w x y := by
      have sp := (forced_on_run tail m (transfer_forced (d:=d) sw old)).2
      refine ⟨by simpa [carrier,ab,z] using sp,?_⟩
      intro v hv sv
      apply old.2 v _ sv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp
      · simp [Finset.mem_singleton.mp hv]
    apply protocol_consistent (gate_protocol d a b) (a:=i) (b:=j)
    exact ⟨by simpa using hI,by simpa using hJ,ne,p,u,v,q,r,s,
      gateForced si w₁ hI,gateForced sj w₂ hJ,gateForced si w₃ hI,gateForced sj w₄ hJ⟩
  · simp only [carrier,if_pos hI,if_neg hJ] at same
    exact fresh (same ▸ jm)
  · simp only [carrier,if_neg hI,if_pos hJ] at same
    exact fresh (same ▸ im)
  · exact ne (by simpa [carrier,hI,hJ] using same)
def divides (T : Sig) (S : Finset Sig) :=
  ∃ (color : Sig → Bool) (h : Sig),
    (∀ p q, separates h p q → ∃ v∈S, color v=true ∧ separates v p q) ∧
    (∀ p q, separates T p q → separates h p q ∨ ∃ v∈S, color v=false ∧ separates v p q) ∧
    ∀ i j, clash T S i j → color i≠color j
lemma divides_gate {T k t U a b d}
    (an : a∉U) (bn : b∉U) (fresh : bin d a b∉insert a (insert b U))
    (tail : Live T k t (insert (bin d a b) U)) (m : t=0)
    (rest : divides T (insert (bin d a b) U)) : divides T (insert a (insert b U)) := by
  obtain ⟨c,h,inside,outside,ok⟩ := rest
  let f := carrier a b (bin d a b)
  refine ⟨fun w => c (f w),h,?_,?_,?_⟩
  · intro p q hit
    obtain ⟨v,mem,clr,sp⟩ := inside p q hit
    rcases Finset.mem_insert.mp mem with rfl | hu
    · rcases join_separates sp with left | right
      · exact ⟨a,by simp,by simpa [f,carrier] using clr,left⟩
      · exact ⟨b,by simp,by simpa [f,carrier] using clr,right⟩
    · have na : v≠a := fun e => an (e ▸ hu)
      have nb : v≠b := fun e => bn (e ▸ hu)
      exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),by simpa [f,carrier,na,nb] using clr,sp⟩
  · intro p q hit
    rcases outside p q hit with sp | ⟨v,mem,clr,sp⟩
    · exact Or.inl sp
    · right
      rcases Finset.mem_insert.mp mem with rfl | hu
      · rcases join_separates sp with left | right
        · exact ⟨a,by simp,by simpa [f,carrier] using clr,left⟩
        · exact ⟨b,by simp,by simpa [f,carrier] using clr,right⟩
      · have na : v≠a := fun e => an (e ▸ hu)
        have nb : v≠b := fun e => bn (e ▸ hu)
        exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),by simpa [f,carrier,na,nb] using clr,sp⟩
  · intro i j bad
    apply ok _ _ (transfer_clash fresh tail m _ _ bad)
    all_goals intro hu; exact ⟨fun e => an (e ▸ hu),fun e => bn (e ▸ hu)⟩
lemma divides_retained {T k t U a b d}
    (ha : proper a) (hb : proper b) (hab : a≠b) (fresh : bin d a b∉insert a (insert b U))
    (tail : Live T k t (insert (bin d a b) U)) (m : t=0) (prot : rectProtocol T (insert (bin d a b) U))
    (shared : Sig) (ha' : a∈U → a=shared) (hb' : b∈U → b=shared) (mem : shared∈insert a (insert b U)) :
    divides T (insert a (insert b U)) := by
  refine ⟨fun w => decide (w=shared),shared,?_,?_,?_⟩
  · intro p q h
    exact ⟨shared,mem,by simp,h⟩
  · intro p q h
    obtain ⟨v,hv,sp⟩ := mono_row_difference (Live.binary ha hb hab fresh tail) m h.1 h.2
    by_cases eq : v=shared
    · exact Or.inl (eq ▸ sp)
    · exact Or.inr ⟨v,hv,by simpa using eq,sp⟩
  · intro i j c same
    by_cases iS : i=shared <;> by_cases jS : j=shared
    · exact c.2.2.1 (iS.trans jS.symm)
    · simp [iS,jS] at same
    · simp [iS,jS] at same
    · have safe (v) (ns : v≠shared) (hu : v∈U) : v≠a ∧ v≠b :=
        ⟨fun e => ns (e.trans (ha' (e ▸ hu))),fun e => ns (e.trans (hb' (e ▸ hu)))⟩
      exact protocol_consistent prot (transfer_clash fresh tail m (safe i iS) (safe j jS) c)
theorem one_fork {T k t S} (run : Live T k t S) (m : t=0) (budget : k≤S.card) : divides T S := by
  induction run using Live.recurse with
  | stop hp =>
    exact ⟨fun _ => true,T,fun p q h => ⟨T,by simp,rfl,h⟩,fun _ _ h => Or.inl h,
      fun _ _ c => False.elim (c.2.2.1 ((Finset.mem_singleton.mp c.1).trans (Finset.mem_singleton.mp c.2.1).symm))⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le (a:=a) (s:=insert b U)
    have y := Finset.card_insert_le (a:=b) (s:=U)
    by_cases am : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at budget
      have tight : k+1≤(insert (bin d a b) U).card := by rw [Finset.card_insert_of_notMem zu]; omega
      apply divides_retained ha hb hab hf tail m (tight_protocol tail tight) a (fun _ => rfl) _ (by simp)
      intro bm
      rw [Finset.insert_eq_of_mem bm] at budget
      omega
    · by_cases bm : b∈U
      · rw [Finset.insert_eq_of_mem bm] at budget x
        have tight : k+1≤(insert (bin d a b) U).card := by rw [Finset.card_insert_of_notMem zu]; omega
        exact divides_retained ha hb hab hf tail m (tight_protocol tail tight) b (fun hm => False.elim (am hm)) (fun _ => rfl) (by simp)
      · apply divides_gate am bm hf tail m (ih m ?_)
        rw [Finset.card_insert_of_notMem zu]
        omega
abbrev Cell2303 := BitVec 768
abbrev Square2303 := Fin 27
def pRow2303 (j : Nat) : Row := (#[3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321,22,82,148,176,304,336,26,162,266,290,21] : Array Row)[j]?.getD 0
def nRow2303 (j : Nat) : Row := (#[42,50,69,104,116,138,200,201,208,261,276,385,402,100,386,400,112,193,84,52,137,73,274,146,42,50,69] : Array Row)[j]?.getD 0
def gridP2303 (i : Fin 768) := pRow2303 (i.val/27 % 27)
def gridN2303 (i : Fin 768) := nRow2303 (i.val % 27)
lemma gridYes2303 : ∀ i : Square2303, bit (pRow2303 i.val) graph=true := by decide +kernel
lemma gridNo2303 : ∀ i : Square2303, bit (nRow2303 i.val) graph=false := by decide +kernel
def uniq2303 {α : Type} (c : α → Cell2303) : List α → Cell2303 × Cell2303
  | [] => (0,0)
  | a::l => let u := uniq2303 c l
            (c a ||| u.1,(c a &&& ~~~u.1) ||| (u.2 &&& ~~~(c a)))
lemma marked2303 {α : Type} (c : α → Cell2303) (xs : List α) (i : Fin 768) :
    ((uniq2303 c xs).1.getLsbD i.val=true ↔ ∃ a∈xs, (c a).getLsbD i.val=true) ∧
    ((uniq2303 c xs).2.getLsbD i.val=true → ∀ a∈xs, ∀ b∈xs,
      (c a).getLsbD i.val=true → (c b).getLsbD i.val=true → a=b) := by
  induction xs with
  | nil => simp [uniq2303]
  | cons x xs ih =>
    obtain ⟨exist,uniq⟩ := ih
    simp only [uniq2303,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,
      i.isLt,decide_true,Bool.true_and,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',
      List.mem_cons,exists_eq_or_imp]
    refine ⟨by rw [exist],?_⟩
    rintro (first|later) a (rfl|am) b (rfl|bm) aa bb
    all_goals first | rfl | exact uniq later.1 _ am _ bm aa bb |
      exact False.elim (Bool.noConfusion (later.2.symm.trans aa)) |
      exact False.elim (Bool.noConfusion (later.2.symm.trans bb)) |
      exact False.elim (Bool.noConfusion (first.2.symm.trans (exist.mpr ⟨_,am,aa⟩))) |
      exact False.elim (Bool.noConfusion (first.2.symm.trans (exist.mpr ⟨_,bm,bb⟩)))
def monoCell2303 (v : Decor) := v.2.1 &&& ~~~v.2.2
def gridSound2303 (xs : List Decor) (col : Decor → Cell2303) (val : Sig → Sig) :=
  ∀ w ∈ xs, ∀ p q : Square2303, separates (val w.1) (pRow2303 p.val) (nRow2303 q.val) →
     (col w).getLsbD (27*p.val+q.val)=true
lemma grid_vals2303 {xs : List Decor} (ok : ∀ w ∈ xs, faithful gridP2303 gridN2303 w) {w} (mem : w∈xs) (p q : Square2303) :
    w.2.1.getLsbD (27*p.val+q.val)=bit (pRow2303 p.val) w.1 ∧
    w.2.2.getLsbD (27*p.val+q.val)=bit (nRow2303 q.val) w.1 := by
  let i : Fin 768 := ⟨27*p.val+q.val,by omega⟩
  have hP : gridP2303 i=pRow2303 p.val := by simp only [gridP2303,i]; congr 1; omega
  have hN : gridN2303 i=nRow2303 q.val := by simp only [gridN2303,i]; congr 1; omega
  rw [show w.2=pairSig gridP2303 gridN2303 w.1 from ok w mem]
  exact ⟨(ofRows_bit _ _ i).trans (hP ▸ rfl),(ofRows_bit _ _ i).trans (hN ▸ rfl)⟩
lemma mono_grid2303 {xs : List Decor} (ok : ∀ w ∈ xs, faithful gridP2303 gridN2303 w) : gridSound2303 xs monoCell2303 id := by
  intro w mem p q h
  obtain ⟨hp,hn⟩ := grid_vals2303 ok mem p q
  have lt : 27*p.val+q.val<768 := by omega
  change separates w.1 (pRow2303 p.val) (nRow2303 q.val) at h
  simp only [monoCell2303,BitVec.getLsbD_and,BitVec.getLsbD_not,lt,decide_true,Bool.true_and,hp,hn,h.1,h.2,Bool.not_false,Bool.and_self]
def marg2303 (v : Nat) : Nat × Nat :=
  let rows := ((1 <<< 729)-1)/134217727
  let x := v &&& ((1 <<< 729)-1)
  let high := (x ||| ((x &&& (rows*67108863))+rows*67108863)) &&& (rows <<< 26)
  let occupied := (((high >>> 26)*(((1 <<< 702)-1)/67108863)) >>> 676) &&& 134217727
  let cols := x
  let cols := cols ||| (cols >>> 27)
  let cols := cols ||| (cols >>> 54)
  let cols := cols ||| (cols >>> 108)
  let cols := cols ||| (cols >>> 216)
  let cols := cols ||| (cols >>> 432)
  (occupied,cols &&& 134217727)
abbrev Info2303 := Sig × Cell2303 × Cell2303 × Nat × Nat
def infos2303 (xs : List Decor) (c : Decor → Cell2303) : List Info2303 :=
  let all := (uniq2303 c xs).2
  xs.map fun w =>
    let u := all &&& c w
    let pq := marg2303 u.toNat
    (w.1,c w,u,pq)
def validXY2303 (v : Cell2303) (p q : Nat) :=
  decide (p<27 ∧ q<27) && v.getLsbD (27*p+q)
def inRow2303 (v : Cell2303) (p : Nat) := ((v.toNat >>> (27*p))%134217728).log2
def gridUnit2303 := ((1 <<< 729)-1)/134217727
def inCol2303 (v : Cell2303) (q : Nat) := (v.toNat &&& (gridUnit2303 <<< q)).log2/27
def edgeGrid2303 (a b : Info2303) :=
  let mp := a.2.2.2.1 &&& b.2.2.2.1
  let mq := a.2.2.2.2 &&& b.2.2.2.2
  if mp==0 || mq==0 || a.1==b.1 then false else
    let p := mp.log2
    let q := mq.log2
    let x := a.2.2.1
    let y := b.2.2.1
    validXY2303 x p (inRow2303 x p) && validXY2303 y p (inRow2303 y p) &&
      validXY2303 x (inCol2303 x q) q && validXY2303 y (inCol2303 y q) q
def forcedValue2303 (S : Finset Sig) (val : Sig → Sig) (w : Sig) (p q : Row) :=
  separates graph p q ∧ ∀ v∈S, separates (val v) p q → v=w
def valueClash2303 (S : Finset Sig) (val : Sig → Sig) (a b : Sig) :=
  a∈S ∧ b∈S ∧ a≠b ∧ ∃ p u v q r s, forcedValue2303 S val a p u ∧ forcedValue2303 S val b p v ∧
    forcedValue2303 S val a r q ∧ forcedValue2303 S val b s q
lemma forced_cell2303 {xs c val} (h : gridSound2303 xs c val) {a p q}
    (mem : a∈infos2303 xs c) (test : validXY2303 a.2.2.1 p q=true) :
    forcedValue2303 (xs.map Prod.fst).toFinset val a.1 (pRow2303 p) (nRow2303 q) := by
  obtain ⟨w,wm,rfl⟩ := List.mem_map.mp mem
  simp only [validXY2303,Bool.and_eq_true,decide_eq_true_eq] at test
  obtain ⟨⟨hp,hq⟩,v⟩ := test
  let i : Fin 768 := ⟨27*p+q,by omega⟩
  change (((uniq2303 c xs).2 &&& c w).getLsbD i.val)=true at v
  simp only [BitVec.getLsbD_and,Bool.and_eq_true] at v
  refine ⟨⟨gridYes2303 ⟨p,hp⟩,gridNo2303 ⟨q,hq⟩⟩,?_⟩
  intro a am sp
  obtain ⟨b,bm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
  exact congrArg Prod.fst ((marked2303 c xs i).2 v.1 b bm w wm (h b bm ⟨p,hp⟩ ⟨q,hq⟩ sp) v.2)
lemma info_mem2303 {xs c a} (h : a∈infos2303 xs c) : a.1∈(xs.map Prod.fst).toFinset := by
  obtain ⟨w,wm,rfl⟩ := List.mem_map.mp h
  exact List.mem_toFinset.mpr (List.mem_map_of_mem wm)
lemma edge_grid_sound2303 {xs c val} (h : gridSound2303 xs c val) {a b}
    (am : a∈infos2303 xs c) (bm : b∈infos2303 xs c) (test : edgeGrid2303 a b=true) :
    valueClash2303 (xs.map Prod.fst).toFinset val a.1 b.1 := by
  simp only [edgeGrid2303] at test
  split at test
  next => contradiction
  next ok =>
    have ne : a.1≠b.1 := fun e => ok (by simp [e])
    simp only [Bool.and_eq_true] at test
    exact ⟨info_mem2303 am,info_mem2303 bm,ne,_,_,_,_,_,_,forced_cell2303 h am test.1.1.1,
      forced_cell2303 h bm test.1.1.2,forced_cell2303 h am test.1.2,forced_cell2303 h bm test.2⟩
def allGrid2303 : Cell2303 := BitVec.ofNat 768 ((1 <<< 729)-1)
def cols2303 : List Info2303 → Cell2303
  | [] => 0
  | v::l => v.2.1 ||| cols2303 l
lemma cols_hit2303 {xs : List Info2303} {v j} (mem : v∈xs) (hit : v.2.1.getLsbD j=true) :
    (cols2303 xs).getLsbD j=true := by
  induction xs with
  | nil => contradiction
  | cons a l ih =>
    simp only [cols2303,BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl | hm
    · exact Or.inl hit
    · exact Or.inr (ih hm)
def lacks2303 (v : Cell2303) (p q : Nat) :=
  decide (p<27 ∧ q<27) && !(v.getLsbD (27*p+q))
def noPart2303 (within outside : Cell2303) :=
  let need := allGrid2303 &&& ~~~outside
  let x := need.toNat
  let units := gridUnit2303
  let low := units*67108863
  let rows := ((x ||| ((x &&& low)+low)) &&& (units <<< 26)) >>> 26
  let cols := (marg2303 x).2
  let missing := (rows*cols) &&& (~~~within).toNat
  if missing==0 then false else
    let j := missing.log2
    let p := j/27
    let q := j % 27
    lacks2303 outside p (inRow2303 need p) && lacks2303 outside (inCol2303 need q) q &&
      lacks2303 within p q
lemma noPart_witness2303 {within outside} (h : noPart2303 within outside=true) :
    ∃ p u v q : Square2303, outside.getLsbD (27*p.val+u.val)=false ∧
      outside.getLsbD (27*v.val+q.val)=false ∧ within.getLsbD (27*p.val+q.val)=false := by
  unfold noPart2303 at h
  dsimp only at h
  split at h
  next => contradiction
  next =>
    simp only [lacks2303,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
    exact ⟨⟨_,h.1.1.1.1⟩,⟨_,h.1.1.1.2⟩,⟨_,h.1.2.1.1⟩,⟨_,h.2.1.2⟩,h.1.1.2,h.1.2.2,h.2.2⟩
lemma joint_hit2303 {a b : List Info2303} {v j} (mem : v∈a ∨ v∈b) (hit : v.2.1.getLsbD j=true) :
    (cols2303 a ||| cols2303 b).getLsbD j=true := by
  rw [BitVec.getLsbD_or,Bool.or_eq_true]
  exact mem.imp (fun h => cols_hit2303 h hit) (fun h => cols_hit2303 h hit)
def area2303 (v : Info2303) :=
  let count := fun (x : Nat) =>
    let x := x - ((x >>> 1) &&& 1431655765)
    let x := (x &&& 858993459) + ((x >>> 2) &&& 858993459)
    ((((x+(x >>> 4)) &&& 252645135)*16843009) >>> 24) % 256
  count v.2.2.2.1 * count v.2.2.2.2
def order2303 (l : List Info2303) := l.insertionSort (fun a b => area2303 b≤area2303 a)
def scanPart2303 (inside outside : List Info2303) : List Info2303 → Bool
  | [] => noPart2303 (cols2303 inside ||| cols2303 []) (cols2303 outside ||| cols2303 [])
  | v::l =>
    let free := cols2303 (v::l)
    (decide (l.length<4) && noPart2303 (cols2303 inside ||| free) (cols2303 outside ||| free)) ||
    ((inside.any (edgeGrid2303 v) || scanPart2303 (v::inside) outside l) &&
    (outside.any (edgeGrid2303 v) || scanPart2303 inside (v::outside) l))
lemma scanPart_bad2303 {xs} (g : gridSound2303 xs monoCell2303 id)
    (D : divides graph (xs.map Prod.fst).toFinset)
    (pass : scanPart2303 [] [] (order2303 (infos2303 xs monoCell2303))=true) : False := by
  obtain ⟨color,h,inner,outer,proper⟩ := D
  let infos := infos2303 xs monoCell2303
  have close (l inside outside : List Info2303) (covered : ∀ a∈infos, a∈l ∨ a∈inside ∨ a∈outside)
      (inOK : ∀ a∈inside, a∈infos ∧ color a.1=true)
      (outOK : ∀ a∈outside, a∈infos ∧ color a.1=false)
      (test : noPart2303 (cols2303 inside ||| cols2303 l) (cols2303 outside ||| cols2303 l)=true) : False := by
    obtain ⟨p,u,v,q,pu,vq,pq⟩ := noPart_witness2303 test
    have force (p q : Square2303) (missing : (cols2303 outside ||| cols2303 l).getLsbD (27*p.val+q.val)=false) :
        separates h (pRow2303 p.val) (nRow2303 q.val) := by
      rcases outer _ _ ⟨gridYes2303 p,gridNo2303 q⟩ with hit | ⟨a,am,clr,sp⟩
      · exact hit
      · obtain ⟨w,wm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
        let z : Info2303 := (w.1,monoCell2303 w,(uniq2303 monoCell2303 xs).2 &&& monoCell2303 w,
          marg2303 ((uniq2303 monoCell2303 xs).2 &&& monoCell2303 w).toNat)
        have zm : z∈infos := List.mem_map_of_mem wm
        rcases covered z zm with bad | ins | outs
        · exact False.elim (Bool.noConfusion (missing.symm.trans (joint_hit2303 (Or.inr bad) (g w wm p q sp))))
        · exact False.elim (Bool.noConfusion (clr.symm.trans (inOK z ins).2))
        · exact False.elim (Bool.noConfusion (missing.symm.trans (joint_hit2303 (Or.inl outs) (g w wm p q sp))))
    have x := force p u pu
    have y := force v q vq
    obtain ⟨a,am,clr,sp⟩ := inner _ _ ⟨x.1,y.2⟩
    obtain ⟨w,wm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
    let z : Info2303 := (w.1,monoCell2303 w,(uniq2303 monoCell2303 xs).2 &&& monoCell2303 w,
      marg2303 ((uniq2303 monoCell2303 xs).2 &&& monoCell2303 w).toNat)
    have zm : z∈infos := List.mem_map_of_mem wm
    rcases covered z zm with bad | ins | outs
    · exact Bool.noConfusion (pq.symm.trans (joint_hit2303 (Or.inr bad) (g w wm p q sp)))
    · exact Bool.noConfusion (pq.symm.trans (joint_hit2303 (Or.inl ins) (g w wm p q sp)))
    · exact Bool.noConfusion (clr.symm.trans (outOK z outs).2)
  have go (l inside outside : List Info2303) (covered : ∀ a∈infos, a∈l ∨ a∈inside ∨ a∈outside)
      (sub : ∀ a∈l, a∈infos)
      (inOK : ∀ a∈inside, a∈infos ∧ color a.1=true)
      (outOK : ∀ a∈outside, a∈infos ∧ color a.1=false)
      (test : scanPart2303 inside outside l=true) : False := by
    induction l generalizing inside outside with
    | nil =>
      apply close [] inside outside covered inOK outOK
      exact test
    | cons x l ih =>
      have xm := sub x (by simp)
      have sm (a) (am : a∈l) := sub a (List.mem_cons_of_mem _ am)
      have dis (v) (vm : v∈infos) (e : edgeGrid2303 x v=true) : color x.1≠color v.1 :=
        proper _ _ (edge_grid_sound2303 g xm vm e)
      simp only [scanPart2303,Bool.and_eq_true,Bool.or_eq_true,List.any_eq_true] at test
      rcases test with stop | test
      · exact close (x::l) inside outside covered inOK outOK stop.2
      cases cx : color x.1
      · rcases test.2 with ⟨v,vm,e⟩ | tail
        · exact dis v (outOK v vm).1 e (cx.trans (outOK v vm).2.symm)
        · apply ih inside (x::outside) _ sm inOK _ tail
          · intro a am
            rcases covered a am with first | si | so
            · rcases List.mem_cons.mp first with rfl | mem
              · exact Or.inr (Or.inr (by simp))
              · exact Or.inl mem
            · exact Or.inr (Or.inl si)
            · exact Or.inr (Or.inr (List.mem_cons_of_mem _ so))
          · intro a am
            rcases List.mem_cons.mp am with rfl | mem
            · exact ⟨xm,cx⟩
            · exact outOK a mem
      · rcases test.1 with ⟨v,vm,e⟩ | tail
        · exact dis v (inOK v vm).1 e (cx.trans (inOK v vm).2.symm)
        · apply ih (x::inside) outside _ sm _ outOK tail
          · intro a am
            rcases covered a am with first | si | so
            · rcases List.mem_cons.mp first with rfl | mem
              · exact Or.inr (Or.inl (by simp))
              · exact Or.inl mem
            · exact Or.inr (Or.inl (List.mem_cons_of_mem _ si))
            · exact Or.inr (Or.inr so)
          · intro a am
            rcases List.mem_cons.mp am with rfl | mem
            · exact ⟨xm,cx⟩
            · exact inOK a mem
  exact go (order2303 infos) [] [] (fun _ hm => Or.inl ((List.mem_insertionSort _).mpr hm))
    (fun _ hm => (List.mem_insertionSort _).mp hm) (by simp) (by simp) pass
-- A read-once formula gives disjoint rectangles. One fork allows two groups of wires.
def rectEnd (cap : Nat) (xs : List Decor) : Bool :=
  if xs.length < cap then false else
    let info := infos2303 xs monoCell2303
    if cap < xs.length then info.any (fun a => info.any (edgeGrid2303 a)) else scanPart2303 [] [] (order2303 info)
lemma rectEnd_sound {cap : Nat} {ds : List Decor} (nd : (ds.map Prod.fst).Nodup)
    (valid : ∀ w ∈ ds, faithful gridP2303 gridN2303 w) (done : rectEnd cap ds=true) :
    ImpossibleT graph cap 0 (ds.map Prod.fst).toFinset := by
  intro k t hk ht run
  have size := List.toFinset_card_of_nodup nd
  rw [List.length_map] at size
  have edge {a b} (am : a ∈ infos2303 ds monoCell2303) (bm : b ∈ infos2303 ds monoCell2303)
      (hit : edgeGrid2303 a b=true) : clash graph (ds.map Prod.fst).toFinset a.1 b.1 :=
    edge_grid_sound2303 (mono_grid2303 valid) am bm hit
  unfold rectEnd at done
  split at done
  next => contradiction
  next later =>
    dsimp only at done
    split at done
    next tight =>
      obtain ⟨a,ha,h⟩ := List.any_eq_true.mp done
      obtain ⟨b,hb,col⟩ := List.any_eq_true.mp h
      exact protocol_consistent (tight_protocol run (by omega)) (edge ha hb col)
    next =>
      exact scanPart_bad2303 (mono_grid2303 valid) (one_fork run (by omega) (by omega)) done
lemma gridLayout :
    (asRow fun j => (dead.samples j).1)=gridP2303 ∧ (asRow fun j => (dead.samples j).2)=gridN2303 := by
  constructor <;> funext i
  · exact (by decide +kernel : ∀ i, asRow (fun j => (dead.samples j).1) i=gridP2303 i) i
  · exact (by decide +kernel : ∀ i, asRow (fun j => (dead.samples j).2) i=gridN2303 i) i
theorem closeChildT_sound {raw T pools links k tmax rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag → ImpossibleT T k tmax (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    ImpossibleT T k tmax (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impT (scalarPoolCut_sound (pValid _ hp) nd ok)
def childT (tmax cap len op : Nat) : Nat :=
  if len==cap then 0 else if op==2 then tmax - 1 else tmax
abbrev LinkFn:=Nat → List (List Sig)
abbrev NodeContextT :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn × LinkFn
def evalMoveT (c : NodeContextT) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,cov,pools,qpools,l0,l1,l2):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let ct:=childT tmax cap len op
    let d:=ct==0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      let links:=if ct==0 then l0 else if ct==1 then l1 else l2
      (if ct==0 then closeChild pools links (cap-1) rest (movedChoice op a b) || rectEnd (cap-1) ((movedDecor op a b)::opKeep un ka kb a b ws) else closeChild pools links (cap-1) rest (movedChoice op a b))
theorem evalMoveT_sound {raw T r s ws pools l0 l1 l2 cap tmax a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0 < cap) (htmax : tmax ≤ 2)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag xs,xs ∈ l2 tag → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (targetEq : T=graph ∧ r=gridP2303 ∧ s=gridN2303)
    (test : evalMoveT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2)
      op a b (movedDecor op a b) ka kb=true) :
    ImpossibleT T (cap-1)
      (childT tmax cap (moveFront ws op a b ka kb).length op)
      (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=moved_full op a b
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz:=(live_size h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMoveT at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  let ct:=childT tmax cap child.length op
  have ht0 : (ct==0)=true → t=0:=by
    intro hct
    have hc0 : ct=0:=beq_iff_eq.mp hct
    change t ≤ ct at ht
    omega
  have sep:=cover_sound h rfl (pair_sep pairs) (ct==0) ht0
  let d:=ct==0
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by
    rw [sep,bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else if _ then true else _)=true at test
  rw [be,pp,fr] at test
  simp only [Bool.false_eq_true,ite_false,Bool.not_true,Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩:=List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost_good ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb)=true then true else _)=true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true,ite_false] at test
    have hct_le : ct ≤ 2:=by
      dsimp only [ct,childT]; split_ifs <;> omega
    by_cases hct0 : ct=0
    · have hctb : (ct==0)=true:=beq_iff_eq.mpr hct0
      rw [hctb] at test; simp only [ite_true] at test
      simp only [Bool.or_eq_true] at test
      rcases test with pass | term
      · exact closeChildT_sound pv lv0 nd' pass k t hk (hct0 ▸ ht) h'
      · rcases targetEq with ⟨rfl,rfl,rfl⟩
        have ready : ∀ w ∈ (movedDecor op a b :: rest), faithful gridP2303 gridN2303 w := by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hm
          · exact moved_faithful (faith a ha) (faith b hb) op
          · exact faith w (sub.subset hm)
        exact rectEnd_sound (ds:=movedDecor op a b :: rest) ndc ready term k t hk (hct0 ▸ ht) h
    · have hctb0 : (ct==0)=false:=beq_eq_false_iff_ne.mpr hct0
      rw [hctb0] at test; simp only [Bool.false_eq_true,ite_false] at test
      by_cases hct1 : ct=1
      · have hctb1 : (ct==1)=true:=beq_iff_eq.mpr hct1
        rw [hctb1] at test; simp only [ite_true] at test
        exact closeChildT_sound pv lv1 nd' test k t hk (hct1 ▸ ht) h'
      · have hctb1 : (ct==1)=false:=beq_eq_false_iff_ne.mpr hct1
        rw [hctb1] at test; simp only [Bool.false_eq_true,ite_false] at test
        have hct2 : ct=2:=by omega
        exact closeChildT_sound pv lv2 nd' test k t hk (hct2 ▸ ht) h'
def testPairT (ctx : NodeContextT) (a b : Decor) (d : Bool) : Bool :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let f:=evalMoveT ctx op a b z
  f false false&&f true false&&f false true&&f true true
def testRowT (ctx : NodeContextT) (a : Decor) (bs : List Decor) : Bool :=
  let unOk:=if ctx.2.1==0 then true else
    let z:=movedDecor 2 a a
    evalMoveT ctx 2 a a z false false&&evalMoveT ctx 2 a a z true true
  unOk&&bs.all (fun b => testPairT ctx a b false&&testPairT ctx a b true)
def testAllT (ctx : NodeContextT) : List Decor → Bool
  | [] => true
  | a :: bs => testRowT ctx a bs&&testAllT ctx bs
theorem all_unaryT {ctx} {ws : List Decor} (h : testAllT ctx ws=true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveT ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  have hne : (ctx.2.1==0)=false:=beq_eq_false_iff_ne.mpr (by omega)
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,hne,Bool.false_eq_true,ite_false] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binaryT {ctx} {ws : List Decor} (h : testAllT ctx ws=true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (d : Bool) : testPairT ctx a b d=true∨testPairT ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left; cases d <;> first | exact (h.1.2 _ bm).1 | exact (h.1.2 _ bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right; cases d <;> first | exact (h.1.2 _ haTail).1 | exact (h.1.2 _ haTail).2
      · exact ih h.2 haTail hbTail
theorem testPairT_at {ctx a b d} (h : testPairT ctx a b d=true) (ka kb : Bool) :
    evalMoveT ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPairT,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem nodeT_sound {raw T r s ws pools l0 l1 l2 cap tmax}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag xs,xs ∈ l2 tag → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (htmax : tmax ≤ 2)
    (targetEq : T=graph ∧ r=gridP2303 ∧ s=gridN2303)
    (checks : testAllT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) ws=true) :
    ImpossibleT T cap tmax (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk _ h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 → S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply enum_stepT nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    have hev:=evalMoveT_sound (op:=2) pairs faith nd ha ha (by simp) hc' htmax pv lv0 lv1 lv2 pro fresh targetEq (all_unaryT checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length=(childOne (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup:=by
        unfold moveFront
        have sub:=keep_sub ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [keep_mem] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
    rw [hf,hlenEq] at hev
    simpa [childT] using hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) a b d=true) :
        ImpossibleT T (cap-1) (if (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length=cap then 0 else tmax)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      have hf:=binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      have hev:=evalMoveT_sound (op:=if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' htmax pv lv0 lv1 lv2
        (eq ▸ pr) (eq ▸ fr) targetEq (testPairT_at test ka kb)
      have hop : ((if d then 1 else 0)==2)=false:=by cases d <;> rfl
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup:=by
          unfold moveFront
          have sub:=keep_sub ws a b ((if d then 1 else 0)==2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let r0:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup:=(nd.erase _).erase _
          have ar : a.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0:=by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [keep_mem] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
      rw [hf,hlenEq] at hev
      simpa [childT,hop] using hev
    rcases all_binaryT checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw:=childTwo_swap (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let rA:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup:=(nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA:=by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
          unfold childTwo
          let rB:=((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup:=(nd.erase b.1).erase a.1
          have br : b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
          have nk:=kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB:=by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd kb b.1 _ nk bx⟩
          rw [bin_comm d b.1 a.1] at hm
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA,←List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ fresh) hh
abbrev PackingT:=Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPackingT : PackingT:=(0,0,0,0,fun _ => 0)
def deadWires : List Decor:=wiresOf dead
def deadSigs : List Sig:=deadWires.map Prod.fst
def decodeSigs (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) zero
    let b:=ws.getD ((bits >>> 4) &&& 15) zero
    let op:=(bits >>> 8) &&& 3
    decodeSigs k (bits >>> 10) (ws ++ [if op=2 then neg a else bin (op==1) a b])
theorem decodeSigs_eq (n bits : Nat) (ws : List Decor) :
    decodeSigs n bits (ws.map Prod.fst)=(decodeBank n bits ws).map Prod.fst:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeSigs,decodeBank]
    have hget : ∀ i,(ws.map Prod.fst).getD i zero=(ws.getD i defaultDecor).1:=by
      intro i
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? <;> rfl
    have hcode : (if ((bits >>> 8) &&& 3)=2 then neg ((ws.map Prod.fst).getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3)==1) ((ws.map Prod.fst).getD (bits &&& 15) zero) ((ws.map Prod.fst).getD ((bits >>> 4) &&& 15) zero)) =
        (codeDecor ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) defaultDecor) (ws.getD ((bits >>> 4) &&& 15) defaultDecor)).1:=by
      rw [hget,hget]
      unfold codeDecor dbin dneg
      split
      · rfl
      · split <;> rfl
    rw [hcode,← List.map_singleton,← List.map_append]
    exact ih (bits >>> 10) _
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    selectLive bits (ws.map f)=(selectLive bits ws).map f:=by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,selectLive]
    split <;> simp [ih]
def readNodeT (levels : Nat → PackingT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw:=deadWires
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def stateSetT (levels : Nat → PackingT) (slot i : Nat) : List Sig :=
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+deadSigs.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (decodeSigs depth ops deadSigs)
theorem stateSetT_eq (levels : Nat → PackingT) (slot i : Nat) :
    stateSetT levels slot i=(readNodeT levels slot i).2.2.map Prod.fst:=by
  unfold stateSetT readNodeT
  rcases levels slot with ⟨num,depth,cw,offw,data⟩
  dsimp only
  have hlen : deadSigs.length=deadWires.length:=by simp [deadSigs]
  rw [hlen]
  dsimp only [deadSigs]
  rw [decodeSigs_eq,selectLive_map]
def linkedSetT (levels : Nat → PackingT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (dead.autos[pair.2]?).map fun perm => (stateSetT levels slot pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSetT_sound (levels : Nat → PackingT) (k tmax : Nat)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (earlier : ∀ i < (levels (3*k+tmax)).1,ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset)
    {pair out} (h : linkedSetT levels (3*k+tmax) pair=some out) :
    ImpossibleT (targetOf dead) k tmax out.toFinset:=by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedT (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def contextOfT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : NodeContextT :=
  let slot:=3 * k+tmax
  let raw:=deadWires
  let (num,depth,cw,offw,data):=levels slot
  let (ops,bank,ws):=readNodeT levels slot i
  let start:=num * (10 * depth+raw.length+depth)
  let pos:=start+num * offw+packedAt data (start+i * offw) offw
  let nr:=packedAt data pos 7
  let st:=pos+7
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule dead ops depth bank a b)
  let ls0:=fun tag => ((idx0 slot tag).bind (linkedSetT levels (3*(k-1)))).toList
  let ls1:=fun tag => ((idx1 slot tag).bind (linkedSetT levels (3*(k-1)+1))).toList
  let ls2:=fun tag => ((idx2 slot tag).bind (linkedSetT levels (3*(k-1)+2))).toList
  (k,tmax,ws.length,ws,preCov ws,rules,rules.map (summarizePool ws),ls0,ls1,ls2)
def prelimT (T : Sig) (c : NodeContextT) : Bool :=
  let ws:=c.2.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
def nodeVerifiedT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : Bool :=
  let c:=contextOfT levels idx0 idx1 idx2 k tmax i
  prelimT (targetOf dead) c&&(if k=0 then true else testAllT c c.2.2.2.1)
theorem nodeVerifiedT_sound (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat)
    (htmax : tmax ≤ 2)
    (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (prior0 : k > 0 → ∀ j < (levels (3*(k-1))).1,ImpossibleT (targetOf dead) (k-1) 0 (stateSetT levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 → ∀ j < (levels (3*(k-1)+1)).1,ImpossibleT (targetOf dead) (k-1) 1 (stateSetT levels (3*(k-1)+1) j).toFinset)
    (prior2 : k > 0 → ∀ j < (levels (3*(k-1)+2)).1,ImpossibleT (targetOf dead) (k-1) 2 (stateSetT levels (3*(k-1)+2) j).toFinset)
    (checked : nodeVerifiedT levels idx0 idx1 idx2 k tmax i=true) :
    ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset:=by
  rw [stateSetT_eq]
  simp only [nodeVerifiedT,prelimT,contextOfT,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at checked
  have hN:=checked.1.1
  have hT : targetOf dead ∉ (readNodeT levels (3*k+tmax) i).2.2.map Prod.fst:=checked.1.2
  by_cases h0 : k=0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k'=0:=by omega
    subst k'
    generalize he : ((readNodeT levels (3*0+tmax) i).2.2.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 → S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply nodeT_sound (raw:=vars dead.mask) samples _ hN hT _ _ _ _ htmax ⟨(by decide +kernel),gridLayout⟩ (by simpa only [h0,ite_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful dead) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1))))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1)=3*(k-1)+0:=by omega
    rw [h0'] at h
    exact linkedSetT_sound levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)+1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) 1 names (prior1 (by omega)) h
  · intro tag xs hx
    have e : ((idx2 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)+2)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) 2 names (prior2 (by omega)) h
def blockT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerifiedT levels idx0 idx1 idx2 k tmax start&&blockT levels idx0 idx1 idx2 k tmax (start+1) n
theorem blockT_at {levels idx0 idx1 idx2 k tmax start n} (h : blockT levels idx0 idx1 idx2 k tmax start n=true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+n) : nodeVerifiedT levels idx0 idx1 idx2 k tmax i=true:=by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockT,Bool.and_eq_true] at h
    by_cases eq : i=start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)
theorem blockT_merge {levels idx0 idx1 idx2 k tmax start a b}
    (ha : blockT levels idx0 idx1 idx2 k tmax start a=true)
    (hb : blockT levels idx0 idx1 idx2 k tmax (start+a) b=true) :
    blockT levels idx0 idx1 idx2 k tmax start (a+b)=true:=by
  induction a generalizing start with
  | zero => simpa [blockT] using hb
  | succ a ih =>
    simp only [blockT,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
theorem makeBlockT {levels idx0 idx1 idx2 k tmax start n}
    (h : ∀ i,start ≤ i → i < start+n → nodeVerifiedT levels idx0 idx1 idx2 k tmax i=true) :
    blockT levels idx0 idx1 idx2 k tmax start n=true:=by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockT,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
theorem forestT_all (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (top : Nat)
    (prior : Nat → Nat)
    (lo : ∀ m,Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior=true)
    (tabs : ∀ k ≤ top,∀ tmax ≤ 2,blockT levels idx0 idx1 idx2 k tmax 0 (levels (3*k+tmax)).1=true) :
    ∀ k ≤ top,∀ tmax ≤ 2,∀ i < (levels (3*k+tmax)).1,ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs:=chart_pairs valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => col_sound ci prior lo (valid.1.2 ci hc)
  have names:=valid.2
  intro k
  induction k with
  | zero =>
    intro hk tmax htmax i hi
    have hb:=tabs 0 hk tmax htmax
    exact nodeVerifiedT_sound levels idx0 idx1 idx2 0 tmax i htmax pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (blockT_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tmax htmax i hi
    have hb:=tabs (k+1) hk tmax htmax
    exact nodeVerifiedT_sound levels idx0 idx1 idx2 (k+1) tmax i htmax pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (fun _ j hj => ih (by omega) 2 (by decide) j hj)
      (blockT_at hb i (Nat.zero_le i) (by simpa using hi))
abbrev Memo2303 := Sig × Nat × Nat × List Sig × List Sig
def memo2303 (ws : List Decor) (k : Nat) (p : BoundPool) : Memo2303 :=
  let d := p.domain
  let av := p.wires.map (masked d)
  let clean := fun (w : Sig) => let y := masked d w
                                y==zero || y==d || av.contains y
  (d,k+p.paid,p.bound+ws.countP (fun w => isMaskedConstant d w.1),
    av,(ws.map Prod.fst).filter (fun w => !(clean w)))
def worth2303 (cap n : Nat) (cov : CovPair) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>cap then false else
  let d := true
  (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) == BitVec.allOnes 768
abbrev Ax2303 := Decor × Decor
abbrev Four2303 := Nat × Nat × Nat × Nat
def couples2303 : List Decor → List Ax2303
  | [] => []
  | a::l => l.map (fun b => (a,b)) ++ couples2303 l
def liftSig2303 (w : Sig) : Bits := BitVec.ofNat 768 w.toNat
def laneEq2303 (r full a b : Nat) := fullMarks r (full ^^^ (a ^^^ b))
def zeroFour2303 (x : Four2303) := (x.1 ||| x.2.1 ||| x.2.2.1 ||| x.2.2.2)==0
def wideWorth2303 (n cap op r full : Nat) (v : CovPair) (a b : PackedSig) (ka kb : Bool) :=
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>cap then 0 else
  let d := true
  let c := getCov v d
  let cover : PackedCov := (r*c.1.toNat,r*c.2.1.toNat,r*c.2.2.toNat)
  fullMarks r (takePacked cover (packedColumn d a) (packedColumn d b) un ka kb |||
    packedColumn d (packedOp full op a b))
def include2303 (r full z : Nat) (wires : List Sig) (seen : Nat) :=
  wires.foldl (fun m w => m ||| laneEq2303 r full z (r*w.toNat)) seen
def maskKeep2303 (r full a b : Nat) (un ka kb : Bool) (miss : List Sig) :=
  miss.foldl (fun m w =>
    let target := r*w.toNat
    m &&& ((if ka then 0 else laneEq2303 r full a target) |||
      (if un || kb then 0 else laneEq2303 r full b target))) r
def shade2303 (r cost top cv free : Nat) (ready : Bool) (loss : Nat) :=
  if ready && cost+loss+1<top then r else
  if cost+loss<top then free else if cost+loss==top then cv else 0
def wideRule2303 (r full a b z : Nat) (un : Bool) (ps : Memo2303) (todo : Four2303) : Four2303 :=
  let (dom,cost,top,av,miss) := ps
  if cost>=top+1 || miss.length>(if un then 1 else 2) then todo else
  let d := r*dom.toNat
  let cm := fun m => laneEq2303 r full m 0 ||| laneEq2303 r full m d
  let zm := z &&& d
  let cz := cm zm
  let free := include2303 r full zm av cz
  let shade := shade2303 r cost top cz free miss.isEmpty
  let ca := cm (a &&& d)
  let cb := cm (b &&& d)
  let step := fun (t : Nat) (ka kb : Bool) =>
    if t==0 then 0 else
    let ca := if ka then 0 else ca
    let cb := if un || kb then 0 else cb
    let kill := (((r ^^^ (ca ||| cb)) &&& shade 0) |||
      ((ca ^^^ cb) &&& shade 1) ||| ((ca &&& cb) &&& shade 2)) &&&
      maskKeep2303 r full a b un ka kb miss
    t ^^^ (t &&& kill)
  (step todo.1 false false,step todo.2.1 true false,step todo.2.2.1 false true,step todo.2.2.2 true true)
def wideRules2303 (r full a b z : Nat) (un : Bool) (todo : Four2303) : List Memo2303 → Four2303
  | [] => todo
  | p::ps => if zeroFour2303 todo then todo else wideRules2303 r full a b z un (wideRule2303 r full a b z un p todo) ps
lemma keyFold2303 (ws : List Sig) (c : Nat) :
    ws.foldl (fun v w => v+keyWord w) c=c+(ws.map keyWord).sum := by
  induction ws generalizing c with
  | nil => simp
  | cons w l ih => simp [ih,Nat.add_assoc]
lemma keySum2303 (ws : List Sig) : keySet ws=(ws.map keyWord).sum := by
  simp [keySet,keyFold2303]
lemma keyPerm2303 {ws vs : List Decor} (h : ws.Perm vs) :
    keySet (ws.map Prod.fst)=keySet (vs.map Prod.fst) := by
  rw [keySum2303,keySum2303]
  exact ((h.map Prod.fst).map keyWord).sum_eq
lemma keyCons2303 (a : Sig) (ws : List Sig) : keySet (a::ws)=keyWord a+keySet ws := by
  simp [keySum2303]
def deltaKey2303 (total : Nat) (a b z : Sig) (un ka kb : Bool) :=
  total+keyWord z-(if ka then 0 else keyWord a)-(if un || kb then 0 else keyWord b)
lemma deltaKey_ok2303 {ws : List Decor} {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (un ka kb : Bool) (ne : un=false → a≠b) (z : Sig) :
    deltaKey2303 (keySet (ws.map Prod.fst)) a.1 b.1 z un ka kb =
      keySet (z::(opKeep un ka kb a b ws).map Prod.fst) := by
  have first := keyPerm2303 (delOne_perm a ha)
  have second := keyPerm2303 (delOne_perm b hb)
  simp only [List.map_cons,keyCons2303] at first second
  cases un
  · have both := keyPerm2303 (delTwo_perm a b ha hb (ne rfl))
    simp only [List.map_cons,keyCons2303] at both
    cases ka <;> cases kb <;>
      simp only [deltaKey2303,opKeep,delOne,delTwo,Bool.false_or,Bool.false_eq_true,
        ite_false,ite_true,keyCons2303] <;> omega
  · cases ka <;> cases kb <;>
      simp only [deltaKey2303,opKeep,delOne,Bool.true_or,Bool.false_eq_true,ite_false,
        ite_true,keyCons2303] <;> omega
def linked2303 (ws : List Decor) (links : Nat → List (List Sig)) (a b : Decor) (w : Sig)
    (un ka kb : Bool) :=
  let other := (opKeep un ka kb a b ws).map Prod.fst
  let st := w::other
  let tag := if un || a.1!=b.1 then deltaKey2303 (keySet (ws.map Prod.fst)) a.1 b.1 w un ka kb else keySet st
  (links tag).any (fun v => v==other++[w] || sameWords st v)
lemma linked_ok2303 {ws links a b w un ka kb} (ha : a∈ws) (hb : b∈ws)
    (ok : linked2303 ws links a b w un ka kb=true) :
    let st := w::(opKeep un ka kb a b ws).map Prod.fst
    (links (keySet st)).any (sameWords st)=true := by
  let rest := (opKeep un ka kb a b ws).map Prod.fst
  have key : (if un || a.1!=b.1 then deltaKey2303 (keySet (ws.map Prod.fst)) a.1 b.1 w un ka kb
        else keySet (w::rest))=keySet (w::rest) := by
    split
    next h =>
      apply deltaKey_ok2303 ha hb
      intro hu eq
      simp [hu,eq] at h
    next => rfl
  change (links _).any (fun v => v==rest++[w] || sameWords (w::rest) v)=true at ok
  rw [key] at ok
  obtain ⟨v,vm,hit⟩ := List.any_eq_true.mp ok
  refine List.any_eq_true.mpr ⟨v,vm,?_⟩
  simp only [Bool.or_eq_true] at hit
  rcases hit with eq | yes
  · rw [beq_iff_eq.mp eq]
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    exact ⟨fun _ e => e.symm,fun _ e => e.symm⟩
  · exact yes
def wideFamily2303 (c : NodeContext) (ps : List Memo2303) (op : Nat) (ops : List Ax2303) :=
  let (cap,n,ws,cov,_,links) := c
  let r := units ops.length
  let full := r*(BitVec.allOnes 768).toNat
  let sa := packedSig (fun e : Ax2303 => e.1.2) ops
  let sb := packedSig (fun e : Ax2303 => e.2.2) ops
  let a := combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) ops
  let b := combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) ops
  let un := op==2
  let z := if un then (r*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b
  let worth := wideWorth2303 n cap op r full cov sa sb
  let todo : Four2303 := (worth false false,if un then 0 else worth true false,
                       if un then 0 else worth false true,worth true true)
  let left := wideRules2303 r full a b z un todo ps
  let verify := fun (ka kb : Bool) (t : Nat) => if t==0 then true else
    onMarks (fun e : Ax2303 =>
      let w := (movedDecor op e.1 e.2).1
      if !properB w || ws.any (fun v => v.1==w) then true else
      linked2303 ws links e.1 e.2 w un ka kb || rectEnd (cap-1) (movedDecor op e.1 e.2 :: opKeep un ka kb e.1 e.2 ws)) t ops
  verify false false left.1 && verify true false left.2.1 &&
    verify false true left.2.2.1 && verify true true left.2.2.2
lemma xorHit2303 (a b : Bits) :
    (BitVec.allOnes 768 ^^^ (a ^^^ b) == BitVec.allOnes 768) = (a==b) := by
  by_cases eq : a=b
  · simp [eq]
  · rw [beq_eq_false_iff_ne.mpr eq]
    apply beq_eq_false_iff_ne.mpr
    intro h
    apply eq
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have v := congrArg (fun x : Bits => x.getLsbD j) h
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_allOnes,hj,decide_true] at v
    cases ha : a.getLsbD j <;> cases hb : b.getLsbD j <;> simp_all
lemma eqLanes2303 {α} (a b : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (laneEq2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes a xs) (combineLanes b xs)).testBit (769*i) = (a xs[i] == b xs[i]) := by
  simp only [laneEq2303,broadcast,lanes_xor,mark_at _ _ _ hi,xorHit2303]
lemma liftEq2303 (a b : Sig) : (liftSig2303 a==liftSig2303 b)=(a==b) := by
  by_cases e : a=b
  · simp [e]
  · have neq : liftSig2303 a≠liftSig2303 b := by
      intro h
      have H := congrArg BitVec.toNat h
      have la : a.toNat<2^768 := lt_trans a.isLt (by decide +kernel)
      have lb : b.toNat<2^768 := lt_trans b.isLt (by decide +kernel)
      apply e
      apply BitVec.eq_of_toNat_eq
      simpa [liftSig2303,Nat.mod_eq_of_lt la,Nat.mod_eq_of_lt lb] using H
    simp [neq,e]
lemma lift_toNat2303 (a : Sig) : (liftSig2303 a).toNat=a.toNat := by
  have lt : a.toNat<2^768 := lt_trans a.isLt (by decide +kernel)
  simp [liftSig2303,Nat.mod_eq_of_lt lt]
lemma bitEqConst2303 {α} (a : α → Sig) (v : Sig) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (laneEq2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun x => liftSig2303 (a x)) xs) (units xs.length*v.toNat)).testBit (769*i) =
      (a xs[i]==v) := by
  rw [←lift_toNat2303 v,broadcast (liftSig2303 v) xs,eqLanes2303 _ _ _ _ hi,liftEq2303]
lemma worthAt2303 (n cap op : Nat) (v : CovPair) (xs : List Ax2303) (i : Nat) (hi : i<xs.length)
    (ka kb : Bool) :
    (wideWorth2303 n cap op (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat) v
      (packedSig (fun e : Ax2303 => e.1.2) xs) (packedSig (fun e : Ax2303 => e.2.2) xs)
      ka kb).testBit (769*i) =
      worth2303 cap n v op xs[i].1 xs[i].2 (movedDecor op xs[i].1 xs[i].2) ka kb := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  by_cases big : len>cap
  · simp only [wideWorth2303,worth2303,show 1+(n-(if ka then 0 else 1)-
        (if (op==2) || kb then 0 else 1))>cap from big,ite_true,Nat.zero_testBit]
  · let d := true
    simp only [wideWorth2303,worth2303,show ¬1+(n-(if ka then 0 else 1)-
        (if (op==2) || kb then 0 else 1))>cap from big,ite_false]
    have cp : (units xs.length*(getCov v d).1.toNat,units xs.length*(getCov v d).2.1.toNat,
        units xs.length*(getCov v d).2.2.toNat) =
        packedCov (fun _ : Ax2303 => getCov v d) xs := by simp only [packedCov,broadcast]
    rw [cp,packed_op (fun e : Ax2303 => e.1) (fun e : Ax2303 => e.2),packed_column,
        packed_column,packed_column,takePacked_ok,lanes_or,mark_at _ _ _ hi]
lemma includeBit2303 {α} (f : α → Sig) (vs : List Sig) (xs : List α) (i) (hi : i<xs.length)
    (seen : Nat) :
    (include2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun x => liftSig2303 (f x)) xs) vs seen).testBit (769*i) =
    (seen.testBit (769*i) || vs.any (fun w => f xs[i]==w)) := by
  induction vs generalizing seen with
  | nil => simp [include2303]
  | cons w l ih =>
    change (include2303 _ _ _ l _).testBit _ = _
    rw [ih,Nat.testBit_or,bitEqConst2303 _ _ _ _ hi,List.any_cons,Bool.or_assoc]
lemma keepBit2303 (xs : List Ax2303) (i) (hi : i<xs.length) (miss : List Sig) (un ka kb : Bool) :
    (maskKeep2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) xs)
      (combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) xs) un ka kb miss).testBit (769*i) =
      miss.all (fun w => (!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let a := combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) xs
  let b := combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) xs
  let f := fun (w : Sig) => (if ka then 0 else laneEq2303 r full a (r*w.toNat)) |||
       (if un || kb then 0 else laneEq2303 r full b (r*w.toNat))
  have get (w) : (f w).testBit (769*i)=
      ((!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
    cases ka <;> cases un <;> cases kb <;>
      simp only [f,r,full,a,b,Nat.testBit_or,bitEqConst2303 _ _ _ _ hi,
        Bool.false_eq_true,ite_false,ite_true,Bool.false_or,Bool.true_or,
        Nat.zero_testBit,Bool.not_true,Bool.not_false,Bool.false_and,Bool.true_and]
  have aux (l : List Sig) (m : Nat) : (l.foldl (fun q w => q &&& f w) m).testBit (769*i)=
      (m.testBit (769*i) && l.all fun w => (!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
    induction l generalizing m with
    | nil => simp
    | cons w l ih => rw [List.foldl_cons,ih,Nat.testBit_and,get,List.all_cons,Bool.and_assoc]
  exact (aux miss r).trans (by simp [r,unit_bit _ _ hi])
lemma liftedAnd2303 (a b : Sig) : liftSig2303 (a &&& b) = liftSig2303 a &&& liftSig2303 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lift_toNat2303,BitVec.toNat_and]
lemma liftedOr2303 (a b : Sig) : liftSig2303 (a ||| b) = liftSig2303 a ||| liftSig2303 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lift_toNat2303,BitVec.toNat_or]
lemma liftedNeg2303 (a : Sig) : liftSig2303 (neg a) = liftSig2303 one ^^^ liftSig2303 a := by
  have eq : neg a=one ^^^ a := BitVec.allOnes_xor.symm
  apply BitVec.eq_of_toNat_eq
  simp only [eq,lift_toNat2303,BitVec.toNat_xor]
lemma maskedLanes2303 {α} (a : α → Sig) (xs : List α) (d : Sig) :
    combineLanes (fun x => liftSig2303 (a x)) xs &&& (units xs.length*d.toNat) =
      combineLanes (fun x => liftSig2303 (masked d (a x))) xs := by
  rw [←lift_toNat2303 d,broadcast (liftSig2303 d) xs,lanes_and]
  simp only [masked,liftedAnd2303,BitVec.and_comm]
lemma opLanes2303 (xs : List Ax2303) (op : Nat) :
    let a := combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) xs
    let b := combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) xs
    (if op==2 then (units xs.length*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b) =
      combineLanes (fun e : Ax2303 => liftSig2303 (movedDecor op e.1 e.2).1) xs := by
  by_cases un : op=2
  · simp only [un,beq_self_eq_true,ite_true,movedDecor,codeDecor,dneg,liftedNeg2303]
    rw [←lift_toNat2303 one,broadcast (liftSig2303 one) xs,lanes_xor]
  · have ne : (op==2)=false := beq_eq_false_iff_ne.mpr un
    cases b : op==1 <;>
      simp only [ne,Bool.false_eq_true,ite_false,b,ite_true,movedDecor,codeDecor,un,dbin,bin,
        liftedOr2303,liftedAnd2303,lanes_or,lanes_and]
def absent2303 (p : BoundPool) (ws : List Decor) :=
  (ws.map Prod.fst).filter (fun w => !availableB p.domain p.wires w)
def payable2303 (cost top : Nat) (zc free ready : Bool) (loss : Nat) :=
  if ready && cost+loss+1<top then true else
  if cost+loss<top then free else if cost+loss==top then zc else false
lemma scalar_fast2303 {p : BoundPool} {ws : List Decor} {k op a b ka kb}
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws)
    (keep : (absent2303 p ws).all (fun w =>
      (!ka && (a.1==w)) || (!((op==2) || kb) && (b.1==w)))=true)
    (test : let const := fun w : Decor => isMaskedConstant p.domain w.1
      let z := choiceVal (movedChoice op a b)
      payable2303 (k+p.paid) (p.bound+ws.countP const) (isMaskedConstant p.domain z)
        (availableB p.domain p.wires z) (absent2303 p ws).isEmpty
        (constantLoss const a ka+constantLoss const b ((op==2)||kb))=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let rest := opKeep (op==2) ka kb a b ws
  let miss := absent2303 p ws
  let loss := constantLoss const a ka+constantLoss const b ((op==2)||kb)
  have failed {v} (hm : v∈ws.map Prod.fst) (no : availableB p.domain p.wires v=false) : v∈miss := by
    simpa [miss,absent2303,List.mem_filter,hm,no]
  have known : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro v vm
    obtain ⟨member,ia,ib⟩ := (kept_value nd ha hb (op==2) ka kb v).mp vm
    cases ev : availableB p.domain p.wires v
    · have bad := List.all_eq_true.mp keep v (failed member ev)
      simp only [Bool.or_eq_true,Bool.and_eq_true] at bad
      rcases bad with ⟨no,eq⟩ | ⟨no,eq⟩
      ·
        have vv : v=a.1 := (beq_iff_eq.mp eq).symm
        exact False.elim (by rcases ia with noeq|on <;> simp_all)
      ·
        have vv : v=b.1 := (beq_iff_eq.mp eq).symm
        exact False.elim (by rcases ib with on|noeq|on <;> simp_all)
    · rfl
  have all_of_empty (empty : miss.isEmpty=true) (w) (hm : w∈ws) :
      availableB p.domain p.wires w.1=true := by
    cases ev : availableB p.domain p.wires w.1
    · have bad := failed (List.mem_map_of_mem (f:=Prod.fst) hm) ev
      have nil : miss=[] := List.isEmpty_iff.mp empty
      rw [nil] at bad
      contradiction
    · rfl
  have counts := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb)
        ≤ rest.countP const at counts
  have mass : ws.countP const ≤ rest.countP const+loss := by dsimp [loss]; omega
  change payable2303 (k+p.paid) (p.bound+ws.countP const) (isMaskedConstant p.domain z)
    (availableB p.domain p.wires z) miss.isEmpty loss=true at test
  unfold payable2303 at test
  have cheap : k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+rest.countP const+(isMaskedConstant p.domain z).toNat := by
    split at test
    next h =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      have le := h.2
      cases availableB p.domain p.wires z <;> cases isMaskedConstant p.domain z <;> simp <;> omega
    next =>
      split at test
      next le => simp [test]; omega
      next =>
        split at test
        next eq =>
          have e := beq_iff_eq.mp eq
          have av : availableB p.domain p.wires z=true :=
            by simp only [availableB,isMaskedConstant,Bool.or_eq_true] at test ⊢; tauto
          simp [av,test]; omega
        next => contradiction
  have buy : (!(!availableB p.domain p.wires z) || choiceOK p.domain p.wires (movedChoice op a b))=true := by
    cases az : availableB p.domain p.wires z
    · have zc : isMaskedConstant p.domain z=false := by
        have ac := az
        change (isMaskedConstant p.domain z || _) = false at ac
        simp only [Bool.or_eq_false_iff] at ac
        exact ac.1
      have empty : miss.isEmpty=true := by
        cases m : miss.isEmpty
        · simp [payable2303,az,zc,m] at test
        · rfl
      have all := all_of_empty empty
      simp [choiceOK,movedChoice,all _ ha,all _ hb]
    · simp
  simpa only [scalarPoolCut,z,rest,known,Bool.and_true,Bool.true_and,Bool.and_eq_true,
    decide_eq_true_eq,List.countP_cons,List.countP_map,Function.comp_def,
    show (if isMaskedConstant p.domain z then 1 else 0)=(isMaskedConstant p.domain z).toNat by cases isMaskedConstant p.domain z <;> rfl,
    Nat.add_assoc] using And.intro cheap buy
def partFour2303 (x : Four2303) (ka kb : Bool) :=
  if ka then (if kb then x.2.2.2 else x.2.1) else (if kb then x.2.2.1 else x.1)
lemma shadeAt2303 {r i cost top cz free ready loss} (unit : r.testBit i=true) :
    (shade2303 r cost top cz free ready loss).testBit i =
      payable2303 cost top (cz.testBit i) (free.testBit i) ready loss := by
  simp only [shade2303,payable2303]
  repeat' split
  all_goals first | assumption | rfl | exact Nat.zero_testBit _
lemma chosenShade2303 {r i a b s t u : Nat} (unit : r.testBit i=true) :
    ((((r ^^^ (a ||| b)) &&& s) ||| ((a ^^^ b) &&& t) ||| ((a &&& b) &&& u)).testBit i) =
    (if a.testBit i then (if b.testBit i then u.testBit i else t.testBit i)
     else if b.testBit i then t.testBit i else s.testBit i) := by
  simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,unit]
  cases a.testBit i <;> cases b.testBit i <;> simp
lemma killedBit2303 {t k i : Nat} (start : t.testBit i=true)
    (finish : (t ^^^ (t &&& k)).testBit i=false) : k.testBit i=true := by
  simpa [Nat.testBit_xor,Nat.testBit_and,start] using finish
lemma dropLoss2303 (const : Decor → Bool) (w : Decor) (keep : Bool) :
    constantLoss const w keep = (if keep then false else const w).toNat := by
  cases keep <;> rfl
abbrev lanes2303 {α} (f : α → Sig) (xs : List α) := combineLanes (fun x => liftSig2303 (f x)) xs
def constantMask2303 (r full x d : Nat) := laneEq2303 r full x 0 ||| laneEq2303 r full x d
lemma wireEqSym2303 (a b : Sig) : (a==b)=(b==a) := by
  by_cases h : a=b
  · simp [h]
  · simp [h,Ne.symm h]
lemma constantAt2303 {α} (f : α → Sig) (xs : List α) (i : Nat) (hi : i<xs.length) (d : Sig) :
    let r := units xs.length
    (constantMask2303 r (r*(BitVec.allOnes 768).toNat) (lanes2303 f xs &&& (r*d.toNat))
        (r*d.toNat)).testBit (769*i) = isMaskedConstant d (f xs[i]) := by
  dsimp only
  have z : units xs.length*zero.toNat=0 := by simp [zero]
  simp only [constantMask2303,Nat.testBit_or,maskedLanes2303,←z,bitEqConst2303 _ _ _ _ hi,isMaskedConstant]
lemma freeAt2303 {α} (f : α → Sig) (xs : List α) (i : Nat) (hi : i<xs.length)
    (d : Sig) (vs : List Sig) :
    let r := units xs.length
    let full := r*(BitVec.allOnes 768).toNat
    let zm := lanes2303 f xs &&& (r*d.toNat)
    (include2303 r full zm (vs.map (masked d)) (constantMask2303 r full zm (r*d.toNat))).testBit (769*i) =
      availableB d vs (f xs[i]) := by
  dsimp only
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let zm := lanes2303 f xs &&& (r*d.toNat)
  have I := includeBit2303 (fun x => masked d (f x)) (vs.map (masked d)) xs i hi
    (constantMask2303 r full zm (r*d.toNat))
  rw [←maskedLanes2303] at I
  refine I.trans ?_
  rw [show (constantMask2303 r full zm (r*d.toNat)).testBit (769*i)=isMaskedConstant d (f xs[i]) from constantAt2303 f xs i hi d]
  simp only [isMaskedConstant,availableB,List.any_map,Function.comp_def]
  congr 1
  congr 1
  funext v
  exact wireEqSym2303 _ _
lemma memoAbsent2303 (ws : List Decor) (k : Nat) (p : BoundPool) :
    (memo2303 ws k p).2.2.2.2=absent2303 p ws := by
  simp only [memo2303,absent2303,availableB]
  congr 1
  funext w
  congr 1
  have same (l : List Sig) (w : Sig) : l.contains w=l.any (fun v => v==w) := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.contains_cons,List.any_cons,ih,wireEqSym2303 w a]
  simp only [same]
lemma partStep2303 (todo : Four2303) (step : Nat → Bool → Bool → Nat) (ka kb : Bool) :
    partFour2303 (step todo.1 false false,step todo.2.1 true false,
      step todo.2.2.1 false true,step todo.2.2.2 true true) ka kb =
      step (partFour2303 todo ka kb) ka kb := by cases ka <;> cases kb <;> rfl
lemma killedRule2303 {p : BoundPool} {ws : List Decor} {k op : Nat} (xs : List Ax2303)
    (i : Nat) (hi : i<xs.length) (ka kb : Bool) (todo : Four2303)
    (nd : (ws.map Prod.fst).Nodup) (ha : xs[i].1∈ws) (hb : xs[i].2∈ws)
    (beginning : (partFour2303 todo ka kb).testBit (769*i)=true) :
    let r := units xs.length
    let full := r*(BitVec.allOnes 768).toNat
    let a := lanes2303 (fun e : Ax2303 => e.1.1) xs
    let b := lanes2303 (fun e : Ax2303 => e.2.1) xs
    let z := lanes2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs
    let cut := wideRule2303 r full a b z (op==2) (memo2303 ws k p) todo
    (partFour2303 cut ka kb).testBit (769*i)=false →
      scalarPoolCut p k ((opKeep (op==2) ka kb xs[i].1 xs[i].2 ws).map Prod.fst)
        (movedChoice op xs[i].1 xs[i].2)=true := by
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let a := lanes2303 (fun e : Ax2303 => e.1.1) xs
  let b := lanes2303 (fun e : Ax2303 => e.2.1) xs
  let z := lanes2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs
  let const := fun v : Decor => isMaskedConstant p.domain v.1
  let dom := r*p.domain.toNat
  let am := constantMask2303 r full (a &&& dom) dom
  let bm := constantMask2303 r full (b &&& dom) dom
  let zm := constantMask2303 r full (z &&& dom) dom
  let av := p.wires.map (masked p.domain)
  let fm := include2303 r full (z &&& dom) av zm
  let miss := absent2303 p ws
  let sel := maskKeep2303 r full a b (op==2) ka kb miss
  let sh := shade2303 r (k+p.paid) (p.bound+ws.countP const) zm fm miss.isEmpty
  let aa := if ka then 0 else am
  let bb := if (op==2)||kb then 0 else bm
  let kill := ((((r ^^^ (aa ||| bb)) &&& sh 0) ||| ((aa ^^^ bb) &&& sh 1) ||| ((aa &&& bb) &&& sh 2)) &&& sel)
  let step := fun (v : Nat) (x y : Bool) =>
    if v==0 then 0 else
      let ax := if x then 0 else am
      let bx := if (op==2)||y then 0 else bm
      let kx := ((((r ^^^ (ax ||| bx)) &&& sh 0) ||| ((ax ^^^ bx) &&& sh 1) ||| ((ax &&& bx) &&& sh 2)) &&&
        maskKeep2303 r full a b (op==2) x y miss)
      v ^^^ (v &&& kx)
  let t := partFour2303 todo ka kb
  have unit : r.testBit (769*i)=true := unit_bit xs.length i hi
  have ca : am.testBit (769*i)=const xs[i].1 := constantAt2303 (fun e : Ax2303 => e.1.1) xs i hi _
  have cb : bm.testBit (769*i)=const xs[i].2 := constantAt2303 (fun e : Ax2303 => e.2.1) xs i hi _
  have cz : zm.testBit (769*i)=isMaskedConstant p.domain (choiceVal (movedChoice op xs[i].1 xs[i].2)) :=
    (constantAt2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs i hi _).trans (by rw [moved_full])
  have free : fm.testBit (769*i)=availableB p.domain p.wires (choiceVal (movedChoice op xs[i].1 xs[i].2)) :=
    (freeAt2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs i hi _ _).trans (by rw [moved_full])
  have lose (n) : (sh n).testBit (769*i)=payable2303 (k+p.paid) (p.bound+ws.countP const)
      (isMaskedConstant p.domain (choiceVal (movedChoice op xs[i].1 xs[i].2)))
      (availableB p.domain p.wires (choiceVal (movedChoice op xs[i].1 xs[i].2))) miss.isEmpty n := by
    rw [show (sh n).testBit (769*i)=_ from shadeAt2303 unit,cz,free]
  have amount (w sw : Nat) (flag : Bool) (prop : Bool) (e : sw.testBit (769*i)=prop) :
      (if flag then 0 else sw).testBit (769*i)=(if flag then false else prop) := by
    cases flag <;> simp [e]
  have notzero : t≠0 := by intro h; have := beginning; change t.testBit _=true at this; simp [h] at this
  dsimp only
  have memoE : memo2303 ws k p=(p.domain,k+p.paid,p.bound+ws.countP const,av,miss) :=
    congrArg (fun v => (p.domain,k+p.paid,p.bound+ws.countP const,av,v)) (memoAbsent2303 ws k p)
  rw [memoE]
  dsimp only [wideRule2303]
  by_cases skip : (decide (k+p.paid≥p.bound+ws.countP const+1) || decide (miss.length>(if op==2 then 1 else 2)))=true
  · rw [if_pos skip]
    intro f; exact False.elim (Bool.noConfusion (beginning.symm.trans f))
  · rw [if_neg skip]
    change (partFour2303 (step todo.1 false false,step todo.2.1 true false,
      step todo.2.2.1 false true,step todo.2.2.2 true true) ka kb).testBit (769*i)=false → _
    rw [partStep2303 todo step ka kb]
    change (if t==0 then 0 else t ^^^ (t &&& kill)).testBit (769*i)=false → _
    simp only [beq_eq_false_iff_ne.mpr notzero,Bool.false_eq_true,ite_false]
    intro h
    have v := killedBit2303 beginning h
    change ( _ &&& sel).testBit (769*i)=true at v
    simp only [Nat.testBit_and,Bool.and_eq_true] at v
    have yes : sel.testBit (769*i)=true := v.2
    rw [show sel.testBit (769*i)=_ from keepBit2303 xs i hi miss (op==2) ka kb] at yes
    apply scalar_fast2303 nd ha hb yes
    have pick := v.1
    rw [chosenShade2303 unit,amount 0 am ka _ ca,amount 0 bm ((op==2)||kb) _ cb] at pick
    simp only [lose] at pick
    have clear (f : Nat → Bool) (u v : Bool)
        (eq : (if u then (if v then f 2 else f 1) else if v then f 1 else f 0)=true) :
        f (u.toNat+v.toNat)=true := by cases u <;> cases v <;> exact eq
    dsimp only
    simp only [dropLoss2303]
    exact clear _ (if ka then false else const xs[i].1) (if (op==2)||kb then false else const xs[i].2) pick
abbrev wideArgs2303 (xs : List Ax2303) (op : Nat) :=
  (units xs.length,units xs.length*(BitVec.allOnes 768).toNat,
    lanes2303 (fun e : Ax2303 => e.1.1) xs,lanes2303 (fun e : Ax2303 => e.2.1) xs,
    lanes2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs)
def runRules2303 (xs : List Ax2303) (op : Nat) (todo : Four2303) (ps : List Memo2303) :=
  let (r,full,a,b,z) := wideArgs2303 xs op
  wideRules2303 r full a b z (op==2) todo ps
def runRule2303 (xs : List Ax2303) (op : Nat) (todo : Four2303) (p : Memo2303) :=
  let (r,full,a,b,z) := wideArgs2303 xs op
  wideRule2303 r full a b z (op==2) p todo
lemma finishedRule2303 {ps : List BoundPool} {ws : List Decor} {k op : Nat}
    (xs : List Ax2303) (i : Nat) (hi : i<xs.length) (ka kb : Bool) (todo : Four2303)
    (nd : (ws.map Prod.fst).Nodup) (ha : xs[i].1∈ws) (hb : xs[i].2∈ws)
    (beginning : (partFour2303 todo ka kb).testBit (769*i)=true)
    (done : (partFour2303 (runRules2303 xs op todo (ps.map (memo2303 ws k))) ka kb).testBit (769*i)=false) :
    ∃ p∈ps, scalarPoolCut p k ((opKeep (op==2) ka kb xs[i].1 xs[i].2 ws).map Prod.fst)
      (movedChoice op xs[i].1 xs[i].2)=true := by
  induction ps generalizing todo with
  | nil => exact False.elim (Bool.noConfusion (beginning.symm.trans done))
  | cons p ps ih =>
    let next := runRule2303 xs op todo (memo2303 ws k p)
    change (partFour2303 (if zeroFour2303 todo then todo else runRules2303 xs op next (ps.map (memo2303 ws k))) ka kb).testBit (769*i)=false at done
    split at done
    next => exact False.elim (Bool.noConfusion (beginning.symm.trans done))
    next =>
      cases he : (partFour2303 next ka kb).testBit (769*i)
      · exact ⟨p,by simp,killedRule2303 xs i hi ka kb todo nd ha hb beginning he⟩
      · obtain ⟨v,vm,cut⟩ := ih next he done
        exact ⟨v,List.mem_cons_of_mem _ vm,cut⟩
def familyCheck2303 (c : NodeContext) (op : Nat) (e : Ax2303) (ka kb : Bool) :=
  let w := (movedDecor op e.1 e.2).1
  if !properB w || c.2.2.1.any (fun v => v.1==w) then true else
  linked2303 c.2.2.1 c.2.2.2.2.2 e.1 e.2 w (op==2) ka kb || rectEnd (c.1-1) (movedDecor op e.1 e.2 :: opKeep (op==2) ka kb e.1 e.2 c.2.2.1)
def todo2303 (c : NodeContext) (op : Nat) (xs : List Ax2303) : Four2303 :=
  let r := units xs.length
  let f := wideWorth2303 c.2.1 c.1 op r (r*(BitVec.allOnes 768).toNat) c.2.2.2.1
    (packedSig (fun e : Ax2303 => e.1.2) xs) (packedSig (fun e : Ax2303 => e.2.2) xs)
  (f false false,if op==2 then 0 else f true false,if op==2 then 0 else f false true,f true true)
def testMarks2303 (c : NodeContext) (op : Nat) (xs : List Ax2303) (ka kb : Bool) (m : Nat) :=
  if m==0 then true else onMarks (fun e => familyCheck2303 c op e ka kb) m xs
lemma todoAt2303 (c : NodeContext) {op} (xs : List Ax2303) (i : Nat) (hi : i<xs.length)
    (ka kb : Bool) (same : (op==2)=true → ka=kb) :
    (partFour2303 (todo2303 c op xs) ka kb).testBit (769*i)=
      worth2303 c.1 c.2.1 c.2.2.2.1 op xs[i].1 xs[i].2 (movedDecor op xs[i].1 xs[i].2) ka kb := by
  cases ka <;> cases kb <;> cases un : op==2 <;>
    first | exact False.elim (Bool.noConfusion (same un)) |
      simpa only [todo2303,partFour2303,un,Bool.false_eq_true,ite_false,ite_true] using
        (worthAt2303 c.2.1 c.1 op c.2.2.2.1 xs i hi _ _)
lemma familyBranch2303 {c : NodeContext} {op} (xs : List Ax2303)
    (pass : wideFamily2303 c (c.2.2.2.2.1.map (memo2303 c.2.2.1 (c.1-1))) op xs=true)
    (ka kb : Bool) :
    let done := runRules2303 xs op (todo2303 c op xs) (c.2.2.2.2.1.map (memo2303 c.2.2.1 (c.1-1)))
    testMarks2303 c op xs ka kb (partFour2303 done ka kb)=true := by
  obtain ⟨cap,n,ws,cov,ps,links⟩ := c
  simp only [wideFamily2303] at pass
  rw [opLanes2303] at pass
  let c : NodeContext := (cap,n,ws,cov,ps,links)
  let done := runRules2303 xs op (todo2303 c op xs) (ps.map (memo2303 ws (cap-1)))
  change (testMarks2303 c op xs false false done.1 && testMarks2303 c op xs true false done.2.1 &&
    testMarks2303 c op xs false true done.2.2.1 && testMarks2303 c op xs true true done.2.2.2)=true at pass
  simp only [Bool.and_eq_true] at pass
  cases ka <;> cases kb
  · exact pass.1.1.1
  · exact pass.1.2
  · exact pass.1.1.2
  · exact pass.2
def monoStep (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len>cap then true else
    let d:=true
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b) ||
        rectEnd (cap-1) (z :: opKeep un ka kb a b ws)
lemma evalDone2303 (c : NodeContext) (op : Nat) (a b : Decor) (ka kb : Bool)
    (ha : a∈c.2.2.1) (hb : b∈c.2.2.1)
    (checked : worth2303 c.1 c.2.1 c.2.2.2.1 op a b (movedDecor op a b) ka kb=true →
      familyCheck2303 c op (a,b) ka kb=true ∨ ∃ p∈c.2.2.2.2.1,
        scalarPoolCut p (c.1-1) ((opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst)
          (movedChoice op a b)=true) :
    monoStep c op a b (movedDecor op a b) ka kb=true := by
  obtain ⟨cap,n,ws,cov,ps,links⟩ := c
  let z := movedDecor op a b
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d := true
  let bits := restCov (getCov cov d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2
  let skip := !properB z.1 || ws.any (fun v => v.1==z.1)
  let st := (opKeep (op==2) ka kb a b ws).map Prod.fst
  change (if len>cap then true else if bits != BitVec.allOnes 768 then true else
    if skip then true else closeChild ps links (cap-1) st (movedChoice op a b) ||
      rectEnd (cap-1) (z :: opKeep (op==2) ka kb a b ws))=true
  by_cases long : len>cap
  · rw [if_pos long]
  rw [if_neg long]
  by_cases notfull : (bits != BitVec.allOnes 768)=true
  · rw [if_pos notfull]
  rw [if_neg notfull]
  by_cases short : skip=true
  · rw [if_pos short]
  rw [if_neg short]
  have w : worth2303 cap n cov op a b z ka kb=true := by
    change (if len>cap then false else bits==BitVec.allOnes 768)=true
    rw [if_neg long,beq_iff_eq]
    exact Classical.byContradiction (fun e => notfull (bne_iff_ne.mpr e))
  rcases checked w with link | cut
  · change (if skip then true else linked2303 ws links a b z.1 (op==2) ka kb ||
          rectEnd (cap-1) (z :: opKeep (op==2) ka kb a b ws))=true at link
    rw [if_neg short] at link
    simp only [Bool.or_eq_true] at link ⊢
    rcases link with l | term
    · left
      have mapped := linked_ok2303 ha hb l
      simp only [closeChild,Bool.or_eq_true]
      left
      simpa only [z,moved_full] using mapped
    · exact Or.inr term
  · rw [Bool.or_eq_true]; left
    simp only [closeChild,Bool.or_eq_true,List.any_eq_true]
    exact Or.inr cut
lemma wideFamily_pass2303 {c : NodeContext} {op : Nat} (xs : List Ax2303)
    (nd : (c.2.2.1.map Prod.fst).Nodup)
    (pass : wideFamily2303 c (c.2.2.2.2.1.map (memo2303 c.2.2.1 (c.1-1))) op xs=true)
    {e : Ax2303} (em : e∈xs) (ha : e.1∈c.2.2.1) (hb : e.2∈c.2.2.1)
    (ka kb : Bool) (same : (op==2)=true → ka=kb) :
    monoStep c op e.1 e.2 (movedDecor op e.1 e.2) ka kb=true := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp em
  subst e
  apply evalDone2303 _ _ _ _ _ _ ha hb
  intro w
  let before := todo2303 c op xs
  let ps := c.2.2.2.2.1
  let done := runRules2303 xs op before (ps.map (memo2303 c.2.2.1 (c.1-1)))
  let last := partFour2303 done ka kb
  have first : (partFour2303 before ka kb).testBit (769*i)=true := (todoAt2303 c xs i hi ka kb same).trans w
  cases h : last.testBit (769*i)
  · exact Or.inr (finishedRule2303 xs i hi ka kb before nd ha hb first h)
  · left
    have run := familyBranch2303 xs pass ka kb
    change testMarks2303 c op xs ka kb last=true at run
    have nz : last≠0 := by intro e; simp [e] at h
    simp only [testMarks2303,beq_eq_false_iff_ne.mpr nz,Bool.false_eq_true,ite_false] at run
    exact marked_ok _ _ _ i hi h run
def triangle2303 (f : Decor → Bits) : List Decor → Nat × Nat × Nat
  | [] => (0,0,0)
  | x::xs =>
    let (suffix,left,right) := triangle2303 f xs
    let m := xs.length
    let v := (f x).toNat
    ((suffix <<< 769)+v,(left <<< (769*m))+units m*v,(right <<< (769*m))+suffix)
lemma lanesAppend2303 {α} (f : α → Bits) (xs ys) :
    combineLanes f (xs++ys)=(combineLanes f ys <<< (769*xs.length))+combineLanes f xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons x l ih =>
    simp only [List.cons_append,List.length_cons,combineLanes,lanePlace,ih,Nat.shiftLeft_eq,
      Nat.mul_succ,Nat.pow_add]
    ring
lemma lanesMap2303 {α β : Type} (f : β → Bits) (g : α → β) (xs) :
    combineLanes f (xs.map g)=combineLanes (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,combineLanes,ih]
lemma triangle_eq2303 (f : Decor → Bits) (xs) :
    triangle2303 f xs=(combineLanes f xs,combineLanes (fun e : Ax2303 => f e.1) (couples2303 xs),
      combineLanes (fun e : Ax2303 => f e.2) (couples2303 xs)) := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    simp only [triangle2303,ih,combineLanes,couples2303,lanesAppend2303,lanesMap2303,
      List.length_map,←broadcast,lanePlace,Nat.shiftLeft_eq,Nat.mul_comm]
def packedFamily2303 (c : NodeContext) (ps : List Memo2303) (op : Nat) (ops : List Ax2303)
    (sa sb : PackedSig) (a b : Nat) :=
  let (cap,n,ws,cov,_,links) := c
  let r := units ops.length
  let full := r*(BitVec.allOnes 768).toNat
  let un := op==2
  let z := if un then (r*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b
  let worth := wideWorth2303 n cap op r full cov sa sb
  let todo : Four2303 := (worth false false,if un then 0 else worth true false,
                       if un then 0 else worth false true,worth true true)
  let left := wideRules2303 r full a b z un todo ps
  let verify := fun (ka kb : Bool) (t : Nat) => if t==0 then true else
    onMarks (fun e : Ax2303 =>
      let w := (movedDecor op e.1 e.2).1
      if !properB w || ws.any (fun v => v.1==w) then true else
      linked2303 ws links e.1 e.2 w un ka kb || rectEnd (cap-1) (movedDecor op e.1 e.2 :: opKeep un ka kb e.1 e.2 ws)) t ops
  verify false false left.1 && verify true false left.2.1 &&
    verify false true left.2.2.1 && verify true true left.2.2.2
def monoTriangle (c : NodeContext) :=
  let ws := c.2.2.1
  let ss := c.2.2.2.2.1.map (memo2303 ws (c.1-1))
  let bs := couples2303 ws
  let (_,pa,pb) := triangle2303 (fun w => w.2.1) ws
  let (_,na,nb) := triangle2303 (fun w => w.2.2) ws
  let (_,a,b) := triangle2303 (fun w => liftSig2303 w.1) ws
  let family := fun op => packedFamily2303 c ss op bs (pa,na) (pb,nb) a b
  family 0 && family 1
def plainContext (c : NodeContextT) : NodeContext :=
  (c.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2.1,c.2.2.2.2.2.2.2.1)
lemma passMonoStep {c : NodeContextT} (ht : c.2.1=0) (op : Nat) (a b : Decor) (ka kb : Bool)
    (h : monoStep (plainContext c) op a b (movedDecor op a b) ka kb=true) :
    evalMoveT c op a b (movedDecor op a b) ka kb=true := by
  obtain ⟨cap,tm,n,ws,cov,ps,fast,l0,l1,l2⟩ := c
  dsimp only at ht
  subst tm
  have zeroChild (len : Nat) : childT 0 cap len op=0 := by simp [childT]
  by_cases cheap : fast.any (fun qp => fastCost qp (cap-1) a b op ka kb)=true
  · simp only [evalMoveT,zeroChild,beq_self_eq_true,ite_true,cheap]
    repeat' split
    all_goals rfl
  · simp only [evalMoveT,zeroChild,beq_self_eq_true,ite_true,cheap,Bool.false_eq_true,ite_false,
      plainContext,monoStep] at h ⊢
    exact h
lemma passTriangle {c : NodeContextT} (ht : c.2.1=0)
    (nd : (c.2.2.2.1.map Prod.fst).Nodup) (h : monoTriangle (plainContext c)=true) :
    testAllT c c.2.2.2.1=true := by
  let p := plainContext c
  let ws := c.2.2.2.1
  let ps := p.2.2.2.2.1.map (memo2303 ws (p.1-1))
  have pair : wideFamily2303 p ps 0 (couples2303 ws)=true ∧ wideFamily2303 p ps 1 (couples2303 ws)=true := by
    simp only [monoTriangle,triangle_eq2303,Bool.and_eq_true] at h
    dsimp only [p,ps,ws,wideFamily2303,packedSig,plainContext]
    exact h
  have check {a b : Decor} (ha : a∈ws) (hb : b∈ws) (mem : (a,b)∈couples2303 ws)
      (d ka kb : Bool) : evalMoveT c (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true := by
    apply passMonoStep ht
    cases d
    · exact wideFamily_pass2303 _ nd pair.1 mem ha hb ka kb (by simp)
    · exact wideFamily_pass2303 _ nd pair.2 mem ha hb ka kb (by simp)
  have go (l : List Decor) (subset : l ⊆ ws) (seen : couples2303 l ⊆ couples2303 ws) : testAllT c l=true := by
    induction l with
    | nil => rfl
    | cons a bs ih =>
      have ha := subset List.mem_cons_self
      have sb : bs ⊆ ws := fun _ hm => subset (List.mem_cons_of_mem _ hm)
      have rest : couples2303 bs ⊆ couples2303 ws := fun _ hm => seen (List.mem_append_right _ hm)
      simp only [testAllT,testRowT,ht,beq_self_eq_true,ite_true,Bool.true_and,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
      refine ⟨?_,ih sb rest⟩
      intro b hb
      have present : (a,b)∈couples2303 ws := seen (List.mem_append_left _ (List.mem_map_of_mem hb))
      have step := check ha (sb hb) present
      have both (d : Bool) : testPairT c a b d=true := by
        simp only [testPairT,Bool.and_eq_true]
        exact ⟨⟨⟨step d false false,step d true false⟩,step d false true⟩,step d true true⟩
      exact ⟨both false,both true⟩
  exact go ws (fun _ m => m) (fun _ m => m)
def monoSpan (levels : Nat → PackingT) (i0 i1 i2 : Nat → Nat → Option (Nat × Nat))
    (k start n : Nat) : Bool :=
  (List.range' start n).all fun i =>
    let c := contextOfT levels i0 i1 i2 k 0 i
    prelimT (targetOf dead) c && monoTriangle (plainContext c)
theorem monoSpan_sound {levels i0 i1 i2 k start n} (h : monoSpan levels i0 i1 i2 k start n=true) :
    blockT levels i0 i1 i2 k 0 start n=true := by
  apply makeBlockT
  intro i lo hi
  rw [monoSpan,List.all_eq_true] at h
  have good := h i (List.mem_range'.mpr ⟨i-start,by omega,by simp only [Nat.one_mul]; omega⟩)
  simp only [Bool.and_eq_true] at good
  simp only [nodeVerifiedT,Bool.and_eq_true]
  refine ⟨good.1,?_⟩
  split
  · rfl
  · apply passTriangle rfl _ good.2
    have pre := good.1
    simp only [prelimT,Bool.and_eq_true,decide_eq_true_eq] at pre
    exact pre.1
def flipped (v : Fin 9) := neg (inputs.getD v.val zero)
def supplied (v : Fin 9) := inputs ++ [flipped v]

-- Each entry records its live wires and the restrictions used to rule out their possible successors.
def layer14 : PackingT := (3,1,8,8,(fun i => 0x4200703034170280824401c0a0400028040104889e4f00ffe44ffe007fe00))
def links14 := lookupWord 16 62 4 13 5 4 (fun i => 0x380540d00a889c02a015100904402ae12d18190402bce121630a3c1c260090182040a60990350c584161470868b402b62111748be00660c007984c02a00b715d88c884ce000a805402a6a000aa02a4c3e26c03da8402a404112680002a01500a9a0804a015172040013d360003)
def layer13 : PackingT := (21,2,8,12,(fun i => 0x280681400c1081e060360b4410d82460061583002c082407e8821b048a00c0f819100ac344343142d0f8245807080601581b05e0218a1b048a4142800e068140b145104043142e09188283401c0f068161406e80a2087a17048d0a01a00e078183413d104050d42e091801c0f03068278168821e2609409100a003842060142d82c32c050d0c6091c018400c00b80c162407e8289c29104142800e1081a050380b0c50b106091a01c0c1a02c020901f86226094401a00e1081c2d82c280c30143609180183e1580b05e021fa1a14094410500e1081c3101a0d02c28c090b82468070386802604178821f850260a4402806803842078180513d0d42c3f8246806158301a00820a1a2608040070140481e05810060a20280409180800e030090840f034090081a048b040070180581e068140b026021305c9c466c2c3f6bb7372b33302ab9283a3f20e9cf19e95a1248e00b487503a8007ff4a200ffe14401ffd67803ffa4f007ff55a00ffe9b401ffd26803ffa2d007ff49600ffe12c01ffd15803ff82b007ff48e00ffe11c01ffd13803ff827007ff44a00ffe094017fd03802ffa05005ff40600))
def links13 := lookupWord 54 206 6 15 7 4 (fun i => 0x800c0827065634003618386180c14f1c1183c00d96305c27484f309a8050036205400d980dfdd5a812801b011d41c9a244167e393c05c00f008582a8036203d500f20d682858ab4106c4834082a03503d22d545ee101e019004f81f002c00d801b00360056f04601b3c02901600d9617c00728ca206c01b00362828709483a1822c863c0d14179024d0096010c2d8036122800d8927f435583a270680b602343a0104ba16d80c9815e04801b3c263923608001b30717b0300d801b2421e82161bb8174036701f6004c081c24006c902f20af80d2059b0524194c17400a704ea15580002a600d8467cc66502f80824499467806c41b601b00360b02e04d40ef41a006c506201b3073f102f190a180c03006c203b0401819806c00d9a16803648e100d801b00364066a0c58088036706b00d801b0036740200d801b002c020000d982c643380e3a19c20c300df861c09781a506ba32b8054d282808c0e07009c31e022591e00d88063c73083f6244a36203278035038415c829785100d801b0036685c0000c040018a00b00c00a3221ce7802800001820c01c52010020091a63d46403440030c00c9003000)
def layer12 : PackingT := (108,3,8,14,(fun i => (if i<1 then 0x4b41213c1813e0282415840300d01704807e41427070401230583f20a0a027070300541a04605c0c4222091004f8084708080c268603e0af05f0107e434140703e0af05f0107e43414070560d01703f21a0a0301f05782f8083f21a0a0381f05782f8083f21a0a0381f0560bb8083f21a0a0381f05782f8083f21a0a03830069c082182b05a101048808082427830560601a04121a130302b0300d02090d09818158180681048684c0c0ac0c03408243426060560d02082821a130302b0300d02090d09818158180681048684c0c0b003004c0f81b0221081b0244805c2181f00e0b81a828383500184015e07c0a81b0140b812281660703f8181fc0b812834260900981f0303fc008360587ac96adca99e9fda64e934a32a8609f8274a9b8267697ae56093ae497905e3ad8cb62b889661fa866e110829a0528025f7e7c51e89787ddcb7585ce171b1c026e61b186ab9a4467959a7647188660457865bed6a758f55de55a550a52ad42b4e8132b4a81236473116d43e10994114fe63df0edb396cde63674d07321cbf12e48b542af8a3326a092823248a1218c83b20207b41d807011ae066418405c715cc51f132c47710603f00e9c35e0c542cc0a0c23a07c418704cc0be0150000fff4a1158037fc9a4a200bff4e828802ffd1a0a200fbf5a156803efd6755a00bff5e936803efd684da00bff62926802ffd7a49a00ffb4a126803efd6749a00fbf55926803efd3649a00bff5e916803efd2645a00bff5e925803dfc7a49600bff5a925803fed2849600fdf55d25803fed2749600bff62825802ffd6a09600bff4e825802ffd1a09600dff26915802ffd6a45600fdf55915803f7d2545600bff4e815802ffd2a05600bff62923802ffd7a48e00bff5a923803fed2848e00ff74dd23802ffd8a08e00bff5a823802ffd5a08e00bff468238037fc9a44e00bff62913802ffd7a44e00bff5a913802ffd5a44e00ffd46113803fdd3644e00ff748d13802ffd8a04e00bff5e813802ffd5a04e00bff4a813802ffd8a44a00bff5e912802ffd6a44a00bff56912802ffd3a44a00ffd45d12803fed2644a00ffd44d12802ffd8a04a00bff56812802ffd3a04a00dff469038037fd2540e00dff629028037fd3a40a00dff469028037fd1840a00dff4d5028037fd1340a00dff4e9018037fd2a40600dff4e1018037fd3540600dff495018037fd23406009ff269288027fc9a55a009ff269368027fc9a49a009ff26925802efd6a09600bef528258027fc9a456009ff26923802bfd8a08e00b7f5e823802efd6a08e00bdf56823802fbd4a08e00bfd46823802ff90a08e009ff269138027fc9a44a00aff62812802dfd7a04a00bbf5a812802f7d5a04a00bef52812802fdd3a04a00bfe428128027fd8a40a00dfe40d028027fd3a406009ff4a9018037f90240600 else (if i<2 then 0x4405303e060960c427d0d220217048b04c0881802b0820d08686d09e1fc87875c123425e07c0c13e87885221824420906043c2886d09e1ff0490d1082483e0622042c8288507143427a31c122106105c0e4411410b0500dc27885a1b824420c044087030480a21b4279330c01305607c0c0d02794f0da13038260440e41802d06582c3e90d0dc1385839061c07058240e64343704e1209811014c0c0e28681c09e23842e091642015e06c0841e0d05111d824460ac200c3058320ea4343704e100e70304506413c3a88e09c200c60410c0e04290509013840220300d03104807e0b89a1056024b8270c08e12016e0b10c0608287409c24100406160b84283f09c1c2d8444121183b8410c098116060880b8058450d014433071098330304405c02c3f8510cc1c4260920b8430302b40b0108204f0c41d447609188181a04807e2182007406213048400681200b03f0621303831c1d82e1402d08ec4286e091384015f0109182c8682d0601ec3ae09160980a6076160dc1884fa1a217048a2100a30760b85011f81310c12270802be0382c1807b21a1d7048903606815e04e0221c1f83710c434140b04c0ac1a0416020b84290d050240ff0109582c1583f0dc434140903e0ac3ab0b05c4341403f101b02c0434121002821c0f01a14031c1b4100d8366201ff048c0378401820d6050a08284805613c3f875c123413021c0e0c50804f0861b43404c1409b0820708a06e0360d8161043f88ec12308403642181e03028c1b0a01bb100ff824660742013c218850fe1303905c2181c8204f0801d03fe09121241882f07e0d01408609820130460680fc2091d05e0a03004c1481c1a05f05e1c414041098230383425e0bc3a82807e1304022c0f8181a031a0806c27b100ff8245822037840180480564341d04f0ea53f048c04c08b03e060680c42794f0da1305022c2181815c05094070278620ea23b048cc2181c2504f0621003a07fc1227080300564ac2783a29e4370489c0f8181a12e09e1fc4284c1181d0303f051842068400e81ff048a0440ac0c0410682148684c100601a05b056434260410e098158340b80602090d098201a82c40a15204e020e482c150903e0880a0208088ac15c28c0881e0360141b024702c40d81f0303fc0814e04a1081a1e45a1005981c1fe04c038410540d0f22829a0b8130343c83f0c0a00d40780d8181fa3406881204c0d4201dc6a108080fc24e10c0881d0360181b0245a1003501c1a6070800fc29c0341682a068771a8402e03f08380903068098203a04141a0fc260507e06824a1f02811f02c048078090820a898341a03f80b8400a049c0b00e05a0a41d13060340500800c60607e0ad03a0d8170243a8c06811c15e070820610340941b02c3a0b0300ac1a50d09e12c23a091142d048510605687d0b40614028 else 0x4510a201e060690102084a08b01c3a85209e21447609200543804b11682423860560602401410c1003a11021b82450030561000b048c124348803f1381b02e040b61448808fc122104e0621613c3a8510d64d027080601201f82b06821487875c122703e04e058341b8872202170489))))
def links12 := lookupWord 28 107 6 15 7 4 (fun i => 0x1e07840df833030240d0901003c00820104020d8be6019a0a3c814a09e50a8072054804100828044c82e8277062281101320388064c07c81dd818c67d40ba816804120752054020c840c04900f944abd0a70116026c12804100820104020c82a9073802f043700aa0016036c01103f6003c074020c817904060f70178041f02c010701b0041b006e0c301ac007b10a010440738296057282a011b02cc1500107c02a01a0082010781b8041501f804011f000400820104020e0219027404900a6022700dac0d1c4101914600004430008490008a0010000c01822040cb080)
def layer11 : PackingT := (65,4,8,13,(fun i => (if i<1 then 0x120fc0ee240ac0c00d006c1882398241d4400a8098348418333048200704904501308204203f0d05e02781202a0ec08607e1e80c12c1f81e411c280a809e86844041d048238701501304308b031083a0907e0771205608f4121141180f2180601100f68241442820029d048288405204405104c080c40880a20981006743c0ec0be80c1a4140380a82350182d02f0280601506906306803704304c0e0d20c40a01000981415412e82413c202482a02dd048278504803d06da0904f0a0960cc0db41209e1412c15c1b682413c280f045021d048328158601b061034a0908902b0c0260dc06e0794120c80561e0441b81068240ac1dc230380a81a01803f83782250484603b8901301801506e03a03f051a0908008c1403c10606010541208e1806c0d01ba80c198134300982e83301850482006811040a0308306604d0c02a03c0d00a20814121040ee2004c0641b810c1fc1441028242301dc500980a84183550482006049055a0904f080400800b741209e1420c13e824100200b81f50560684683c86607e00089c0d0790b051c21414c1c0f80f2180ff03780182c2341e43503006012701605e0484103b88037025c09c0ba0d07a0c04e05941b81381611a0f21c05702d82a8342341e4370003ae05b0703c83e06e06056a05e01e0004160e07711a1a0960500e949461a0f4f3e6e933195f49be4711dd8b543de1210357db3e2de30eb172b381db58d69687326d898c095e92e6d6c8b0955d297d4389e54d1257d2388d944520ecfc07853891a4cc885f52d3155c9e04712110fac7503711910b7c5202410ed062c2600e104900ac001dff4612540e00effa309aa050067fd1362902802bdea5934944011ff26d7a4da008ff936c524d0047fc9b5a9258023fe4dad48ac011ff26d3a056008ff936c52470047fc9b5a9238023fe4db1489c011ff26d7a44e008ff936b52270047fc9b569138023fe4dab409c011ff26d8a44a008ff936ad2250047fc9b4e9128023fe55a6a814011ff2ad1340a00cf7a964d2510047fd3b269288023fe8d934944019fb4949a4a2008ffa764d2ad0047fd2b269568023fe8d934ab4019df4549a55a008ffab64d26d0047fd2b269368023fe8d9349b4019f744c9a4da008ffb164d24d0047fd5b269268023fe9d934934019bf5589a49a00cdfa6c4d24d0047fd8b269258023fe9d93492c011ff46c9a49600cefa2a4d24b0047fd3b269158023fe959348ac011ff62c9a48e008ffab64d2470047fd1b269238033ee8993491c011ff62c9a44e008ffab64d2270047fd2b269138023fec5934894011ff56c9a44a008ffa764d2250067f98a40d02803bec9aa0681401dfa4950340a00efb22681a050047fd8b4e9018023fec5a5480c011ff4ed2a40600cff274812030077e92540901803bf88aa0480c011ef52c9a4a200 else 0x456850c03051405800198048d01490d01542820811e01d0803e0504b21208aa0308b0470c06805610121e104c120ea1c0541bd8241f812c280a80f04501802c80a042b0483c090151340670686090440c09321609c0801005404c20c1a58241e411c380a83683481a01884430484083c8901501306802e03108360907e077120260cc074096034100c120ea200541b41a418c1a182410c380a80183701a03f827820b0484603b8a04604904c0602a026086116062106c)))
def links11 := lookupWord 1 5 0 10 2 4 (fun i => 0x14c00bc000b81)
def layer10 : PackingT := (2,5,8,8,(fun i => 0x225055e0030702300f2180c7029f00780811c07c03b876200f749354950340a00f761254550240600))
def allLayers : Nat → PackingT
  | 42 => layer14
  | 39 => layer13
  | 36 => layer12
  | 33 => layer11
  | 30 => layer10
  | _ => emptyPackingT

def allLinks : Nat → Nat → Option (Nat × Nat)
  | 42 => links14
  | 39 => links13
  | 36 => links12
  | 33 => links11
  | _ => fun _ => none

def noLinks (_ _ : Nat) : Option (Nat × Nat) := none
def slab := blockT allLayers allLinks noLinks noLinks
theorem verifySpan (k start n : Nat) (checked : monoSpan allLayers allLinks noLinks noLinks k start n=true) : slab k 0 start n=true := monoSpan_sound checked
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part10_0 : slab 10 0 0 2=true := verifySpan 10 0 2 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem layerOK10 : slab 10 0 0 2=true := part10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part11_0 : slab 11 0 0 16=true := verifySpan 11 0 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part11_16 : slab 11 0 16 16=true := verifySpan 11 16 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part11_32 : slab 11 0 32 16=true := verifySpan 11 32 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part11_48 : slab 11 0 48 16=true := verifySpan 11 48 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part11_64 : slab 11 0 64 1=true := verifySpan 11 64 1 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem layerOK11 : slab 11 0 0 65=true := (blockT_merge (start:=0) (a:=32) (b:=33) (blockT_merge (start:=0) (a:=16) (b:=16) part11_0 part11_16) (blockT_merge (start:=32) (a:=16) (b:=17) part11_32 (blockT_merge (start:=48) (a:=16) (b:=1) part11_48 part11_64)))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_0 : slab 12 0 0 16=true := verifySpan 12 0 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_16 : slab 12 0 16 16=true := verifySpan 12 16 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_32 : slab 12 0 32 16=true := verifySpan 12 32 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_48 : slab 12 0 48 16=true := verifySpan 12 48 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_64 : slab 12 0 64 16=true := verifySpan 12 64 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_80 : slab 12 0 80 16=true := verifySpan 12 80 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part12_96 : slab 12 0 96 12=true := verifySpan 12 96 12 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem layerOK12 : slab 12 0 0 108=true := (blockT_merge (start:=0) (a:=48) (b:=60) (blockT_merge (start:=0) (a:=16) (b:=32) part12_0 (blockT_merge (start:=16) (a:=16) (b:=16) part12_16 part12_32)) (blockT_merge (start:=48) (a:=32) (b:=28) (blockT_merge (start:=48) (a:=16) (b:=16) part12_48 part12_64) (blockT_merge (start:=80) (a:=16) (b:=12) part12_80 part12_96)))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part13_0 : slab 13 0 0 16=true := verifySpan 13 0 16 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part13_16 : slab 13 0 16 5=true := verifySpan 13 16 5 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem layerOK13 : slab 13 0 0 21=true := (blockT_merge (start:=0) (a:=16) (b:=5) part13_0 part13_16)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part14_0 : slab 14 0 0 3=true := verifySpan 14 0 3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem layerOK14 : slab 14 0 0 3=true := part14_0
theorem checkedLayers : ∀ k ≤ 14, ∀ t ≤ 2, slab k t 0 (allLayers (3*k+t)).1=true := by
  intro k hk t ht
  interval_cases k <;> interval_cases t
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact layerOK10
  · rfl
  · rfl
  · exact layerOK11
  · rfl
  · rfl
  · exact layerOK12
  · rfl
  · rfl
  · exact layerOK13
  · rfl
  · rfl
  · exact layerOK14
  · rfl
  · rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem monoPlain : ImpossibleT graph 14 0 inputs.toFinset := by
  have h := forestT_all allLayers allLinks noLinks noLinks 14 _ (before_sound known383 valid383) geomdead checkedLayers 14 (by decide) 0 (by decide) 0 (by decide +kernel)
  have eq : (stateSetT allLayers 42 0).toFinset = inputs.toFinset := by decide +kernel
  exact eq ▸ h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem monoZero : ImpossibleT graph 14 0 (supplied 0).toFinset := by
  have h := forestT_all allLayers allLinks noLinks noLinks 14 _ (before_sound known383 valid383) geomdead checkedLayers 14 (by decide) 0 (by decide) 1 (by decide +kernel)
  have eq : (stateSetT allLayers 42 1).toFinset = (supplied 0).toFinset := by decide +kernel
  exact eq ▸ h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem monoFour : ImpossibleT graph 14 0 (supplied 4).toFinset := by
  have h := forestT_all allLayers allLinks noLinks noLinks 14 _ (before_sound known383 valid383) geomdead checkedLayers 14 (by decide) 0 (by decide) 2 (by decide +kernel)
  have eq : (stateSetT allLayers 42 2).toFinset = (supplied 4).toFinset := by decide +kernel
  exact eq ▸ h
open PEqualNP.CircuitLowerBounds
theorem edge_eq_petersen (x : Fin 9→Bool) : edge x=Binary.petersenF x:=by
  simp [edge,Binary.petersenF,Binary.PetersenNine.edgeFun,Binary.PetersenNine.edges,Bool.or_assoc]
set_option maxRecDepth 8192 in
theorem increasingWitness : ∀ v i : Fin 9,
    (bit (presentRow i) graph && !bit (absentRow i) graph) &&
    (supplied v).all (fun w => w == inputs.getD i.val zero ||
      !(bit (presentRow i) w && !bit (absentRow i) w)) = true := by decide +kernel

theorem unsignedLive {v k S} (h : Live graph k 0 S) (sub : ∀ a ∈ S, a ∈ supplied v) :
    S = inputs.toFinset ∨ S = (supplied v).toFinset := by
  have needed : inputs.toFinset ⊆ S := by
    intro a ha
    have mem := List.mem_toFinset.mp ha
    rw [←input_list,List.mem_ofFn] at mem
    obtain ⟨i,rfl⟩ := mem
    have w := increasingWitness v i
    simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at w
    obtain ⟨a,ha,hi,lo⟩ := mono_row_difference h rfl w.1.1 w.1.2
    have same := of_decide_eq_true w.2 a (sub a ha)
    have eq : a = inputs.getD i.val zero := by simpa [hi,lo] using same
    exact eq ▸ ha
  by_cases hs : flipped v ∈ S
  · right
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      rcases List.mem_append.mp (List.mem_toFinset.mp ha) with old | last
      · exact needed (List.mem_toFinset.mpr old)
      · exact List.mem_singleton.mp last ▸ hs
  · left
    refine Finset.Subset.antisymm ?_ needed
    intro a ha
    rcases List.mem_append.mp (sub a ha) with old | last
    · exact List.mem_toFinset.mpr old
    · exact False.elim (hs (List.mem_singleton.mp last ▸ ha))

theorem headNot (g : Gate) (v : Fin 9)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (e : gv inputs g = flipped v) : g.op = .not := by
  have getZero (j : Nat) : bit 0 (inputs.getD j zero) = false := by
    by_cases hj : j < 9
    · interval_cases j <;> decide +kernel
    · have le : inputs.length ≤ j := by rw [←input_list,List.length_ofFn]; omega
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none le]
      exact bit_zero _
  have up : bit 0 (gv inputs g) = true := by rw [e,flipped,bit_neg,getZero]; rfl
  have notOne : flipped v ≠ one := by
    have h : ∀ i : Fin 9, flipped i ≠ one := by decide +kernel
    exact h v
  rcases legal with op | op | op
  · cases eq : g.inputs with
    | nil => exact False.elim (notOne (e ▸ (by simp [gv,op,eq] : gv inputs g=one)))
    | cons i l =>
      have z : bit 0 (gv inputs g) = false := by
        rw [show gv inputs g = bin false (inputs.getD i zero)
            ((l.map (fun t => inputs.getD t zero)).foldr (bin false) one) by simp [gv,op,eq]]
        rw [bit_bin,getZero]; rfl
      simp [z] at up
  · have allZero (l : List Nat) :
        bit 0 ((l.map (fun t => inputs.getD t zero)).foldr (bin true) zero) = false := by
      induction l with
      | nil => exact bit_zero _
      | cons a l ih =>
        rw [List.map_cons,List.foldr_cons,bit_bin,getZero,ih]
        rfl
    have z : bit 0 (gv inputs g) = false := by simpa only [gv,op] using allZero g.inputs
    simp [z] at up
  · exact op

theorem finishGap (v : Fin 9) (hv : v = 0 ∨ v = 4) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !y v)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) : False := by
  have headEq : (execute C.gates inputs).getD 9 zero = flipped v := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (bit_neg r _).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right fun hn => hn graph_proper
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    have nonzero : ∀ i : Fin 9, flipped i ≠ zero := by decide +kernel
    exact nonzero v headEq.symm
  | cons g gs =>
    have eq0 : gv inputs g = flipped v := by
      rw [hgs] at headEq
      change (execute gs (inputs ++ [gv inputs g])).getD 9 zero = _ at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs ++ [gv inputs g])
      rw [hl] at headEq
      exact headEq
    have legalG := legal g (hgs ▸ List.mem_cons_self)
    have op := headNot g v legalG.1 eq0
    have low : 14 ≤ Binary.CircuitProof.nonNotCount C.gates := by
      by_contra! h
      apply Binary.petersen_binary_bound C legal _ (by omega)
      intro x
      exact (congrFun computes x).trans (edge_eq_petersen x)
    have count := Binary.nonNotCount_add_notCount gs
    have consCount : Binary.CircuitProof.nonNotCount (g :: gs) = Binary.CircuitProof.nonNotCount gs := by
      simp only [Binary.CircuitProof.nonNotCount,List.countP_cons,op]
      rfl
    rw [hgs,consCount] at low
    have len : gs.length + 1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    have same : (fun g : Gate => isNotT g.op) = (fun g : Gate => Binary.CircuitProof.isNotGate g.op) := by
      funext g; cases g.op <;> rfl
    have no : gs.countP (fun g => isNotT g.op) = 0 := by
      rw [same,List.countP_eq_length_filter]
      omega
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs ++ [gv inputs g]) at targetIn
    rw [eq0] at targetIn
    obtain ⟨k,t,S,hk,ht,run,sub⟩ := extractT gs (supplied v)
      (fun a ha => legal a (hgs ▸ List.mem_cons_of_mem _ ha)) graph_proper targetIn
    have tz : t=0 := by omega
    subst t
    rcases unsignedLive run sub with u | b
    · exact monoPlain k 0 (by omega) (by decide) (u ▸ run)
    · rcases hv with rfl | rfl
      · exact monoZero k 0 (by omega) (by decide) (b ▸ run)
      · exact monoFour k 0 (by omega) (by decide) (b ▸ run)

-- The signed bound uses the certificate of L-meta-2442.
namespace Transfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

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


def permute (p : Fin 9 → Fin 9) (i : Fin 11) : Fin 11 :=
  if h : i.val < 9 then (p ⟨i.val,h⟩).castLE (by decide)
  else if i.val = 9 then 10 else 9

def negGate (v : Fin 9) : Gate := ⟨.not,[v.val]⟩
def orGate (p : Fin 9 → Fin 9) : Gate := ⟨.or,[(p 0).val,(p 2).val]⟩

def enlarged (p : Fin 9 → Fin 9) (v : Fin 9) (C : Circuit) : Circuit :=
  ⟨negGate (p v) :: orGate p :: C.gates.map (relGate 11 11 (permute p)),
    wmap 11 11 (permute p) C.output⟩

theorem legalEnlarged (p : Fin 9 → Fin 9) (v : Fin 9) (C : Circuit)
    (h : FanInTwo C) : FanInTwo (enlarged p v C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨by simp [negGate],by simp [negGate]⟩
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨by simp [orGate],by simp [orGate]⟩
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact ⟨(h a ha).1,by simpa [relGate] using (h a ha).2⟩

theorem readBase {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,i.isLt]

theorem negStep (x : Fin 9 → Bool) (v : Fin 9) :
    step (List.ofFn x) (negGate v) = List.ofFn x ++ [!(x v)] := by
  change _ ++ [!((List.ofFn x).getD v.val false)] = _
  rw [readBase]

theorem orStep (x : Fin 9 → Bool) (p : Fin 9 → Fin 9) (v : Fin 9) :
    step (List.ofFn x ++ [!x (p v)]) (orGate p) =
      (List.ofFn x ++ [!x (p v)]) ++ [x (p 0) || x (p 2)] := by
  have read (i : Fin 9) : (List.ofFn x ++ [!x (p v)]).getD i.val false = x i := by
    rw [List.getD_append _ _ _ _ (by simp)]
    exact readBase x i
  simp only [step,orGate,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,read]

theorem firstWire (x : Fin 9 → Bool) (p : Fin 9 → Fin 9) (v : Fin 9) (C : Circuit) :
    ((enlarged p v C).wires (List.ofFn x)).getD 9 false = !x (p v) := by
  change (Binary.CircuitProof.wiresFrom (orGate p :: _) (step (List.ofFn x) (negGate (p v)))).getD 9 false = _
  rw [negStep,Binary.CircuitProof.getD_wiresFrom _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

def given (x : Fin 9 → Bool) (v : Fin 9) := List.ofFn x ++ [x 0 || x 2,!x v]

theorem starting (x : Fin 9 → Bool) (p : Fin 9 → Fin 9) (v : Fin 9) :
    Rel 11 11 (permute p) (given (x ∘ p) v)
      ((List.ofFn x ++ [!x (p v)]) ++ [x (p 0) || x (p 2)]) := by
  refine ⟨by simp [given],by simp [given],?_⟩
  intro i
  by_cases h : i < 9
  · let j : Fin 9 := ⟨i,h⟩
    have h11 : i < 11 := by omega
    have e : wmap 11 11 (permute p) i = (p j).val := by simp [wmap,permute,h,h11,j]
    rw [e]
    rw [List.getD_append _ _ _ _ (by simp; have := (p j).isLt; omega),
        List.getD_append _ _ _ _ (by simp)]
    unfold given
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    exact (readBase x (p j)).trans (readBase (x ∘ p) j).symm
  · by_cases h11 : i < 11
    · have : i = 9 ∨ i = 10 := by omega
      rcases this with rfl | rfl <;>
        simp [wmap,permute,given,List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ (by simp [wmap,h11]),
          List.getD_eq_default _ _ (by simp [given]; omega)]

theorem evaluation (x : Fin 9 → Bool) (p : Fin 9 → Fin 9) (v : Fin 9) (C : Circuit) :
    (enlarged p v C).eval (List.ofFn x) = C.eval (given (x ∘ p) v) := by
  change ((C.gates.map (relGate 11 11 (permute p))).foldl step
    (step (step (List.ofFn x) (negGate (p v))) (orGate p))).getD _ false = _
  rw [negStep,orStep]
  exact (rel_fold _ _ _ C.gates _ _ (starting x p v)).2.2 C.output

def reflection : Fin 9 → Fin 9 := ![3,2,1,0,4,8,7,6,5]

theorem reflectionEdge : ∀ x : Fin 9 → Bool, edge (x ∘ reflection) = edge x := by
  decide +kernel

def SignedBound := ∀ (v : Fin 9), v = 0 ∨ v = 4 → ∀ C : Circuit, FanInTwo C →
  (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x v) →
  circuitFun 9 C = edge → C.size ≤ 15 → False

theorem exclude (bound : SignedBound) (p : Fin 9 → Fin 9) (v : Fin 9)
    (hv : p v = 0 ∨ p v = 4) (symm : ∀ x, edge (x ∘ p) = edge x)
    (C : Circuit) (legal : FanInTwo C) (small : C.size ≤ 13) :
    ∃ x, C.eval (given x v) ≠ edge x := by
  by_contra! good
  apply bound (p v) hv (enlarged p v C) (legalEnlarged p v C legal)
    (fun x => firstWire x p v C)
  · funext x
    exact (evaluation x p v C).trans ((good _).trans (symm x))
  · change C.gates.length ≤ 13 at small
    simp [enlarged,Circuit.size]
    omega

end Transfer

end PEqualNP.Outside.L_meta_3885
open PEqualNP.Outside.L_meta_3885
theorem PEqualNP.Outside.L_meta_3885 : ∀ (x1 : Fin (11 : ℕ)),   x1 = (0 : Fin (11 : ℕ)) ∨ x1 = (3 : Fin (11 : ℕ)) ∨ x1 = (4 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [!x7.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2 := by
  intro i hi C legal small
  have bound : Transfer.SignedBound := finishGap
  have take (v : Fin 9) (h : ∃ x, C.eval (Transfer.given x v) ≠ edge x)
      (eqv : i.val = v.val) :
      ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 2]) ++
        [!(List.ofFn x ++ [x 0 || x 2]).getD i.val false]) ≠ edge x := by
    obtain ⟨x,hx⟩ := h
    refine ⟨x,?_⟩
    have ev : (List.ofFn x ++ [x 0 || x 2]).getD i.val false = x v := by
      rw [eqv,List.getD_append _ _ _ _ (by simp)]
      exact Transfer.readBase x v
    simpa only [ev,List.append_assoc,List.cons_append,List.nil_append,Transfer.given] using hx
  have fail : ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 0 || x 2]) ++
        [!(List.ofFn x ++ [x 0 || x 2]).getD i.val false]) ≠ edge x := by
    rcases hi with rfl | rfl | rfl
    · exact take 0 (Transfer.exclude bound id 0 (Or.inl rfl) (fun _ => rfl) C legal small) rfl
    · exact take 3 (Transfer.exclude bound Transfer.reflection 3 (Or.inl rfl)
        Transfer.reflectionEdge C legal small) rfl
    · exact take 4 (Transfer.exclude bound id 4 (Or.inr rfl) (fun _ => rfl) C legal small) rfl
  obtain ⟨x,hx⟩ := fail
  exact ⟨x,by simpa only [List.any_cons,List.any_nil,Bool.or_false,edge,Bool.or_assoc] using hx⟩
