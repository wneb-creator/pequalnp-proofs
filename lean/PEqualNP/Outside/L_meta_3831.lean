import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3831

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
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
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
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
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
      simp [simpAnd] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; rfl
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
    simp [opCount, he]

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
    exact PEqualNP.Outside.L_meta_3831.least_gate_inputs_nodup least nonnull _
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

abbrev petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
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
  let _ : DecidableRel petersenGraph.Adj := petersenAdjDecidable
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
    cases isNotGate g.op <;> simp <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenNine

def cube (i j k : Vertex) (m u : Nat) (b : Bool) (v : Vertex) : Bool :=
  if v = k then b else if v = i then u.testBit 0 else if v = j then u.testBit 1 else m.testBit v.val

def witnessAt (idx : Nat) : Nat :=
  (bif Nat.blt idx 364 then (bif Nat.blt idx 182 then (bif Nat.blt idx 91 then (bif Nat.blt idx 45 then (bif Nat.blt idx 22 then (bif Nat.blt idx 11 then 0 else (bif Nat.blt idx 16 then (bif Nat.blt idx 13 then (bif Nat.blt idx 12 then 57 else 0) else (bif Nat.blt idx 14 then 53 else (bif Nat.blt idx 15 then 53 else 57))) else (bif Nat.blt idx 19 then 0 else (bif Nat.blt idx 20 then 549 else (bif Nat.blt idx 21 then 0 else 2085))))) else (bif Nat.blt idx 33 then (bif Nat.blt idx 27 then (bif Nat.blt idx 24 then (bif Nat.blt idx 23 then 8229 else 549) else (bif Nat.blt idx 25 then 0 else (bif Nat.blt idx 26 then 1061 else 0))) else (bif Nat.blt idx 30 then (bif Nat.blt idx 28 then 0 else (bif Nat.blt idx 29 then 16421 else 2085)) else (bif Nat.blt idx 31 then 0 else (bif Nat.blt idx 32 then 165 else 293)))) else (bif Nat.blt idx 39 then (bif Nat.blt idx 36 then (bif Nat.blt idx 34 then 0 else (bif Nat.blt idx 35 then 0 else 165)) else (bif Nat.blt idx 37 then 0 else (bif Nat.blt idx 38 then 53 else 0))) else (bif Nat.blt idx 42 then (bif Nat.blt idx 40 then 57 else (bif Nat.blt idx 41 then 0 else 53)) else 0)))) else (bif Nat.blt idx 68 then (bif Nat.blt idx 56 then (bif Nat.blt idx 50 then (bif Nat.blt idx 47 then (bif Nat.blt idx 46 then 0 else 53) else (bif Nat.blt idx 48 then 0 else (bif Nat.blt idx 49 then 0 else 53))) else (bif Nat.blt idx 53 then (bif Nat.blt idx 51 then 0 else (bif Nat.blt idx 52 then 0 else 57)) else (bif Nat.blt idx 54 then 57 else (bif Nat.blt idx 55 then 0 else 1061)))) else (bif Nat.blt idx 62 then (bif Nat.blt idx 59 then (bif Nat.blt idx 57 then 0 else (bif Nat.blt idx 58 then 0 else 16421)) else 0) else (bif Nat.blt idx 65 then (bif Nat.blt idx 63 then 1061 else 0) else (bif Nat.blt idx 66 then 1061 else (bif Nat.blt idx 67 then 0 else 293))))) else (bif Nat.blt idx 79 then (bif Nat.blt idx 73 then (bif Nat.blt idx 70 then (bif Nat.blt idx 69 then 165 else 0) else 0) else (bif Nat.blt idx 76 then (bif Nat.blt idx 74 then 549 else (bif Nat.blt idx 75 then 0 else 165)) else (bif Nat.blt idx 77 then 4133 else (bif Nat.blt idx 78 then 165 else 1061)))) else (bif Nat.blt idx 85 then (bif Nat.blt idx 82 then 0 else (bif Nat.blt idx 83 then 0 else (bif Nat.blt idx 84 then 53 else 0))) else (bif Nat.blt idx 88 then (bif Nat.blt idx 86 then 57 else (bif Nat.blt idx 87 then 57 else 53)) else 0))))) else (bif Nat.blt idx 136 then (bif Nat.blt idx 113 then (bif Nat.blt idx 102 then (bif Nat.blt idx 96 then 0 else (bif Nat.blt idx 99 then 0 else (bif Nat.blt idx 100 then 53 else 0))) else (bif Nat.blt idx 107 then (bif Nat.blt idx 104 then (bif Nat.blt idx 103 then 57 else 0) else (bif Nat.blt idx 105 then 0 else (bif Nat.blt idx 106 then 53 else 57))) else (bif Nat.blt idx 110 then (bif Nat.blt idx 108 then 0 else (bif Nat.blt idx 109 then 16421 else 0)) else (bif Nat.blt idx 111 then 101 else (bif Nat.blt idx 112 then 0 else 4133))))) else (bif Nat.blt idx 124 then (bif Nat.blt idx 118 then (bif Nat.blt idx 115 then (bif Nat.blt idx 114 then 0 else 1061) else (bif Nat.blt idx 116 then 0 else (bif Nat.blt idx 117 then 101 else 293))) else (bif Nat.blt idx 121 then (bif Nat.blt idx 119 then 0 else (bif Nat.blt idx 120 then 0 else 4133)) else (bif Nat.blt idx 122 then 0 else (bif Nat.blt idx 123 then 0 else 549)))) else (bif Nat.blt idx 130 then (bif Nat.blt idx 127 then (bif Nat.blt idx 125 then 0 else (bif Nat.blt idx 126 then 0 else 293)) else (bif Nat.blt idx 128 then 0 else (bif Nat.blt idx 129 then 16421 else 0))) else (bif Nat.blt idx 133 then (bif Nat.blt idx 131 then 0 else (bif Nat.blt idx 132 then 0 else 8229)) else (bif Nat.blt idx 134 then 4133 else (bif Nat.blt idx 135 then 293 else 53)))))) else (bif Nat.blt idx 159 then (bif Nat.blt idx 147 then (bif Nat.blt idx 141 then (bif Nat.blt idx 138 then (bif Nat.blt idx 137 then 0 else 53) else 0) else (bif Nat.blt idx 144 then (bif Nat.blt idx 142 then 0 else (bif Nat.blt idx 143 then 0 else 57)) else (bif Nat.blt idx 145 then 0 else (bif Nat.blt idx 146 then 0 else 101)))) else (bif Nat.blt idx 153 then (bif Nat.blt idx 150 then (bif Nat.blt idx 148 then 0 else (bif Nat.blt idx 149 then 0 else 4133)) else (bif Nat.blt idx 151 then 2085 else 0)) else (bif Nat.blt idx 156 then (bif Nat.blt idx 154 then 549 else (bif Nat.blt idx 155 then 0 else 2085)) else (bif Nat.blt idx 157 then 101 else (bif Nat.blt idx 158 then 0 else 293))))) else (bif Nat.blt idx 170 then (bif Nat.blt idx 164 then (bif Nat.blt idx 161 then (bif Nat.blt idx 160 then 101 else 0) else (bif Nat.blt idx 162 then 0 else (bif Nat.blt idx 163 then 0 else 549))) else (bif Nat.blt idx 167 then (bif Nat.blt idx 165 then 0 else (bif Nat.blt idx 166 then 2085 else 8229)) else (bif Nat.blt idx 168 then 549 else (bif Nat.blt idx 169 then 0 else 1061)))) else (bif Nat.blt idx 176 then (bif Nat.blt idx 173 then (bif Nat.blt idx 171 then 0 else (bif Nat.blt idx 172 then 57 else 0)) else (bif Nat.blt idx 174 then 0 else (bif Nat.blt idx 175 then 53 else 0))) else (bif Nat.blt idx 179 then (bif Nat.blt idx 177 then 0 else (bif Nat.blt idx 178 then 57 else 53)) else 0)))))) else (bif Nat.blt idx 273 then (bif Nat.blt idx 227 then (bif Nat.blt idx 204 then (bif Nat.blt idx 193 then (bif Nat.blt idx 187 then 0 else (bif Nat.blt idx 190 then 0 else (bif Nat.blt idx 191 then 53 else 0))) else (bif Nat.blt idx 198 then (bif Nat.blt idx 195 then (bif Nat.blt idx 194 then 57 else 0) else (bif Nat.blt idx 196 then 0 else (bif Nat.blt idx 197 then 53 else 57))) else (bif Nat.blt idx 201 then (bif Nat.blt idx 199 then 8229 else 0) else (bif Nat.blt idx 202 then 101 else 0)))) else (bif Nat.blt idx 215 then (bif Nat.blt idx 209 then (bif Nat.blt idx 206 then (bif Nat.blt idx 205 then 0 else 101) else (bif Nat.blt idx 207 then 0 else (bif Nat.blt idx 208 then 549 else 16421))) else (bif Nat.blt idx 212 then (bif Nat.blt idx 210 then 0 else (bif Nat.blt idx 211 then 101 else 0)) else (bif Nat.blt idx 213 then 0 else (bif Nat.blt idx 214 then 0 else 101)))) else (bif Nat.blt idx 221 then (bif Nat.blt idx 218 then (bif Nat.blt idx 216 then 165 else (bif Nat.blt idx 217 then 0 else 549)) else 0) else (bif Nat.blt idx 224 then (bif Nat.blt idx 222 then 0 else (bif Nat.blt idx 223 then 0 else 16421)) else (bif Nat.blt idx 225 then 8229 else (bif Nat.blt idx 226 then 0 else 53)))))) else (bif Nat.blt idx 250 then (bif Nat.blt idx 238 then (bif Nat.blt idx 232 then (bif Nat.blt idx 229 then (bif Nat.blt idx 228 then 0 else 53) else (bif Nat.blt idx 230 then 0 else (bif Nat.blt idx 231 then 57 else 0))) else (bif Nat.blt idx 235 then 0 else (bif Nat.blt idx 236 then 2085 else (bif Nat.blt idx 237 then 0 else 165)))) else (bif Nat.blt idx 244 then (bif Nat.blt idx 241 then (bif Nat.blt idx 239 then 0 else (bif Nat.blt idx 240 then 165 else 8229)) else (bif Nat.blt idx 242 then 4133 else 0)) else (bif Nat.blt idx 247 then (bif Nat.blt idx 245 then 16421 else (bif Nat.blt idx 246 then 2085 else 0)) else (bif Nat.blt idx 248 then 165 else (bif Nat.blt idx 249 then 293 else 0))))) else (bif Nat.blt idx 261 then (bif Nat.blt idx 255 then (bif Nat.blt idx 252 then (bif Nat.blt idx 251 then 0 else 165) else (bif Nat.blt idx 253 then 16421 else (bif Nat.blt idx 254 then 0 else 101))) else (bif Nat.blt idx 258 then (bif Nat.blt idx 256 then 0 else (bif Nat.blt idx 257 then 4133 else 0)) else (bif Nat.blt idx 259 then 1061 else (bif Nat.blt idx 260 then 0 else 101)))) else (bif Nat.blt idx 267 then (bif Nat.blt idx 264 then (bif Nat.blt idx 262 then 0 else (bif Nat.blt idx 263 then 57 else 0)) else (bif Nat.blt idx 265 then 0 else (bif Nat.blt idx 266 then 53 else 0))) else (bif Nat.blt idx 270 then (bif Nat.blt idx 268 then 0 else (bif Nat.blt idx 269 then 57 else 53)) else 0))))) else (bif Nat.blt idx 318 then (bif Nat.blt idx 295 then (bif Nat.blt idx 284 then (bif Nat.blt idx 278 then 0 else (bif Nat.blt idx 281 then (bif Nat.blt idx 279 then 0 else (bif Nat.blt idx 280 then 57 else 0)) else (bif Nat.blt idx 282 then 53 else 0))) else (bif Nat.blt idx 289 then (bif Nat.blt idx 286 then 0 else (bif Nat.blt idx 287 then 0 else (bif Nat.blt idx 288 then 53 else 293))) else (bif Nat.blt idx 292 then (bif Nat.blt idx 290 then 0 else (bif Nat.blt idx 291 then 101 else 0)) else (bif Nat.blt idx 293 then 8229 else 0)))) else (bif Nat.blt idx 306 then (bif Nat.blt idx 300 then (bif Nat.blt idx 297 then (bif Nat.blt idx 296 then 1061 else 101) else (bif Nat.blt idx 298 then 0 else (bif Nat.blt idx 299 then 1061 else 0))) else (bif Nat.blt idx 303 then (bif Nat.blt idx 301 then 0 else (bif Nat.blt idx 302 then 165 else 0)) else (bif Nat.blt idx 304 then 0 else (bif Nat.blt idx 305 then 0 else 165)))) else (bif Nat.blt idx 312 then (bif Nat.blt idx 309 then (bif Nat.blt idx 307 then 0 else (bif Nat.blt idx 308 then 0 else 1061)) else (bif Nat.blt idx 310 then 0 else (bif Nat.blt idx 311 then 2085 else 1061))) else (bif Nat.blt idx 315 then 0 else (bif Nat.blt idx 316 then 0 else (bif Nat.blt idx 317 then 0 else 53)))))) else (bif Nat.blt idx 341 then (bif Nat.blt idx 329 then (bif Nat.blt idx 323 then (bif Nat.blt idx 320 then (bif Nat.blt idx 319 then 0 else 53) else (bif Nat.blt idx 321 then 57 else (bif Nat.blt idx 322 then 57 else 0))) else (bif Nat.blt idx 326 then (bif Nat.blt idx 324 then 0 else (bif Nat.blt idx 325 then 0 else 57)) else (bif Nat.blt idx 327 then 0 else (bif Nat.blt idx 328 then 53 else 0)))) else (bif Nat.blt idx 335 then (bif Nat.blt idx 332 then (bif Nat.blt idx 330 then 57 else 0) else (bif Nat.blt idx 333 then 0 else (bif Nat.blt idx 334 then 293 else 0))) else (bif Nat.blt idx 338 then (bif Nat.blt idx 336 then 0 else (bif Nat.blt idx 337 then 4133 else 0)) else (bif Nat.blt idx 339 then 0 else (bif Nat.blt idx 340 then 549 else 0))))) else (bif Nat.blt idx 352 then (bif Nat.blt idx 346 then (bif Nat.blt idx 343 then (bif Nat.blt idx 342 then 0 else 8229) else (bif Nat.blt idx 344 then 0 else (bif Nat.blt idx 345 then 0 else 101))) else (bif Nat.blt idx 349 then 0 else (bif Nat.blt idx 350 then 101 else (bif Nat.blt idx 351 then 0 else 53)))) else (bif Nat.blt idx 358 then (bif Nat.blt idx 355 then (bif Nat.blt idx 353 then 0 else (bif Nat.blt idx 354 then 57 else 0)) else 0) else (bif Nat.blt idx 361 then (bif Nat.blt idx 359 then 0 else (bif Nat.blt idx 360 then 57 else 0)) else 0))))))) else (bif Nat.blt idx 546 then (bif Nat.blt idx 455 then (bif Nat.blt idx 409 then (bif Nat.blt idx 386 then (bif Nat.blt idx 375 then (bif Nat.blt idx 369 then 0 else (bif Nat.blt idx 372 then (bif Nat.blt idx 370 then 549 else 0) else (bif Nat.blt idx 373 then 8229 else 0))) else (bif Nat.blt idx 380 then (bif Nat.blt idx 377 then (bif Nat.blt idx 376 then 0 else 549) else (bif Nat.blt idx 378 then 0 else (bif Nat.blt idx 379 then 16421 else 549))) else (bif Nat.blt idx 383 then (bif Nat.blt idx 381 then 0 else (bif Nat.blt idx 382 then 165 else 0)) else 0))) else (bif Nat.blt idx 397 then (bif Nat.blt idx 391 then (bif Nat.blt idx 388 then (bif Nat.blt idx 387 then 101 else 293) else (bif Nat.blt idx 389 then 0 else (bif Nat.blt idx 390 then 101 else 2085))) else (bif Nat.blt idx 394 then (bif Nat.blt idx 392 then 0 else (bif Nat.blt idx 393 then 549 else 0)) else (bif Nat.blt idx 395 then 0 else (bif Nat.blt idx 396 then 0 else 4133)))) else (bif Nat.blt idx 403 then (bif Nat.blt idx 400 then (bif Nat.blt idx 398 then 0 else (bif Nat.blt idx 399 then 0 else 101)) else (bif Nat.blt idx 401 then 0 else (bif Nat.blt idx 402 then 0 else 101))) else (bif Nat.blt idx 406 then 0 else (bif Nat.blt idx 407 then 57 else 0))))) else (bif Nat.blt idx 432 then (bif Nat.blt idx 420 then (bif Nat.blt idx 414 then (bif Nat.blt idx 411 then (bif Nat.blt idx 410 then 57 else 0) else (bif Nat.blt idx 412 then 0 else 53)) else (bif Nat.blt idx 417 then (bif Nat.blt idx 415 then 293 else (bif Nat.blt idx 416 then 0 else 16421)) else 0)) else (bif Nat.blt idx 426 then (bif Nat.blt idx 423 then (bif Nat.blt idx 421 then 8229 else (bif Nat.blt idx 422 then 4133 else 293)) else (bif Nat.blt idx 424 then 549 else (bif Nat.blt idx 425 then 16421 else 0))) else (bif Nat.blt idx 429 then (bif Nat.blt idx 427 then 101 else 0) else (bif Nat.blt idx 430 then 0 else (bif Nat.blt idx 431 then 101 else 165))))) else (bif Nat.blt idx 443 then (bif Nat.blt idx 437 then (bif Nat.blt idx 434 then (bif Nat.blt idx 433 then 293 else 0) else (bif Nat.blt idx 435 then 101 else (bif Nat.blt idx 436 then 0 else 8229))) else (bif Nat.blt idx 440 then (bif Nat.blt idx 438 then 0 else (bif Nat.blt idx 439 then 0 else 1061)) else (bif Nat.blt idx 441 then 101 else (bif Nat.blt idx 442 then 549 else 0)))) else (bif Nat.blt idx 449 then (bif Nat.blt idx 446 then (bif Nat.blt idx 444 then 0 else (bif Nat.blt idx 445 then 8229 else 0)) else (bif Nat.blt idx 447 then 0 else (bif Nat.blt idx 448 then 0 else 549))) else 0)))) else (bif Nat.blt idx 500 then (bif Nat.blt idx 477 then (bif Nat.blt idx 466 then (bif Nat.blt idx 460 then 0 else (bif Nat.blt idx 463 then (bif Nat.blt idx 461 then 8229 else 0) else 0)) else (bif Nat.blt idx 471 then (bif Nat.blt idx 468 then (bif Nat.blt idx 467 then 165 else 101) else (bif Nat.blt idx 469 then 53 else (bif Nat.blt idx 470 then 0 else 57))) else (bif Nat.blt idx 474 then 0 else (bif Nat.blt idx 475 then 0 else (bif Nat.blt idx 476 then 0 else 53))))) else (bif Nat.blt idx 488 then (bif Nat.blt idx 482 then (bif Nat.blt idx 479 then (bif Nat.blt idx 478 then 53 else 0) else (bif Nat.blt idx 480 then 0 else (bif Nat.blt idx 481 then 57 else 0))) else (bif Nat.blt idx 485 then (bif Nat.blt idx 483 then 0 else (bif Nat.blt idx 484 then 57 else 53)) else (bif Nat.blt idx 486 then 0 else (bif Nat.blt idx 487 then 0 else 1061)))) else (bif Nat.blt idx 494 then (bif Nat.blt idx 491 then (bif Nat.blt idx 489 then 0 else (bif Nat.blt idx 490 then 0 else 16421)) else 0) else (bif Nat.blt idx 497 then (bif Nat.blt idx 495 then 1061 else (bif Nat.blt idx 496 then 57 else 0)) else (bif Nat.blt idx 498 then 57 else 0))))) else (bif Nat.blt idx 523 then (bif Nat.blt idx 511 then (bif Nat.blt idx 505 then (bif Nat.blt idx 502 then 0 else (bif Nat.blt idx 503 then 0 else (bif Nat.blt idx 504 then 53 else 0))) else (bif Nat.blt idx 508 then (bif Nat.blt idx 506 then 549 else 0) else 0)) else (bif Nat.blt idx 517 then (bif Nat.blt idx 514 then (bif Nat.blt idx 512 then 16421 else (bif Nat.blt idx 513 then 8229 else 0)) else (bif Nat.blt idx 515 then 1061 else 0)) else (bif Nat.blt idx 520 then (bif Nat.blt idx 518 then 165 else 0) else (bif Nat.blt idx 521 then 0 else (bif Nat.blt idx 522 then 165 else 16421))))) else (bif Nat.blt idx 534 then (bif Nat.blt idx 528 then (bif Nat.blt idx 525 then (bif Nat.blt idx 524 then 549 else 0) else (bif Nat.blt idx 526 then 165 else 0)) else (bif Nat.blt idx 531 then (bif Nat.blt idx 529 then 0 else (bif Nat.blt idx 530 then 0 else 101)) else (bif Nat.blt idx 532 then 0 else (bif Nat.blt idx 533 then 8229 else 0)))) else (bif Nat.blt idx 540 then (bif Nat.blt idx 537 then 0 else (bif Nat.blt idx 538 then 0 else (bif Nat.blt idx 539 then 165 else 101))) else 0))))) else (bif Nat.blt idx 637 then (bif Nat.blt idx 591 then (bif Nat.blt idx 568 then (bif Nat.blt idx 557 then (bif Nat.blt idx 551 then (bif Nat.blt idx 548 then 0 else (bif Nat.blt idx 549 then 0 else (bif Nat.blt idx 550 then 0 else 2085))) else (bif Nat.blt idx 554 then (bif Nat.blt idx 552 then 16421 else 0) else (bif Nat.blt idx 555 then 165 else 0))) else (bif Nat.blt idx 562 then (bif Nat.blt idx 559 then (bif Nat.blt idx 558 then 293 else 0) else (bif Nat.blt idx 560 then 53 else (bif Nat.blt idx 561 then 0 else 57))) else (bif Nat.blt idx 565 then (bif Nat.blt idx 563 then 0 else (bif Nat.blt idx 564 then 57 else 0)) else 0))) else (bif Nat.blt idx 579 then (bif Nat.blt idx 573 then (bif Nat.blt idx 570 then (bif Nat.blt idx 569 then 0 else 1061) else (bif Nat.blt idx 571 then 0 else (bif Nat.blt idx 572 then 293 else 165))) else (bif Nat.blt idx 576 then 0 else (bif Nat.blt idx 577 then 0 else (bif Nat.blt idx 578 then 0 else 101)))) else (bif Nat.blt idx 585 then (bif Nat.blt idx 582 then (bif Nat.blt idx 580 then 0 else (bif Nat.blt idx 581 then 0 else 4133)) else (bif Nat.blt idx 583 then 2085 else 0)) else (bif Nat.blt idx 588 then (bif Nat.blt idx 586 then 0 else (bif Nat.blt idx 587 then 57 else 0)) else (bif Nat.blt idx 589 then 57 else (bif Nat.blt idx 590 then 0 else 53)))))) else (bif Nat.blt idx 614 then (bif Nat.blt idx 602 then (bif Nat.blt idx 596 then 0 else (bif Nat.blt idx 599 then (bif Nat.blt idx 597 then 1061 else (bif Nat.blt idx 598 then 0 else 2085)) else (bif Nat.blt idx 600 then 1061 else 0))) else (bif Nat.blt idx 608 then (bif Nat.blt idx 605 then (bif Nat.blt idx 603 then 0 else (bif Nat.blt idx 604 then 293 else 0)) else (bif Nat.blt idx 606 then 101 else (bif Nat.blt idx 607 then 2085 else 0))) else (bif Nat.blt idx 611 then (bif Nat.blt idx 609 then 549 else 0) else (bif Nat.blt idx 612 then 0 else (bif Nat.blt idx 613 then 57 else 0))))) else (bif Nat.blt idx 625 then (bif Nat.blt idx 619 then (bif Nat.blt idx 616 then (bif Nat.blt idx 615 then 53 else 0) else 0) else (bif Nat.blt idx 622 then (bif Nat.blt idx 620 then 0 else (bif Nat.blt idx 621 then 57 else 0)) else (bif Nat.blt idx 623 then 2085 else (bif Nat.blt idx 624 then 16421 else 0)))) else (bif Nat.blt idx 631 then (bif Nat.blt idx 628 then (bif Nat.blt idx 626 then 0 else (bif Nat.blt idx 627 then 165 else 0)) else (bif Nat.blt idx 629 then 0 else (bif Nat.blt idx 630 then 293 else 0))) else 0)))) else (bif Nat.blt idx 683 then (bif Nat.blt idx 660 then (bif Nat.blt idx 648 then (bif Nat.blt idx 642 then (bif Nat.blt idx 639 then 0 else (bif Nat.blt idx 640 then 0 else (bif Nat.blt idx 641 then 0 else 4133))) else (bif Nat.blt idx 645 then (bif Nat.blt idx 643 then 0 else (bif Nat.blt idx 644 then 0 else 293)) else (bif Nat.blt idx 646 then 293 else 0))) else (bif Nat.blt idx 654 then (bif Nat.blt idx 651 then (bif Nat.blt idx 649 then 0 else (bif Nat.blt idx 650 then 549 else 0)) else (bif Nat.blt idx 652 then 165 else (bif Nat.blt idx 653 then 4133 else 165))) else (bif Nat.blt idx 657 then (bif Nat.blt idx 655 then 1061 else 0) else (bif Nat.blt idx 658 then 549 else (bif Nat.blt idx 659 then 0 else 2085))))) else (bif Nat.blt idx 671 then (bif Nat.blt idx 665 then (bif Nat.blt idx 662 then (bif Nat.blt idx 661 then 101 else 0) else (bif Nat.blt idx 663 then 293 else (bif Nat.blt idx 664 then 101 else 0))) else (bif Nat.blt idx 668 then (bif Nat.blt idx 666 then 0 else (bif Nat.blt idx 667 then 0 else 2085)) else (bif Nat.blt idx 669 then 0 else (bif Nat.blt idx 670 then 165 else 0)))) else (bif Nat.blt idx 677 then (bif Nat.blt idx 674 then (bif Nat.blt idx 672 then 165 else (bif Nat.blt idx 673 then 8229 else 4133)) else 0) else (bif Nat.blt idx 680 then (bif Nat.blt idx 678 then 57 else (bif Nat.blt idx 679 then 0 else 57)) else (bif Nat.blt idx 681 then 53 else (bif Nat.blt idx 682 then 53 else 0)))))) else (bif Nat.blt idx 706 then (bif Nat.blt idx 694 then (bif Nat.blt idx 688 then (bif Nat.blt idx 685 then (bif Nat.blt idx 684 then 0 else 4133) else (bif Nat.blt idx 686 then 0 else (bif Nat.blt idx 687 then 0 else 101))) else (bif Nat.blt idx 691 then (bif Nat.blt idx 689 then 0 else (bif Nat.blt idx 690 then 0 else 101)) else (bif Nat.blt idx 692 then 0 else (bif Nat.blt idx 693 then 0 else 57)))) else (bif Nat.blt idx 700 then (bif Nat.blt idx 697 then (bif Nat.blt idx 695 then 0 else (bif Nat.blt idx 696 then 0 else 53)) else (bif Nat.blt idx 698 then 0 else (bif Nat.blt idx 699 then 0 else 53))) else (bif Nat.blt idx 703 then (bif Nat.blt idx 701 then 57 else 0) else (bif Nat.blt idx 704 then 57 else (bif Nat.blt idx 705 then 0 else 53))))) else (bif Nat.blt idx 717 then (bif Nat.blt idx 711 then (bif Nat.blt idx 708 then (bif Nat.blt idx 707 then 0 else 53) else 0) else (bif Nat.blt idx 714 then (bif Nat.blt idx 712 then 0 else (bif Nat.blt idx 713 then 0 else 4133)) else (bif Nat.blt idx 715 then 0 else (bif Nat.blt idx 716 then 0 else 293)))) else (bif Nat.blt idx 723 then (bif Nat.blt idx 720 then (bif Nat.blt idx 718 then 293 else 0) else 0) else 0)))))))

def witness (i j k : Vertex) : Nat := witnessAt (i.val * 81 + j.val * 9 + k.val)


def bad (i j k : Vertex) : Prop := witness i j k ≠ 0

def response (i j k : Vertex) (m u : Nat) : Bool × Bool :=
  (petersenF (cube i j k m u false), petersenF (cube i j k m u true))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
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
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [i.isLt]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma cover_shapes (s : Finset Vertex) (card : s.card ≤ 5)
    (covers : ∀ e ∈ edges, e.1 ∈ s ∨ e.2 ∈ s) : sᶜ ∈ cuts ∧ s.card = 5 := by
  obtain ⟨m,rfl⟩ := represented s
  have hh : ∀ m : BitVec 9, (maskSet m).card ≤ 5 →
      edges.all (fun e => decide (e.1 ∈ maskSet m ∨ e.2 ∈ maskSet m)) = true →
      (maskSet m)ᶜ ∈ cuts ∧ (maskSet m).card = 5 := by decide +kernel
  exact hh m card (List.all_eq_true.mpr fun e he => decide_eq_true (covers e he))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma pair_check :
    ∀ i j k : Vertex, i ≠ j → petersenGraph.Adj i k → petersenGraph.Adj j k →
      witness i j k ≠ 0 := by
  change ∀ i j k : Vertex, i ≠ j → ((i,k) ∈ edges ∨ (k,i) ∈ edges) →
    ((j,k) ∈ edges ∨ (k,j) ∈ edges) → witness i j k ≠ 0
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
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
  let _ : DecidableRel petersenGraph.Adj := petersenAdjDecidable
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
  [(102,8),(74,4),(84,2),(56,64),(102,1),(102,16),(74,1),(74,16),(74,32),(84,1),(84,8),(84,32),(56,1),(56,2),(56,4)]

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

def kNat (n : Nat) : Nat :=
  let nx := Nat.xor n 127
  bif Nat.ble n nx then n else nx

def seedsMask : Nat := 0x2800000100010100

def bits64Aux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | k + 1, m, acc =>
    bits64Aux k m (bif m.testBit k then k :: acc else acc)

def bits64 (m : Nat) : List Nat := bits64Aux 64 m []

def pair4 (a b : Nat) : Nat :=
  let na := Nat.xor a 127
  let nb := Nat.xor b 127
  let p1 := 1 <<< kNat (Nat.land a b)
  let p2 := 1 <<< kNat (Nat.land a nb)
  let p3 := 1 <<< kNat (Nat.land na b)
  let p4 := 1 <<< kNat (Nat.land na nb)
  Nat.lor (Nat.lor p1 p2) (Nat.lor p3 p4)

def prodPairs (a : Nat) : List Nat → Nat → Nat
  | [], pm => pm
  | b :: bs, pm => prodPairs a bs (Nat.lor pm (pair4 a b))

def prodAll : List Nat → List Nat → Nat → Nat
  | [], _, pm => pm
  | a :: as, allB, pm => prodAll as allB (prodPairs a allB pm)

def prodMask (m : Nat) : Nat :=
  let bs := bits64 m
  prodAll bs bs 0

def fastWeCan (wanted : List Nat) : Nat → Nat → Bool
  | 0, m => (wanted.filter (fun q => !(m.testBit q))).isEmpty
  | k + 1, m =>
    let need := wanted.filter (fun q => !(m.testBit q))
    bif need.isEmpty then true
    else bif Nat.blt (k + 1) need.length then false
    else
      let pm := prodMask m
      let cands := bif Nat.beq need.length (k + 1) then
        need.filter (fun q => pm.testBit q)
      else
        (bits64 pm).filter (fun q => !(m.testBit q))
      cands.any (fun q => fastWeCan wanted k (Nat.lor m (1 <<< q)))

def covMaskOf (z : Nat) : Nat :=
  bif Nat.ble 72 z then 0 else (bif Nat.blt z 36 then (bif Nat.blt z 18 then (bif Nat.blt z 9 then (bif Nat.blt z 4 then (bif Nat.blt z 2 then (bif Nat.blt z 1 then 0 else 4688) else (bif Nat.blt z 3 then 8196 else 12804)) else (bif Nat.blt z 6 then (bif Nat.blt z 5 then 16386 else 20546) else (bif Nat.blt z 7 then 24576 else (bif Nat.blt z 8 then 28672 else 1025)))) else (bif Nat.blt z 13 then (bif Nat.blt z 11 then (bif Nat.blt z 10 then 1553 else 1028) else (bif Nat.blt z 12 then 1540 else 0)) else (bif Nat.blt z 15 then 0 else (bif Nat.blt z 16 then 0 else (bif Nat.blt z 17 then 160 else 240))))) else (bif Nat.blt z 27 then (bif Nat.blt z 22 then (bif Nat.blt z 20 then 0 else (bif Nat.blt z 21 then 130 else 194)) else (bif Nat.blt z 24 then 0 else (bif Nat.blt z 25 then 33 else (bif Nat.blt z 26 then 49 else 0)))) else (bif Nat.blt z 31 then 0 else (bif Nat.blt z 33 then (bif Nat.blt z 32 then 0 else 2304) else (bif Nat.blt z 34 then 2880 else (bif Nat.blt z 35 then 2052 else 2564)))))) else (bif Nat.blt z 54 then (bif Nat.blt z 45 then (bif Nat.blt z 40 then (bif Nat.blt z 38 then (bif Nat.blt z 37 then 258 else 322) else 0) else (bif Nat.blt z 42 then (bif Nat.blt z 41 then 3072 else 3584) else (bif Nat.blt z 43 then 3076 else (bif Nat.blt z 44 then 3588 else 0)))) else (bif Nat.blt z 49 then (bif Nat.blt z 47 then 0 else (bif Nat.blt z 48 then 0 else 384)) else (bif Nat.blt z 51 then (bif Nat.blt z 50 then 448 else 0) else (bif Nat.blt z 52 then 0 else (bif Nat.blt z 53 then 386 else 450))))) else (bif Nat.blt z 63 then 0 else (bif Nat.blt z 67 then (bif Nat.blt z 65 then (bif Nat.blt z 64 then 0 else 8) else (bif Nat.blt z 66 then 4104 else 8200)) else (bif Nat.blt z 69 then (bif Nat.blt z 68 then 12296 else 16392) else (bif Nat.blt z 70 then 20488 else (bif Nat.blt z 71 then 24584 else 28680)))))))

def optsNat : Nat → List Nat
  | 0 => [8,9,24,25]
  | 1 => [4,5,20,21,36,37,52,53]
  | 2 => [2,3,10,11,34,35,42,43]
  | 3 => [64,65,66,67,68,69,70,71]
  | 4 => [1,9,17,25]
  | 5 => [16,17,24,25]
  | 6 => [1,5,17,21,33,37,49,53]
  | 7 => [16,17,20,21,48,49,52,53]
  | 8 => [32,33,36,37,48,49,52,53]
  | 9 => [1,3,9,11,33,35,41,43]
  | 10 => [8,9,10,11,40,41,42,43]
  | 11 => [32,33,34,35,40,41,42,43]
  | 12 => [1,3,5,7,65,67,69,71]
  | 13 => [2,3,6,7,66,67,70,71]
  | 14 => [4,5,6,7,68,69,70,71]
  | _ => []

def firstUncovAux : Nat → Nat → Nat → Nat
  | 0, _, i => i
  | r + 1, cov, i => bif cov.testBit i then firstUncovAux r cov (i + 1) else i

def firstUncov (cov : Nat) : Nat := firstUncovAux 15 cov 0

def remLb4 (cov : Nat) : Nat :=
  (bif cov.testBit 0 then 0 else 1) +
  (bif cov.testBit 1 then 0 else 1) +
  (bif cov.testBit 2 then 0 else 1) +
  (bif cov.testBit 3 then 0 else 1)

def remLb (cov : Nat) : Nat :=
  let s := remLb4 cov
  bif Nat.beq s 0 then (bif Nat.beq cov 32767 then 0 else 1) else s

def fastSolve : Nat → Nat → Nat → List Nat → Bool
  | 0, chLen, cov, wanted =>
    !(Nat.blt 9 (chLen + wanted.length)) &&
      Nat.beq cov 32767 && fastWeCan wanted (9 - chLen) seedsMask
  | k + 1, chLen, cov, wanted =>
    bif Nat.blt 9 (chLen + remLb cov + wanted.length) then false
    else bif Nat.beq cov 32767 then fastWeCan wanted (9 - chLen) seedsMask
    else
      let idx := firstUncov cov
      (optsNat idx).any fun z =>
        let kz := kNat z
        let w2 := bif seedsMask.testBit kz || wanted.contains kz then wanted else kz :: wanted
        fastSolve k (chLen + 1) (Nat.lor cov (covMaskOf z)) w2

lemma nat_blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff]
  intro ht
  rw [Nat.blt_eq] at ht
  omega

lemma nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff]
  intro ht
  exact h (Nat.beq_eq.mp ht)

lemma nat_beq_false_ne {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  rintro rfl
  simp at h

lemma key_spec : ∀ z : M,
    (key z).toNat = kNat z.toNat ∧ (key z).toNat < 64 ∧ (~~~z).toNat = Nat.xor z.toNat 127 := by
  decide +kernel

lemma seeds_spec : ∀ a ∈ seeds, a.toNat < 64 ∧ seedsMask.testBit a.toNat = true := by decide +kernel

lemma covMaskOf_lt : ∀ z : M, covMaskOf z.toNat < 2 ^ 15 := by decide +kernel

lemma covMaskOf_spec : ∀ (z : M) (i : Fin 15),
    (covMaskOf z.toNat).testBit i.val = hit (cells.getD i.val (0, 0)) z := by decide +kernel

lemma optsNat_spec : ∀ (i : Fin 15) (z : M),
    hit (cells.getD i.val (0, 0)) z = true → z.toNat ∈ optsNat i.val := by decide +kernel

lemma disj4_spec : ∀ (z : M) (i j : Fin 4),
    hit (cells.getD i.val (0, 0)) z = true →
    hit (cells.getD j.val (0, 0)) z = true → i = j := by decide +kernel

lemma testBit_one_shift_self (q : Nat) : (1 <<< q).testBit q = true := by
  simp

lemma pair4_spec (u v : M) :
    (pair4 u.toNat v.toNat).testBit (key (u &&& v)).toNat = true ∧
    (pair4 u.toNat v.toNat).testBit (key (u &&& ~~~v)).toNat = true ∧
    (pair4 u.toNat v.toNat).testBit (key (~~~u &&& v)).toNat = true ∧
    (pair4 u.toNat v.toNat).testBit (key (~~~u &&& ~~~v)).toNat = true := by
  have e1 : (key (u &&& v)).toNat = kNat (Nat.land u.toNat v.toNat) := by
    rw [(key_spec (u &&& v)).1, BitVec.toNat_and, Nat.land_eq]
  have e2 : (key (u &&& ~~~v)).toNat = kNat (Nat.land u.toNat (Nat.xor v.toNat 127)) := by
    rw [(key_spec (u &&& ~~~v)).1, BitVec.toNat_and, (key_spec v).2.2, Nat.land_eq]
  have e3 : (key (~~~u &&& v)).toNat = kNat (Nat.land (Nat.xor u.toNat 127) v.toNat) := by
    rw [(key_spec (~~~u &&& v)).1, BitVec.toNat_and, (key_spec u).2.2, Nat.land_eq]
  have e4 : (key (~~~u &&& ~~~v)).toNat = kNat (Nat.land (Nat.xor u.toNat 127) (Nat.xor v.toNat 127)) := by
    rw [(key_spec (~~~u &&& ~~~v)).1, BitVec.toNat_and, (key_spec u).2.2, (key_spec v).2.2, Nat.land_eq]
  unfold pair4
  simp only [Nat.lor_eq, Nat.testBit_or, e1, e2, e3, e4, testBit_one_shift_self,
    Bool.true_or, Bool.or_true, and_self]

lemma mem_bits64Aux (n m : Nat) (acc : List Nat) (q : Nat) :
    q ∈ bits64Aux n m acc ↔ q ∈ acc ∨ (q < n ∧ m.testBit q = true) := by
  induction n generalizing acc with
  | zero => simp [bits64Aux]
  | succ k ih =>
    rw [bits64Aux, ih]
    cases h : m.testBit k
    · simp only [Bool.cond_false]
      constructor
      · rintro (hq | ⟨hq1, hq2⟩)
        · exact Or.inl hq
        · exact Or.inr ⟨by omega, hq2⟩
      · rintro (hq | ⟨hq1, hq2⟩)
        · exact Or.inl hq
        · have hne : q ≠ k := fun e => by rw [e, h] at hq2; cases hq2
          exact Or.inr ⟨by omega, hq2⟩
    · simp only [Bool.cond_true, List.mem_cons]
      constructor
      · rintro ((rfl | hq) | ⟨hq1, hq2⟩)
        · exact Or.inr ⟨by omega, h⟩
        · exact Or.inl hq
        · exact Or.inr ⟨by omega, hq2⟩
      · rintro (hq | ⟨hq1, hq2⟩)
        · exact Or.inl (Or.inr hq)
        · by_cases he : q = k
          · exact Or.inl (Or.inl he)
          · exact Or.inr ⟨by omega, hq2⟩

lemma mem_bits64 (m q : Nat) : q ∈ bits64 m ↔ q < 64 ∧ m.testBit q = true := by
  simpa [bits64] using mem_bits64Aux 64 m [] q

lemma prodPairs_mono (a : Nat) (bs : List Nat) (pm q : Nat) (h : pm.testBit q = true) :
    (prodPairs a bs pm).testBit q = true := by
  induction bs generalizing pm with
  | nil => exact h
  | cons b bs ih =>
    apply ih
    simp [Nat.lor_eq, h]

lemma prodPairs_mem (a b : Nat) (bs : List Nat) (hb : b ∈ bs) (pm q : Nat)
    (h : (pair4 a b).testBit q = true) : (prodPairs a bs pm).testBit q = true := by
  induction bs generalizing pm with
  | nil => cases hb
  | cons x bs ih =>
    simp only [prodPairs]
    rcases List.mem_cons.mp hb with rfl | hmem
    · apply prodPairs_mono
      simp [Nat.lor_eq, h]
    · exact ih hmem _

lemma prodAll_mono (as allB : List Nat) (pm q : Nat) (h : pm.testBit q = true) :
    (prodAll as allB pm).testBit q = true := by
  induction as generalizing pm with
  | nil => exact h
  | cons a as ih => exact ih _ (prodPairs_mono a allB pm q h)

lemma prodAll_mem (a b : Nat) (as allB : List Nat) (ha : a ∈ as) (hb : b ∈ allB) (pm q : Nat)
    (h : (pair4 a b).testBit q = true) : (prodAll as allB pm).testBit q = true := by
  induction as generalizing pm with
  | nil => cases ha
  | cons x as ih =>
    simp only [prodAll]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact prodAll_mono as allB _ q (prodPairs_mem a b allB hb pm q h)
    · exact ih hmem _

lemma prodMask_of_products {xs : List M} {m : Nat}
    (hxs : ∀ x ∈ xs, x.toNat < 64 ∧ m.testBit x.toNat = true)
    {a : M} (ha : a ∈ products xs) :
    a.toNat < 64 ∧ (prodMask m).testBit a.toNat = true := by
  unfold products at ha
  rw [List.mem_flatMap] at ha
  obtain ⟨x, hx, hy⟩ := ha
  rw [List.mem_map] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  refine ⟨(key_spec (x &&& y)).2.1, ?_⟩
  unfold lits at hx hy
  rw [List.mem_append, List.mem_map] at hx hy
  have memB (u : M) (hu : u ∈ xs) : u.toNat ∈ bits64 m :=
    (mem_bits64 m u.toNat).mpr (hxs u hu)
  rcases hx with ux | ⟨u, ux, rfl⟩ <;> rcases hy with vy | ⟨v, vy, rfl⟩
  · exact prodAll_mem _ _ _ _ (memB x ux) (memB y vy) 0 _ (pair4_spec x y).1
  · exact prodAll_mem _ _ _ _ (memB x ux) (memB v vy) 0 _ (pair4_spec x v).2.1
  · exact prodAll_mem _ _ _ _ (memB u ux) (memB y vy) 0 _ (pair4_spec u y).2.2.1
  · exact prodAll_mem _ _ _ _ (memB u ux) (memB v vy) 0 _ (pair4_spec u v).2.2.2

lemma need_len_le {wanted : List Nat} {m : Nat} {tail : List M}
    (hnd : wanted.Nodup)
    (hall : ∀ q ∈ wanted, m.testBit q = true ∨ q ∈ tail.map BitVec.toNat) :
    (wanted.filter (fun q => !(m.testBit q))).length ≤ tail.length := by
  let need := wanted.filter (fun q => !(m.testBit q))
  have nd_need : need.Nodup := hnd.filter _
  have sub : need.toFinset ⊆ (tail.map BitVec.toNat).toFinset := by
    intro q hq
    have hm := List.mem_filter.mp (List.mem_toFinset.mp hq)
    have hmf : m.testBit q = false := by simpa using hm.2
    exact List.mem_toFinset.mpr ((hall q hm.1).resolve_left (by simp [hmf]))
  calc need.length
    _ = need.toFinset.card := (List.toFinset_card_of_nodup nd_need).symm
    _ ≤ (tail.map BitVec.toNat).toFinset.card := Finset.card_le_card sub
    _ ≤ (tail.map BitVec.toNat).length := List.toFinset_card_le _
    _ = tail.length := List.length_map _

lemma fastWeCan_ok {wanted : List Nat} (hnd : wanted.Nodup) {xs tail : List M} {fuel m : Nat}
    (hrun : Builds xs tail)
    (hxs : ∀ x ∈ xs, x.toNat < 64 ∧ m.testBit x.toNat = true)
    (hsmall : tail.length ≤ fuel)
    (hall : ∀ q ∈ wanted, m.testBit q = true ∨ q ∈ tail.map BitVec.toNat) :
    fastWeCan wanted fuel m = true := by
  induction tail generalizing fuel xs m with
  | nil =>
    have hemp : (wanted.filter (fun q => !(m.testBit q))).isEmpty = true := by
      rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
      intro q hq
      have hm := List.mem_filter.mp hq
      have h1 := hall q hm.1
      simp at h1
      simp [h1] at hm
    cases fuel with
    | zero => simp [fastWeCan, hemp]
    | succ k => simp [fastWeCan, hemp]
  | cons a rest ih =>
    obtain ⟨hprod, hrest⟩ := hrun
    obtain ⟨halt64, hpm⟩ := prodMask_of_products hxs hprod
    by_cases halr : m.testBit a.toNat = true
    · apply ih (xs := a :: xs) hrest
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨halt64, halr⟩
        · exact hxs x hx
      · exact Nat.le_trans (Nat.le_succ _) hsmall
      · intro q hq
        rcases hall q hq with h | h
        · exact Or.inl h
        · simp only [List.map_cons, List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inl halr
          · exact Or.inr h
    · have halrf : m.testBit a.toNat = false := Bool.eq_false_iff.mpr halr
      cases fuel with
      | zero => simp at hsmall
      | succ k =>
        have hlen : (wanted.filter (fun q => !(m.testBit q))).length ≤ k + 1 :=
          (need_len_le hnd hall).trans hsmall
        rw [fastWeCan]
        cases hemp : (wanted.filter (fun q => !(m.testBit q))).isEmpty
        · simp only [Bool.cond_false]
          have hblt : Nat.blt (k + 1) (wanted.filter (fun q => !(m.testBit q))).length = false :=
            nat_blt_false hlen
          rw [hblt]; simp only [Bool.cond_false]
          let m2 := Nat.lor m (1 <<< a.toNat)
          have hm2_self : m2.testBit a.toNat = true := by
            simp [m2, Nat.lor_eq]
          have hm2_mono : ∀ r, m.testBit r = true → m2.testBit r = true := by
            intro r hr; simp [m2, Nat.lor_eq, hr]
          have hrec : fastWeCan wanted k m2 = true := by
            apply ih (xs := a :: xs) hrest
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨halt64, hm2_self⟩
              · exact ⟨(hxs x hx).1, hm2_mono _ (hxs x hx).2⟩
            · simp only [List.length_cons] at hsmall; omega
            · intro q hq
              rcases hall q hq with h | h
              · exact Or.inl (hm2_mono q h)
              · simp only [List.map_cons, List.mem_cons] at h
                rcases h with rfl | h
                · exact Or.inl hm2_self
                · exact Or.inr h
          apply List.any_eq_true.mpr
          refine ⟨a.toNat, ?_, hrec⟩
          cases hbeq : Nat.beq (wanted.filter (fun q => !(m.testBit q))).length (k + 1)
          · simp only [Bool.cond_false, List.mem_filter, mem_bits64]
            exact ⟨⟨halt64, hpm⟩, by simp [halrf]⟩
          · simp only [Bool.cond_true, List.mem_filter]
            have heq_len : (wanted.filter (fun q => !(m.testBit q))).length = k + 1 :=
              Nat.beq_eq.mp hbeq
            refine ⟨?_, hpm⟩
            by_contra hnot_need
            have hnot_w : a.toNat ∉ wanted := by
              intro hw
              exact hnot_need ⟨hw, by simp [halrf]⟩
            have hle_rest : (wanted.filter (fun q => !(m.testBit q))).length ≤ rest.length := by
              apply need_len_le hnd
              intro q hq
              rcases hall q hq with h | h
              · exact Or.inl h
              · simp only [List.map_cons, List.mem_cons] at h
                rcases h with rfl | h
                · exact False.elim (hnot_w hq)
                · exact Or.inr h
            simp only [List.length_cons] at hsmall
            omega
        · rfl

lemma firstUncovAux_spec (r cov i : Nat)
    (hprev : ∀ j < i, cov.testBit j = true) :
    (firstUncovAux r cov i < i + r ∧ cov.testBit (firstUncovAux r cov i) = false) ∨
      (firstUncovAux r cov i = i + r ∧ ∀ j < i + r, cov.testBit j = true) := by
  induction r generalizing i with
  | zero =>
    exact Or.inr ⟨by simp [firstUncovAux], by simpa using hprev⟩
  | succ r ih =>
    rw [firstUncovAux]
    cases h : cov.testBit i
    · simp only [Bool.cond_false]
      exact Or.inl ⟨by omega, h⟩
    · simp only [Bool.cond_true]
      have hprev' : ∀ j < i + 1, cov.testBit j = true := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact hprev j hlt
        · exact h
      rcases ih (i + 1) hprev' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨by omega, fun j hj => h2 j (by omega)⟩

lemma all_bits_15_eq {cov : Nat} (hlt : cov < 2 ^ 15)
    (hall : ∀ j < 15, cov.testBit j = true) : cov = 32767 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 15
  · rw [hall j hj]
    have h32 : (32767 : Nat) = 2 ^ 15 - 1 := rfl
    rw [h32, Nat.testBit_two_pow_sub_one]
    simp [hj]
  · have hge : 15 ≤ j := by omega
    have h1 : cov.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hge))
    have h32lt : (32767 : Nat) < 2 ^ 15 := by decide
    have h2 : (32767 : Nat).testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h32lt (Nat.pow_le_pow_right (by omega) hge))
    rw [h1, h2]

lemma firstUncov_spec {cov : Nat} (hlt : cov < 2 ^ 15) (hne : cov ≠ 32767) :
    firstUncov cov < 15 ∧ cov.testBit (firstUncov cov) = false := by
  unfold firstUncov
  rcases firstUncovAux_spec 15 cov 0 (fun _ hj => by omega) with ⟨h1, h2⟩ | ⟨_, h2⟩
  · simp only [Nat.zero_add] at h1
    exact ⟨h1, h2⟩
  · simp only [Nat.zero_add] at h2
    exact False.elim (hne (all_bits_15_eq hlt h2))

lemma remLb4_le_sdiff {blocks chosen : List M} {cov : Nat}
    (hcov : ∀ i : Fin 15, cov.testBit i.val = chosen.any (hit (cells.getD i.val (0, 0))))
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) :
    remLb4 cov ≤ (blocks.toFinset \ chosen.toFinset).card := by
  classical
  let U : Finset (Fin 4) := Finset.univ.filter (fun j : Fin 4 => !(cov.testBit j.val))
  have hU_card : U.card = remLb4 cov := by
    have heq : U.card = ∑ j : Fin 4, if !(cov.testBit j.val) then 1 else 0 := by
      rw [Finset.card_filter]
    rw [heq, Fin.sum_univ_four]
    have v0 : ((0 : Fin 4) : Nat) = 0 := rfl
    have v1 : ((1 : Fin 4) : Nat) = 1 := rfl
    have v2 : ((2 : Fin 4) : Nat) = 2 := rfl
    have v3 : ((3 : Fin 4) : Nat) = 3 := rfl
    rw [v0, v1, v2, v3]
    unfold remLb4
    cases cov.testBit 0 <;> cases cov.testBit 1 <;> cases cov.testBit 2 <;> cases cov.testBit 3 <;> simp
  have hex : ∀ j : Fin 4,
      ∃ z : M, j ∈ U → z ∈ blocks.toFinset \ chosen.toFinset ∧ hit (cells.getD j.val (0, 0)) z = true := by
    intro j
    by_cases hj : j ∈ U
    · have hbit : cov.testBit j.val = false := by
        have hm := (Finset.mem_filter.mp hj).2
        simpa using hm
      have hc_mem : cells.getD j.val (0, 0) ∈ cells := by
        have hlt : j.val < cells.length := by have := j.isLt; simp [cells]; omega
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      obtain ⟨z, hzB, hhit⟩ := hcover _ hc_mem
      have hzNotC : z ∉ chosen := by
        intro hzC
        have hany : chosen.any (hit (cells.getD j.val (0, 0))) = true :=
          List.any_eq_true.mpr ⟨z, hzC, hhit⟩
        have hcv := hcov ⟨j.val, by omega⟩
        change cov.testBit j.val = chosen.any (hit (cells.getD j.val (0, 0))) at hcv
        rw [hbit, hany] at hcv
        cases hcv
      exact ⟨z, fun _ => ⟨Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hzB, by simpa using hzNotC⟩, hhit⟩⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose f hf using hex
  rw [← hU_card]
  exact Finset.card_le_card_of_injOn f
    (fun j hj => Finset.mem_coe.mpr (hf j (Finset.mem_coe.mp hj)).1)
    (fun j1 hj1 j2 hj2 heq => by
      have h1 := (hf j1 (Finset.mem_coe.mp hj1)).2
      have h2 := (hf j2 (Finset.mem_coe.mp hj2)).2
      rw [← heq] at h2
      exact disj4_spec (f j1) j1 j2 h1 h2)

lemma remLb_bound {blocks chosen : List M} {cov : Nat}
    (hnd : chosen.Nodup)
    (hsub : ∀ z ∈ chosen, z ∈ blocks)
    (hlt : cov < 2 ^ 15)
    (hcov : ∀ i : Fin 15, cov.testBit i.val = chosen.any (hit (cells.getD i.val (0, 0))))
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) :
    chosen.length + remLb cov ≤ blocks.length := by
  classical
  have hsubF : chosen.toFinset ⊆ blocks.toFinset := by
    intro z hz; exact List.mem_toFinset.mpr (hsub z (List.mem_toFinset.mp hz))
  have hcardC : chosen.toFinset.card = chosen.length := List.toFinset_card_of_nodup hnd
  have hcardB : blocks.toFinset.card ≤ blocks.length := List.toFinset_card_le blocks
  have hsplit : (blocks.toFinset \ chosen.toFinset).card + chosen.toFinset.card = blocks.toFinset.card :=
    Finset.card_sdiff_add_card_eq_card hsubF
  unfold remLb
  dsimp only
  cases hs : Nat.beq (remLb4 cov) 0
  · change chosen.length + remLb4 cov ≤ blocks.length
    have h4 := remLb4_le_sdiff hcov hcover
    omega
  · cases hc : Nat.beq cov 32767
    · change chosen.length + 1 ≤ blocks.length
      have hne : cov ≠ 32767 := nat_beq_false_ne hc
      obtain ⟨idx_lt, hbit⟩ := firstUncov_spec hlt hne
      let i15 : Fin 15 := ⟨firstUncov cov, idx_lt⟩
      have hc_mem : cells.getD i15.val (0, 0) ∈ cells := by
        have hltC : i15.val < cells.length := by simp [cells, i15, idx_lt]
        rw [List.getD_eq_getElem _ _ hltC]
        exact List.getElem_mem hltC
      obtain ⟨z, hzB, hhit⟩ := hcover _ hc_mem
      have hzNotC : z ∉ chosen := by
        intro hzC
        have hany : chosen.any (hit (cells.getD i15.val (0, 0))) = true :=
          List.any_eq_true.mpr ⟨z, hzC, hhit⟩
        have hcv := hcov i15
        change cov.testBit (firstUncov cov) = chosen.any (hit (cells.getD i15.val (0, 0))) at hcv
        rw [hbit, hany] at hcv
        cases hcv
      have hpos : 1 ≤ (blocks.toFinset \ chosen.toFinset).card :=
        Finset.card_pos.mpr ⟨z, Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hzB, by simpa using hzNotC⟩⟩
      omega
    · change chosen.length + 0 ≤ blocks.length
      omega

lemma fastSolve_ok {tail blocks : List M}
    (hrun : Builds seeds tail)
    (hbound : tail.length + blocks.length ≤ 9)
    (hattain : ∀ z ∈ blocks, key z ∈ seeds ∨ key z ∈ tail)
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) :
    ∀ (fuel : Nat) (chosen : List M) (cov : Nat) (wanted : List Nat),
      chosen.Nodup →
      (∀ z ∈ chosen, z ∈ blocks) →
      cov < 2 ^ 15 →
      (∀ i : Fin 15, cov.testBit i.val = chosen.any (hit (cells.getD i.val (0, 0)))) →
      wanted.Nodup →
      (∀ q ∈ wanted, seedsMask.testBit q = false ∧ q ∈ tail.map BitVec.toNat) →
      blocks.length ≤ fuel + chosen.length →
      fastSolve fuel chosen.length cov wanted = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro chosen cov wanted hndC hsubC hltC hcov hndW hwSpec henough
    have hrem := remLb_bound hndC hsubC hltC hcov hcover
    have hrem0 : remLb cov = 0 := by omega
    have hcov_eq : cov = 32767 := by
      by_contra hne
      unfold remLb at hrem0
      dsimp only at hrem0
      cases hs : Nat.beq (remLb4 cov) 0
      · rw [hs] at hrem0
        change remLb4 cov = 0 at hrem0
        exact nat_beq_false_ne hs hrem0
      · have hc : Nat.beq cov 32767 = false := nat_beq_false hne
        rw [hs, hc] at hrem0
        cases hrem0
    have hw_len : wanted.length ≤ tail.length := by
      have := need_len_le hndW (m := seedsMask) (tail := tail) (fun q hq => Or.inr (hwSpec q hq).2)
      have heq_f : wanted.filter (fun q => !(seedsMask.testBit q)) = wanted :=
        List.filter_eq_self.mpr (fun q hq => by simp [(hwSpec q hq).1])
      rwa [heq_f] at this
    have hwe : fastWeCan wanted (9 - chosen.length) seedsMask = true :=
      fastWeCan_ok hndW hrun seeds_spec (by omega) (fun q hq => Or.inr (hwSpec q hq).2)
    have hblt : Nat.blt 9 (chosen.length + wanted.length) = false :=
      nat_blt_false (by omega)
    simp [fastSolve, hblt, hcov_eq, hwe]
  | succ k ih =>
    intro chosen cov wanted hndC hsubC hltC hcov hndW hwSpec henough
    have hrem := remLb_bound hndC hsubC hltC hcov hcover
    have hw_len : wanted.length ≤ tail.length := by
      have := need_len_le hndW (m := seedsMask) (tail := tail) (fun q hq => Or.inr (hwSpec q hq).2)
      have heq_f : wanted.filter (fun q => !(seedsMask.testBit q)) = wanted :=
        List.filter_eq_self.mpr (fun q hq => by simp [(hwSpec q hq).1])
      rwa [heq_f] at this
    have hblt : Nat.blt 9 (chosen.length + remLb cov + wanted.length) = false :=
      nat_blt_false (by omega)
    rw [fastSolve, hblt]
    simp only [Bool.cond_false]
    by_cases hcov_eq : cov = 32767
    · subst hcov_eq
      simp only [Nat.beq_refl, Bool.cond_true]
      exact fastWeCan_ok hndW hrun seeds_spec (by omega) (fun q hq => Or.inr (hwSpec q hq).2)
    · have hc : Nat.beq cov 32767 = false := nat_beq_false hcov_eq
      rw [hc]
      simp only [Bool.cond_false]
      obtain ⟨idx_lt, hbit⟩ := firstUncov_spec hltC hcov_eq
      let i15 : Fin 15 := ⟨firstUncov cov, idx_lt⟩
      have hc_mem : cells.getD i15.val (0, 0) ∈ cells := by
        have hltL : i15.val < cells.length := by simp [cells, i15, idx_lt]
        rw [List.getD_eq_getElem _ _ hltL]
        exact List.getElem_mem hltL
      obtain ⟨z, hzB, hhit⟩ := hcover _ hc_mem
      have hzNotC : z ∉ chosen := by
        intro hzC
        have hany : chosen.any (hit (cells.getD i15.val (0, 0))) = true :=
          List.any_eq_true.mpr ⟨z, hzC, hhit⟩
        have hcv := hcov i15
        change cov.testBit (firstUncov cov) = chosen.any (hit (cells.getD i15.val (0, 0))) at hcv
        rw [hbit, hany] at hcv
        cases hcv
      apply List.any_eq_true.mpr
      refine ⟨z.toNat, optsNat_spec i15 z hhit, ?_⟩
      let kz := kNat z.toNat
      have hkz_eq : (key z).toNat = kz := (key_spec z).1
      let w2 := bif seedsMask.testBit kz || wanted.contains kz then wanted else kz :: wanted
      have hw2_nd : w2.Nodup := by
        dsimp only [w2]
        cases hb : (seedsMask.testBit kz || wanted.contains kz)
        · simp only [Bool.cond_false]
          have hnotW : kz ∉ wanted := by
            intro hm
            have hc1 : wanted.contains kz = true := List.contains_iff_mem.mpr hm
            rw [hc1, Bool.or_true] at hb
            cases hb
          exact List.nodup_cons.mpr ⟨hnotW, hndW⟩
        · simp only [Bool.cond_true]; exact hndW
      have hw2_spec : ∀ q ∈ w2, seedsMask.testBit q = false ∧ q ∈ tail.map BitVec.toNat := by
        dsimp only [w2]
        cases hb : (seedsMask.testBit kz || wanted.contains kz)
        · simp only [Bool.cond_false, List.mem_cons]
          have hsF : seedsMask.testBit kz = false := by
            cases h1 : seedsMask.testBit kz
            · rfl
            · rw [h1, Bool.true_or] at hb; cases hb
          have hinT : kz ∈ tail.map BitVec.toNat := by
            rcases hattain z hzB with hseed | htail
            · have hsT := (seeds_spec (key z) hseed).2
              rw [hkz_eq, hsF] at hsT; cases hsT
            · rw [← hkz_eq]
              exact List.mem_map_of_mem htail
          rintro q (rfl | hq)
          · exact ⟨hsF, hinT⟩
          · exact hwSpec q hq
        · simp only [Bool.cond_true]; exact hwSpec
      have hcov2_lt : Nat.lor cov (covMaskOf z.toNat) < 2 ^ 15 := by
        rw [Nat.lor_eq]
        exact Nat.or_lt_two_pow hltC (covMaskOf_lt z)
      have hcov2_spec : ∀ i : Fin 15,
          (Nat.lor cov (covMaskOf z.toNat)).testBit i.val =
            (z :: chosen).any (hit (cells.getD i.val (0, 0))) := by
        intro i
        rw [Nat.lor_eq, Nat.testBit_or, hcov i, covMaskOf_spec z i, List.any_cons, Bool.or_comm]
      have hrec := ih (z :: chosen) (Nat.lor cov (covMaskOf z.toNat)) w2
        (List.nodup_cons.mpr ⟨hzNotC, hndC⟩)
        (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hzB) (hsubC x))
        hcov2_lt hcov2_spec hw2_nd hw2_spec (by simp; omega)
      simpa only [List.length_cons] using hrec

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
lemma fastSolve_checked : fastSolve 9 0 0 [] = false := by decide +kernel

theorem no_cover_build (tail blocks : List M)
    (hrun : Builds seeds tail)
    (hbound : tail.length + blocks.length ≤ 9)
    (hattain : ∀ z ∈ blocks, key z ∈ seeds ∨ key z ∈ tail)
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) : False := by
  have h0lt : (0 : Nat) < 2 ^ 15 := by decide
  have h1 : fastSolve 9 ([] : List M).length 0 [] = true :=
    fastSolve_ok hrun hbound hattain hcover 9 [] 0 []
      List.nodup_nil (fun _ h => by cases h) h0lt
      (fun _ => by simp) List.nodup_nil (fun _ h => by cases h) (by simp; omega)
  exact Bool.false_ne_true (fastSolve_checked.symm.trans h1)

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
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [i.isLt]
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
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · refine ⟨fun t _ r => ?_,fun _ => ?_,fun hn => (hn nz).elim,fun hn => (hn nz).elim,
      fun t ht => False.elim (by rw [nz] at ht; simp at ht)⟩
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
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
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
set_option maxHeartbeats 4000000 in
lemma fixture_delta : ∀ h t i, (inp h i 7 (pick t)).toNat = if i = term h t then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
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
set_option maxHeartbeats 4000000 in
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
  simp only [sense, vl_gate gs clean _ _ g hg, op, args, List.map_cons, List.map_nil, GateOp.eval]
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
  simp only [zero, beq_self_eq_true]
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
    (safe : AllSafe l (aim h)) : False := by
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
  exact CoverCheck.no_cover_build ps bs build (by omega)
    (fun z hz => by simpa [List.mem_append, or_comm] using outputs z hz)
    (output_cover safe)

end Probes

theorem binaryFloor (C : PEqualNP.CircuitLowerBounds.Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = petersenF x) :
    14 ≤ CircuitProof.nonNotCount C.gates := by
  by_contra! small
  obtain ⟨gs,o,L,budget⟩ := CircuitProof.Readers.least_with_budget C hf computes petersen_nonconstant
  have bound : CircuitProof.nonNotCount gs ≤ 13 := by omega
  obtain ⟨s,hs,once⟩ := terminal_class L bound
  obtain ⟨h,hh⟩ := Probes.layout_exists s hs
  obtain ⟨l,valid,safe⟩ := Probes.ledger_for_circuit L h (fun t => once _ (hh t))
  exact Probes.no_ledger bound valid safe

def petersenRhs (x12 : Fin 9 → Bool) : Bool :=
  (x12 0 && x12 1 || x12 1 && x12 2 || x12 2 && x12 3 || x12 3 && x12 4 ||
   x12 4 && x12 0 || x12 0 && x12 5 || x12 1 && x12 6 || x12 2 && x12 7 ||
   x12 3 && x12 8 || x12 5 && x12 7 || x12 6 && x12 8 || x12 8 && x12 5)

def remap (w : ℕ) : ℕ :=
  if w = 0 then 9 else if w < 9 then w else w + 1

def remapGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map remap⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp

lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append w [b] false i hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma remap_init (x : Fin 9 → Bool) (w : ℕ) :
    (List.ofFn x ++ [!x 0]).getD (remap w) false =
      (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i).getD w false := by
  unfold remap
  by_cases hw0 : w = 0
  · subst hw0
    simp only [↓reduceIte]
    have h1 := getD_snoc_self (List.ofFn x) (!x 0)
    rw [List.length_ofFn] at h1
    rw [h1]
    simp
  · rw [ite_eq_right hw0]
    by_cases hw9 : w < 9
    · rw [ite_eq_left hw9]
      rw [List.getD_append _ _ _ _ (by simp [hw9])]
      rw [List.getD_eq_getElem _ _ (by simp [hw9]), List.getD_eq_getElem _ _ (by simp [hw9])]
      simp only [List.getElem_ofFn]
      have hne : (⟨w, hw9⟩ : Fin 9) ≠ 0 := fun e => hw0 (congrArg Fin.val e)
      simp [hne]
    · rw [ite_eq_right hw9]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma remap_foldl (gs : List Gate) :
    ∀ (k : ℕ) (wD wC : List Bool),
      wD.length = 10 + k →
      wC.length = 9 + k →
      (∀ w : ℕ, wD.getD (remap w) false = wC.getD w false) →
      ∀ w : ℕ,
        ((gs.map remapGate).foldl stepW wD).getD (remap w) false =
          (gs.foldl stepW wC).getD w false := by
  induction gs with
  | nil => intro k wD wC _ _ hrel w; exact hrel w
  | cons g gs ih =>
    intro k wD wC hlD hlC hrel w
    simp only [List.map_cons, List.foldl_cons]
    have hev : (remapGate g).op.eval ((remapGate g).inputs.map fun i => wD.getD i false) =
        g.op.eval (g.inputs.map fun i => wC.getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => hrel i
    let v := g.op.eval (g.inputs.map fun i => wC.getD i false)
    have hsD : stepW wD (remapGate g) = wD ++ [v] := by
      unfold stepW
      rw [hev]
    have hsC : stepW wC g = wC ++ [v] := rfl
    rw [hsD, hsC]
    apply ih (k + 1) (wD ++ [v]) (wC ++ [v]) (by simp [hlD]; omega) (by simp [hlC]; omega)
    intro u
    by_cases hu : u = 9 + k
    · subst hu
      have hr : remap (9 + k) = 10 + k := by
        unfold remap
        split_ifs <;> omega
      rw [hr, ← hlD, getD_snoc_self, ← hlC, getD_snoc_self]
    · have hr_ne : remap u ≠ wD.length := by
        unfold remap
        split_ifs <;> omega
      rw [getD_snoc_ne _ _ _ hr_ne, getD_snoc_ne _ _ _ (by omega)]
      exact hrel u

lemma mono_eval_gate (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hop with h | h <;> rw [h]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hall x hx
    exact hle x (hall x hx)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨x, hx, h1⟩
    exact ⟨x, hx, hle x h1⟩

lemma mono_foldl (gs : List Gate) (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl stepW w1).getD i false = true → (gs.foldl stepW w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ hle i; exact hle i
  | cons g gs ih =>
    intro w1 w2 hlen hle i
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')) (stepW w1 g) (stepW w2 g)
      (by simp [stepW, hlen])
    intro j hj
    by_cases heq : j = w1.length
    · subst heq
      simp only [stepW, getD_snoc_self] at hj
      simp only [stepW, hlen, getD_snoc_self]
      exact mono_eval_gate g (hmono g List.mem_cons_self) w1 w2 hle hj
    · simp only [stepW, getD_snoc_ne _ _ _ heq] at hj
      simp only [stepW, getD_snoc_ne _ _ _ (by omega : j ≠ w2.length)]
      exact hle j hj

lemma nonNotCount_remap (gs : List Gate) :
    CircuitProof.nonNotCount (gs.map remapGate) = CircuitProof.nonNotCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [CircuitProof.nonNotCount, List.map_cons, List.countP_cons, remapGate] at ih ⊢
    rw [ih]

theorem prove_3831_from_floor
    (floor : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = petersenRhs x) →
      14 ≤ CircuitProof.nonNotCount C.gates) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) := by
  intro x1 _ _ hfan hsize _ _ _ _ _ _
  by_contra hall
  have heq : ∀ x : Fin 9 → Bool,
      circuitFun 9 x1 (fun i : Fin 9 => if i = 0 then !x 0 else x i) = petersenRhs x := by
    intro x
    by_contra hne
    exact hall ⟨x, hne⟩
  let g0 : Gate := ⟨GateOp.not, [0]⟩
  let D : Circuit := ⟨g0 :: x1.gates.map remapGate, remap x1.output⟩
  have hD_fan : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hmap
    · exact ⟨by simp [g0], by simp [g0]⟩
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hmap
      obtain ⟨hop, hlen⟩ := hfan g' hg'
      exact ⟨hop, by simpa [remapGate] using hlen⟩
  have hD_eval : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = petersenRhs x := by
    intro x
    have hg0 : stepW (List.ofFn x) g0 = List.ofFn x ++ [!x 0] := by
      simp [stepW, g0, GateOp.eval]
    change ((x1.gates.map remapGate).foldl stepW (stepW (List.ofFn x) g0)).getD (remap x1.output) false = petersenRhs x
    rw [hg0, remap_foldl x1.gates 0 (List.ofFn x ++ [!x 0])
      (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)
      (by simp) (by simp) (remap_init x) x1.output]
    exact heq x
  have h14 : 14 ≤ CircuitProof.nonNotCount D.gates := floor D hD_fan hD_eval
  have hD_cnt : CircuitProof.nonNotCount D.gates = CircuitProof.nonNotCount x1.gates := by
    have hcons : CircuitProof.nonNotCount (g0 :: x1.gates.map remapGate) = CircuitProof.nonNotCount (x1.gates.map remapGate) := by
      simp [CircuitProof.nonNotCount, g0, CircuitProof.isNotGate]
    exact hcons.trans (nonNotCount_remap x1.gates)
  rw [hD_cnt] at h14
  have hlen14 : x1.gates.length ≤ 14 := hsize
  have hall_nonNot : ∀ g ∈ x1.gates, (!CircuitProof.isNotGate g.op) = true := by
    have hcp : x1.gates.countP (fun g => !CircuitProof.isNotGate g.op) = x1.gates.length := by
      have hle := List.countP_le_length (p := fun g : Gate => !CircuitProof.isNotGate g.op) (l := x1.gates)
      unfold CircuitProof.nonNotCount at h14
      omega
    exact List.countP_eq_length.mp hcp
  have hmono : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have hop := (hfan g hg).1
    have hnn := hall_nonNot g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hnn; simp [CircuitProof.isNotGate] at hnn
  let xHi : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
  let xLo : Fin 9 → Bool := fun i => decide (i = 1)
  let w1 := List.ofFn (fun i : Fin 9 => if i = 0 then !xHi 0 else xHi i)
  let w2 := List.ofFn (fun i : Fin 9 => if i = 0 then !xLo 0 else xLo i)
  have hw_le : ∀ i, w1.getD i false = true → w2.getD i false = true := by
    intro i hi
    by_cases hlt : i < 9
    · have e1 : w1.getD i false = (if (⟨i, hlt⟩ : Fin 9) = 0 then !xHi 0 else xHi ⟨i, hlt⟩) := by
        rw [List.getD_eq_getElem _ _ (by simp [w1, hlt]), List.getElem_ofFn]
      have e2 : w2.getD i false = (if (⟨i, hlt⟩ : Fin 9) = 0 then !xLo 0 else xLo ⟨i, hlt⟩) := by
        rw [List.getD_eq_getElem _ _ (by simp [w2, hlt]), List.getElem_ofFn]
      rw [e1] at hi
      rw [e2]
      revert hi
      have hfin : ∀ j : Fin 9,
          (if j = 0 then !xHi 0 else xHi j) = true →
          (if j = 0 then !xLo 0 else xLo j) = true := by decide
      exact hfin ⟨i, hlt⟩
    · rw [List.getD_eq_default _ _ (by simp [w1]; omega)] at hi
      cases hi
  have hev1 : (x1.gates.foldl stepW w1).getD x1.output false = true := by
    have h1 := heq xHi
    have hrhs1 : petersenRhs xHi = true := by decide
    rw [hrhs1] at h1
    exact h1
  have hev2 : (x1.gates.foldl stepW w2).getD x1.output false = true :=
    mono_foldl x1.gates hmono w1 w2 (by simp [w1, w2]) hw_le x1.output hev1
  have h2 := heq xLo
  have hrhs2 : petersenRhs xLo = false := by decide
  rw [hrhs2] at h2
  change (x1.gates.foldl stepW w2).getD x1.output false = false at h2
  rw [hev2] at h2
  cases h2


lemma petersenF_eq_rhs (x : Fin 9 → Bool) : petersenF x = petersenRhs x := by
  simp only [petersenF, PetersenNine.edgeFun, PetersenNine.edges, petersenRhs,
    List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem main_3831 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) :=
  prove_3831_from_floor fun C hfan hev =>
    binaryFloor C hfan fun x => (hev x).trans (petersenF_eq_rhs x).symm

end PEqualNP.Outside.L_meta_3831

theorem PEqualNP.Outside.L_meta_3831 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3831.main_3831
