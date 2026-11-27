import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18791_aux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1549_aux

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

def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)

def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed ∧ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed ∧ neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅

def closeIsolates (removed : Finset V) : Finset V := removed ∪ isolates G removed

def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)

lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root := by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty := by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root) := by
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu

lemma dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V, A ∪ Q ⊆ removeClass G B root := by
  classical
  by_cases someActive : ∃ root ∈ Q, root ∉ B ∧ (neighborsAfter G B root).Nonempty
  · obtain ⟨root, rootQ, rootOut, rootLive⟩ := someActive
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU := live.mono (neighborsAfter_subset G smaller u)
      have oldRoot := rootLive.mono (neighborsAfter_subset G smaller root)
      have same := neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root := by simp [maximalClass, rootOut, rootLive, uIn, same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V := Classical.choice inferInstance
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u, hu, uIn, live⟩)

lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty := by
  have uOut : u ∉ removed := fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty := by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v, hv⟩ := old
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨v, ?_⟩
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hv.1, fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v := by
      simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv.1.symm, uOut⟩
    have none : neighborsAfter G removed v = ∅ := by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness

lemma closeIsolates_idempotent (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed := by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live := retained_after_close G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅ := by
      simpa [isolates] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left

def TwinSteps : Finset V → List (Finset V) → Prop
  | _, [] => True
  | removed, group :: rest => TwinGroup G removed group ∧ TwinSteps (removed ∪ group) rest

def removedThrough : Finset V → List (Finset V) → Finset V
  | removed, [] => removed
  | removed, group :: rest => removedThrough (removed ∪ group) rest

def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0, start, finish => finish = start
  | k + 1, start, finish => ∃ root : V, ClassSteps k (removeClass G start root) finish

lemma dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V, ClassSteps G groups.length B finish ∧ removedThrough A groups ⊆ finish := by
  induction groups generalizing A B with
  | nil => exact ⟨B, rfl, smaller⟩
  | cons group rest ih =>
    obtain ⟨twins, next⟩ := steps
    obtain ⟨root, subset⟩ := dominates_step G smaller twins
    obtain ⟨finish, walk, covered⟩ := ih subset next
    exact ⟨finish, ⟨root, walk⟩, covered⟩

def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v, u ∉ removed → v ∉ removed → ¬ G.Adj u v

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B := by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))

lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ := by
  ext u
  simp only [Finset.mem_univ, iff_true]
  by_contra out
  obtain ⟨v, hv⟩ := retained_after_close G out
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact noEdges u v out hv.2 hv.1

lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V, start = closeIsolates G D) : ∃ D : Finset V, finish = closeIsolates G D := by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root, after⟩ := walk
    exact ih after ⟨_, rfl⟩

lemma covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ := by
  obtain ⟨D, steps, subset⟩ := dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges := edgeless_mono G subset finished
  obtain ⟨A, hD⟩ := classSteps_finish_closed G steps ⟨∅, rfl⟩
  rw [hD] at noEdges
  rwa [hD, closed_edgeless_all G noEdges] at steps

end FiniteGraph

end BranchGraph

namespace BranchGroupsLean

open BranchGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}

def bucket (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v = r)

def below (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v < r)

def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)

omit [DecidableEq V] in
@[local simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅ := by
  ext v
  simp [coveredBy]

lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r := by
  ext v
  simp [coveredBy, bucket, List.mem_append]

omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V, label v = out ∨ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r := by
  have facts := List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy, below, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after := (List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots, r < out)
    (twinAt : ∀ r ∈ roots, TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)) := by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots := complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev := covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next := ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_, ?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next

lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending) := by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton, ih]
    simp [List.append_assoc]

omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))) := by
  rw [← coveredBy_nil label, removedThrough_coveredBy, List.nil_append]
  intro u v uNot vNot
  have hu : label u = out := (allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out := (allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket, hu]) v (by simp [bucket, hv])

lemma roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches, r < out)
    (twinAt : ∀ r ∈ branches, TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V), TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card := by
  let roots := branches.sort
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out ∨ label v ∈ roots := by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out := beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)) := by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last := no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last

end Graph

end BranchGroupsLean

namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

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

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

lemma dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

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

abbrev Stat := Bool ⊕ Nat
abbrev Stat.const : Bool → Stat := Sum.inl
abbrev Stat.wire : Nat → Stat := Sum.inr

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Sum.inl c :: _ => (none, Stat.const (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Sum.inl c] => (none, Stat.const c)
  | [Sum.inr j] => (none, Stat.wire j)
  | [Sum.inl c, Sum.inl d] => (none, Stat.const (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Sum.inl c] => (none, Stat.const c)
  | [Sum.inr j] => (none, Stat.wire j)
  | [Sum.inl c, Sum.inl d] => (none, Stat.const (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

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
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
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
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
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
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
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

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

lemma simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

lemma elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

lemma suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

lemma length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
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

lemma two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

lemma gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

lemma CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
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

lemma CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
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

lemma clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

lemma simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
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

lemma toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

lemma clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
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

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

lemma inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

lemma getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

lemma statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

lemma statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

lemma statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

lemma inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

lemma stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
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

lemma elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

lemma elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

lemma const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

lemma elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

lemma agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
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

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

lemma vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

lemma vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
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

lemma vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

lemma agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

lemma gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

lemma two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

lemma drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
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
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
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
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

lemma drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
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

lemma drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

lemma inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

lemma st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

lemma st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

lemma st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

lemma simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

lemma st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

lemma const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

end PEqualNP.MetaComplexity.Helpers

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Helpers

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

lemma difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
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

lemma cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
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

lemma unary_factor {A : Type} (w f : A → Bool)
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

lemma read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private lemma gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
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

lemma circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
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

lemma circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
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

namespace PEqualNP.MetaComplexity.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

lemma snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

lemma gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

lemma one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.MetaComplexity.Helpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.MetaComplexity.Helpers.Forest

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length

lemma Least.hcl {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : CleanL m gs := L.1

lemma Least.hev {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : ∀ x : Fin m → Bool, vl gs x o = f x := L.2.1

lemma Least.hmin {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length := L.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

lemma dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

lemma Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

lemma has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

lemma reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

lemma reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

lemma vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

lemma vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

lemma exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

lemma drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
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
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

lemma Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

lemma Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

lemma Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

lemma Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

lemma Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
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

lemma upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

lemma restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

lemma save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | inr j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section LocalSection2

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.MetaComplexity.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

lemma Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

lemma Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

lemma Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

lemma rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

lemma rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

lemma Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

lemma Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end LocalSection2

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

lemma gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end LocalSection1

section LocalSection2

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

lemma Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

lemma Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

lemma Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

lemma Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end LocalSection2

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

lemma lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp

lemma set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

lemma set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

lemma set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section LocalSection1

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

lemma Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h

lemma Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩

lemma Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩

  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩

  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw

  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk

  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end LocalSection1

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

lemma fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf

lemma fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Helpers.Forest

lemma pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
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


end PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.RunAsm

lemma least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
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

lemma least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]

lemma least_wire_readers_in_range {n out : Nat} {gs : List Gate}
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
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers

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

lemma predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

lemma predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

lemma predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

lemma predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
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

lemma predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact PEqualNP.Outside.L_meta_1549_aux.least_gate_inputs_nodup least nonnull _
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

private lemma eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
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

private lemma absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private lemma absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private lemma changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private lemma changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private lemma constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private lemma neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private lemma bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private lemma combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
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

private lemma stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
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

lemma fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
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

private lemma edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩

private lemma edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
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

private lemma edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
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

private lemma edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
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

lemma adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
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
open PEqualNP.MetaComplexity.Helpers
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

lemma negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
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

lemma negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
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

lemma wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private lemma wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private lemma wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private lemma wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

lemma wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
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

lemma wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

lemma wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

lemma wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
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
open PEqualNP.MetaComplexity.Helpers
open PetersenCutFormula PetersenCutTrace PetersenScratch

lemma wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
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

lemma cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

lemma adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
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
lemma exists_boundary (v : Fin m) :
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
lemma boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
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

lemma first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

lemma first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

lemma first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

lemma first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
lemma path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

lemma first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

lemma read_before {v w : Fin m} (route : ReflTransGen reads v w)
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

lemma ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

lemma edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
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

lemma avoiding_stays_before {v w : Fin m}
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

lemma no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
lemma unique_follow_predecessor {source a b goal : Fin m}
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

lemma unique_predecessor_before {source a b goal : Fin m}
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
lemma weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
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
lemma weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
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
open PEqualNP.MetaComplexity.Helpers
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

lemma mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

lemma wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
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

lemma firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
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

lemma firstInputGroup_controlled {n : Nat} {gs : List Gate}
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

lemma firstInputGroup_independent {n : Nat} {gs : List Gate}
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


namespace PetersenGroupBFS

abbrev MaskGraph := Nat × (Nat → Nat)

abbrev MaskGraph.width (g : MaskGraph) : Nat := g.1
abbrev MaskGraph.adjacency (g : MaskGraph) : Nat → Nat := g.2

def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex

def fullMask (g : MaskGraph) : Nat :=
  bit g.width - 1

def residualNeighbors (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (fullMask g) deleted)

def closeIsolates (g : MaskGraph) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if residualNeighbors g deleted v = 0 then Nat.lor mask (bit v) else mask)
    deleted

def twinClass (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (residualNeighbors g deleted v == residualNeighbors g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0

lemma bit_at (v w : Nat) : (bit v).testBit w = decide (v = w) := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma full_at (g : MaskGraph) (w : Nat) :
    (fullMask g).testBit w = decide (w < g.width) := by
  simp [fullMask, bit, Nat.shiftLeft_eq]

lemma neighbor_at (g : MaskGraph) (deleted v w : Nat) (hw : w < g.width) :
    (residualNeighbors g deleted v).testBit w =
      ((g.adjacency v).testBit w && !(deleted.testBit w)) := by
  simp [residualNeighbors, Nat.testBit_xor, full_at, hw]

private lemma fold_mask_at (vertices : List Nat) (p : Nat → Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w || (vertices.any fun v => decide (p v) && (v == w))) := by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h, bit_at, Bool.or_assoc, Bool.beq_eq_decide_eq]

private lemma any_mask_at (p : Nat → Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v) && (v == w)) =
      (decide (w < n) && decide (p w)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.and_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨v, hv, hp, rfl⟩
    exact ⟨hv, hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨w, hw, hp, rfl⟩

lemma close_at (g : MaskGraph) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w || (decide (w < g.width) && decide (residualNeighbors g deleted w = 0))) := by
  unfold closeIsolates
  rw [fold_mask_at, any_mask_at]

lemma class_at (g : MaskGraph) (deleted v w : Nat) :
    (twinClass g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w) && (residualNeighbors g deleted w == residualNeighbors g deleted v))) := by
  unfold twinClass
  rw [fold_mask_at, any_mask_at]
  simp [Bool.beq_eq_decide_eq]

lemma bit_eq_power (width : Nat) : bit width = 2 ^ width := by
  simp [bit, Nat.shiftLeft_eq]

lemma lor_bounded {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width := by
  rw [bit_eq_power] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb

lemma high_false {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false := by
  rw [bit_eq_power] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))

lemma mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width, a.testBit w = b.testBit w) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [high_false ha (Nat.le_of_not_gt hw), high_false hb (Nat.le_of_not_gt hw)]

lemma neighbor_bounded (g : MaskGraph) (deleted v : Nat) (hd : deleted < bit g.width) :
    residualNeighbors g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [residualNeighbors, full_at, Nat.not_lt_of_ge hw, high_false hd hw]

lemma close_bounded (g : MaskGraph) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at, Nat.not_lt_of_ge hw, high_false hd hw]

lemma class_bounded (g : MaskGraph) (deleted v : Nat) :
    twinClass g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at, Nat.not_lt_of_ge hw]

def step (g : MaskGraph) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v) && (residualNeighbors g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (twinClass g deleted v)))
    else none

def frontier (g : MaskGraph) : Nat → List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((frontier g depth).flatMap (step g)).eraseDups

lemma advance {g : MaskGraph} {depth deleted next : Nat}
    (hd : deleted ∈ frontier g depth) (hs : next ∈ step g deleted) :
    next ∈ frontier g (depth + 1) := by
  rw [frontier, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨deleted, hd, hs⟩

lemma stay {g : MaskGraph} {depth deleted : Nat} (hd : deleted ∈ frontier g depth) :
    deleted ∈ frontier g (depth + 1) :=
  advance hd (by simp [step])

lemma advance_class {g : MaskGraph} {depth deleted vertex : Nat}
    (hd : deleted ∈ frontier g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : residualNeighbors g deleted vertex ≠ 0) :
    closeIsolates g (Nat.lor deleted (twinClass g deleted vertex)) ∈ frontier g (depth + 1) := by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex, List.mem_range.mpr hv, ?_⟩
  simp [hlive, hne]


end PetersenGroupBFS

namespace PetersenMaskBridge

open PetersenGroupBFS
open BranchGraph

def decode (g : MaskGraph) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)

@[local simp] lemma mem_decode (g : MaskGraph) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask ↔ mask.testBit v.val = true := by
  simp [decode]

@[local simp] lemma decode_zero (g : MaskGraph) : decode g 0 = ∅ := by
  ext v
  simp

@[local simp] lemma decode_full (g : MaskGraph) : decode g (fullMask g) = Finset.univ := by
  ext v
  simp [full_at, v.isLt]

lemma decode_or (g : MaskGraph) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b := by
  ext v
  simp [Bool.or_eq_true]

lemma decode_inj (g : MaskGraph) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b := by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w, hw⟩ : Fin g.width) ∈ decode g a ↔ (⟨w, hw⟩ : Fin g.width) ∈ decode g b := by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm

lemma bit_pos (n : Nat) : 0 < bit n := by
  rw [bit_eq_power]
  exact Nat.two_pow_pos n

lemma full_bounded (g : MaskGraph) : fullMask g < bit g.width := by
  unfold fullMask
  have := bit_pos g.width
  omega

section Graph

variable (g : MaskGraph) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width, G.Adj u v ↔ (g.adjacency u.val).testBit v.val = true)

include adj in
lemma decode_neighbors (deleted : Nat) (u : Fin g.width) :
    decode g (residualNeighbors g deleted u.val) = neighborsAfter G (decode g deleted) u := by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode, neighborsAfter, neighbor_at g deleted u.val v.val v.isLt, adj, h]

include adj in
lemma residual_zero_iff (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    residualNeighbors g deleted u.val = 0 ↔ neighborsAfter G (decode g deleted) u = ∅ := by
  constructor
  · intro h
    rw [← decode_neighbors g G adj, h, decode_zero]
  · intro h
    apply decode_inj g (neighbor_bounded g deleted u.val bound) (bit_pos g.width)
    rw [decode_neighbors g G adj, h, decode_zero]

include adj in
lemma decode_close (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted) := by
  ext v
  simp [close_at, v.isLt, BranchGraph.closeIsolates, isolates, Bool.or_eq_true,
    residual_zero_iff g G adj deleted bound]

include adj in
lemma decode_class (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (twinClass g deleted root.val) = maximalClass G (decode g deleted) root := by
  have same (u : Fin g.width) : residualNeighbors g deleted u.val = residualNeighbors g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root := by
    rw [← decode_neighbors g G adj deleted u, ← decode_neighbors g G adj deleted root]
    exact ⟨congrArg (decode g), decode_inj g (neighbor_bounded g deleted u.val bound)
      (neighbor_bounded g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at, v.isLt, maximalClass, outside, live, h, same, Bool.beq_eq_decide_eq]

def Represented (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m, m ∈ frontier g depth ∧ m < bit g.width ∧ decode g m = removed

include adj in
lemma initial_rep : Represented g 0 (BranchGraph.closeIsolates G ∅) := by
  refine ⟨PetersenGroupBFS.closeIsolates g 0, ?_,
    close_bounded g 0 (bit_pos g.width), ?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [decode_close g G adj _ (bit_pos g.width), decode_zero]

include adj in
lemma advance_rep {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : Represented g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    Represented g (depth + 1) (removeClass G removed root) := by
  obtain ⟨m, hm, bounded, same⟩ := rep
  subst removed
  by_cases active : root ∉ decode g m ∧ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false := by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : residualNeighbors g m root.val ≠ 0 := by
      intro h
      have none := (residual_zero_iff g G adj m bounded root).mp h
      simpa [none] using active.2
    have united := lor_bounded bounded (class_bounded g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (twinClass g m root.val)),
      advance_class hm root.isLt live someNeighbor, close_bounded g _ united, ?_⟩
    rw [decode_close g G adj _ united, decode_or, decode_class g G adj m bounded root active.1 active.2,
      removeClass]
  · have sameRemoval : removeClass G (decode g m) root = decode g m := by
      have emptyClass : maximalClass G (decode g m) root = ∅ := ite_eq_right active
      simp only [removeClass, emptyClass, Finset.union_empty, closed]
    exact ⟨m, stay hm, bounded, sameRemoval.symm⟩

include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : ClassSteps G count start finish) (initial : Represented g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : Represented g (depth + count) finish := by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk, Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root, next⟩ := walk
    have nextClosed : BranchGraph.closeIsolates G (removeClass G start root) = removeClass G start root :=
      closeIsolates_idempotent G _
    have rest := ih next (advance_rep g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using rest

lemma frontier_up {m k r : Nat} (reached : m ∈ frontier g k) (budget : k ≤ r) : m ∈ frontier g r := by
  induction r with
  | zero =>
    have : k = 0 := by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))

include adj in
lemma groups_exceed_budget [Nonempty (Fin g.width)] (k : Nat) (noFinish : fullMask g ∉ frontier g k)
    (groups : List (Finset (Fin g.width))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : k < groups.length := by
  by_contra! budget
  have walk := covering_sequence_reaches_univ G groups twins finished
  obtain ⟨m, reached, bound, allGone⟩ :=
    simulate g G adj walk (initial_rep g G adj) (closeIsolates_idempotent G ∅)
  have equal : m = fullMask g := decode_inj g bound (full_bounded g) (by simpa using allGone)
  rw [equal, Nat.zero_add] at reached
  exact noFinish (frontier_up g reached budget)

end Graph


end PetersenMaskBridge


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers

section LocalSection1

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
  {gs : List Gate} {o : ℕ}




end LocalSection1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w


private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]


private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]







private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)



private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)








































open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers





open PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers

section LocalSection1

variable {m : ℕ} {gs : List Gate}





end LocalSection1


namespace EssentialInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.PermInputs

lemma dependent_input_read {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (least : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (dep : Dep f i)
    (nc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b)) :
    ∃ q, Reads gs q i := by
  by_contra none
  have noRead : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact none ⟨q, g, hq, hi⟩
  have outputDifferent : o ≠ i := by
    intro he
    obtain ⟨x, y, hxy⟩ := nc
    apply hxy
    rw [← least.hev, ← least.hev, he, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := dep
  apply hx
  rw [← least.hev, ← least.hev]
  refine agree_except i gs _ _ noRead (by simp) ?_ o outputDifferent
  intro j hj
  by_cases within : j < n + 1
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false =
          Function.update x i (!x i) ⟨j, within⟩ from getD_ofFn _ _ false ⟨j, within⟩,
        show (List.ofFn x).getD j false = x ⟨j, within⟩ from getD_ofFn _ x false ⟨j, within⟩]
    exact Function.update_of_ne (fun h => hj (congrArg Fin.val h)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma force_essential {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (i : Fin (n + 1)) (b : Bool) (dep : Dep f i)
    (nc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (circuit : HasCircuitSize (n + 1) f s) : Drop f i b 1 s := by
  have nonconstant : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := nc
    exact ⟨Function.update x i b, Function.update y i b, h⟩
  obtain ⟨gs, o, least, size⟩ := exists_least (n + 1) f s nonconstant circuit
  obtain ⟨r, read⟩ := dependent_input_read least i b dep nc
  obtain ⟨s', saved, hc⟩ := least.save i b nc {r} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input b read)
  exact ⟨s', (by simpa using saved : s' + 1 ≤ gs.length).trans size, hc⟩

lemma remove_free_or {n s : ℕ} {h : (Fin (n + 1) → Bool) → Bool} (i : Fin (n + 1))
    (independent : ∀ x, h (Function.update x i false) = h x)
    (nonconstant : ∃ x y, h x ≠ h y)
    (circuit : HasCircuitSize (n + 1) (fun x => x i || h x) s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize (n + 1) h s' := by
  let f : (Fin (n + 1) → Bool) → Bool := fun x => x i || h x
  have restriction (x : Fin (n + 1) → Bool) : f (Function.update x i false) = h x := by
    simp [f, independent]
  have dep : Dep f i := by
    have ⟨x, hx⟩ : ∃ x, h x = false := by
      obtain ⟨x, y, hxy⟩ := nonconstant
      cases hx : h x
      · exact ⟨x, hx⟩
      · exact ⟨y, by simpa [hx] using Ne.symm hxy⟩
    let z := Function.update x i false
    refine ⟨z, ?_⟩
    simp [f, z, independent, hx]
  have nc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false) := by
    simpa only [restriction] using nonconstant
  obtain ⟨s', size, hsize⟩ := force_essential i false dep nc circuit
  rw [show (fun x => f (Function.update x i false)) = h from funext restriction] at hsize
  exact ⟨s', size, hsize⟩

end EssentialInput

namespace ThetaC7Base

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs

def cycle7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def path6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)

def path4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def path4On6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def path4Plus5 (x : Fin 6 → Bool) : Bool := x 5 || path4On6 x

def path4WithTwo (x : Fin 6 → Bool) : Bool := x 4 || path4Plus5 x

def cyclicOffset (p i : Fin 7) : ℕ := (i.val + 7 - p.val) % 7

def projectFalse (p i : Fin 7) : Fin 6 := ⟨(cyclicOffset p i - 1) % 6, by omega⟩

def projectTrue (p i : Fin 7) : Fin 6 :=
  let k := cyclicOffset p i
  ⟨(if k = 1 then 4 else if k = 6 then 5 else k - 2) % 6, by omega⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
lemma falseProjection : ∀ (p : Fin 7) (x : Fin 6 → Bool),
    cycle7 (Function.update (x ∘ projectFalse p) p false) = path6 x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
lemma trueProjection : ∀ (p : Fin 7) (x : Fin 6 → Bool),
    cycle7 (Function.update (x ∘ projectTrue p) p true) = path4WithTwo x := by
  decide +kernel

def point (w i : Fin 7) : Bool := decide (i = w)

lemma dependence_check : ∀ p : Fin 7,
    cycle7 (Function.update (point (p + 1)) p (!(point (p + 1) p))) ≠
      cycle7 (point (p + 1)) := by decide +kernel

lemma restrict_nonconstant_check : ∀ (p : Fin 7) (b : Bool),
    cycle7 (Function.update (fun _ => false) p b) ≠
      cycle7 (Function.update (fun _ => true) p b) := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
lemma no_funnel_check : ∀ (p q : Fin 7), p ≠ q → ∀ a b : Bool, ∃ w : Fin 7,
    ¬(cycle7 (set2 (point w) p (!a) q b) = cycle7 (set2 (point w) p a q (!b)) ∧
      cycle7 (set2 (point w) p a q (!b)) = cycle7 (set2 (point w) p (!a) q (!b))) := by
  decide +kernel

lemma cyclic_restr_nonconstant : RestrNC cycle7 := by
  intro p _ b
  exact ⟨fun _ => false, fun _ => true, restrict_nonconstant_check p b⟩

lemma cyclic_no_funnel : NoFunnel cycle7 := by
  intro p q hne _ _ h
  obtain ⟨a, b, repeated⟩ := h
  obtain ⟨w, distinct⟩ := no_funnel_check p q hne a b
  exact distinct (repeated (point w))

def wrap4 (i : Fin 6) : Fin 4 := ⟨i.val % 4, by omega⟩

lemma path4_projection (y : Fin 4 → Bool) : path4On6 (y ∘ wrap4) = path4 y := by
  rfl

lemma ncAtPair (h : (Fin 6 → Bool) → Bool)
    (negative : h (fun _ => false) = false)
    (positive : h (fun i => decide (i.val ≤ 1)) = true) : ∃ x y, h x ≠ h y :=
  ⟨fun _ => false, fun i => decide (i.val ≤ 1), by simp [negative, positive]⟩

lemma cycle7_lower_from_paths
    (p6 : ∀ s, HasCircuitSize 6 path6 s → 7 ≤ s)
    (p4 : ∀ s, HasCircuitSize 4 path4 s → 4 ≤ s)
    (s : ℕ) (c : HasCircuitSize 7 cycle7 s) : 10 ≤ s := by
  have dep : ∃ p : Fin 7, Dep cycle7 p := ⟨0, point (0 + 1), dependence_check 0⟩
  rcases fanout_step_3_4 6 cycle7 s dep cyclic_restr_nonconstant cyclic_no_funnel c with
    ⟨p, t, drop, d⟩ | ⟨p, t, drop, d⟩
  · have smaller := relabel_size (projectFalse p) _ t d
    rw [funext (falseProjection p)] at smaller
    have := p6 t smaller
    omega
  · have smaller := relabel_size (projectTrue p) _ t d
    rw [funext (trueProjection p)] at smaller
    obtain ⟨t', drop', d'⟩ := EssentialInput.remove_free_or (h := path4Plus5) 4
      (fun y => by simp [path4Plus5, path4On6])
      (ncAtPair path4Plus5 (by decide) (by decide)) smaller
    obtain ⟨r, hr, c4⟩ := EssentialInput.remove_free_or (h := path4On6) 5
      (fun y => by simp [path4On6])
      (ncAtPair path4On6 (by decide) (by decide)) d'
    have smallerPath : HasCircuitSize 4 path4 r := by
      simpa only [path4_projection] using relabel_size wrap4 _ r c4
    have := p4 r smallerPath
    omega

end ThetaC7Base

namespace PEqualNP.MetaComplexity.Helpers.PadOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

lemma pad_down (n s : ℕ) (f : (Fin n → Bool) → Bool) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1)) : HasCircuitSize n f s := by
  obtain ⟨y, y', hyy⟩ := hnc
  set g : (Fin (n + 1) → Bool) → Bool :=
    fun x => x (Fin.last n) || f (fun i : Fin n => x i.castSucc) with hg
  have hupd : ∀ (x : Fin (n + 1) → Bool) (b : Bool),
      (fun i : Fin n => Function.update x (Fin.last n) b i.castSucc) = fun i => x i.castSucc := by
    intro x b; funext i
    exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
  have hres : ∀ x : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) false) = f (fun i : Fin n => x i.castSucc) := by
    intro x; simp only [hg]; rw [hupd]; simp
  have hsn : ∀ z : Fin n → Bool, ∀ b : Bool, (fun i : Fin n => (Fin.snoc z b : Fin (n + 1) → Bool) i.castSucc) = z := by
    intro z b; funext i; exact Fin.snoc_castSucc (α := fun _ => Bool) ..

  obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, f z = false := by
    cases h1 : f y
    · exact ⟨y, h1⟩
    · cases h2 : f y'
      · exact ⟨y', h2⟩
      · exact absurd (h1.trans h2.symm) hyy
  have hdep : ∃ x : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ g x := by
    refine ⟨Fin.snoc z false, ?_⟩
    simp only [hg, Function.update_self, Fin.snoc_last]
    rw [hupd, hsn, hz]; simp
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) false) ≠ g (Function.update x' (Fin.last n) false) := by
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    rw [hres, hres, hsn, hsn]; exact hyy
  have h1 := PEqualNP.MetaComplexity.Helpers.Forest.one_gate_at n g (Fin.last n) false s hdep hnc' h
  have h1' : HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc)) s := by
    have e : (fun x => g (Function.update x (Fin.last n) false))
        = (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc)) := by
      funext x; exact hres x
    rw [← e]; exact h1

  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd (congrArg f (Subsingleton.elim y y')) hyy
    | succ m => exact ⟨m, rfl⟩
  let π : Fin (m + 1 + 1) → Fin (m + 1) := Fin.lastCases 0 id
  have h2 := relabel_size π _ s h1'
  have e : (fun x : Fin (m + 1) → Bool => f (fun i : Fin (m + 1) => (x ∘ π) i.castSucc)) = f := by
    funext x; congr 1; funext i; simp [π, Fin.lastCases_castSucc]
  rw [e] at h2; exact h2

end PEqualNP.MetaComplexity.Helpers.PadOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def path3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)

def path4 (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def path5 (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)

def path6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)

private def path2WithFree (x : Fin 3 → Bool) : Bool := x 0 || (x 1 && x 2)

private def path4WithFree (x : Fin 5 → Bool) : Bool :=
  x (Fin.last 4) || path4 (fun i => x i.castSucc)

private lemma same_cost_relabel {m n s bound : ℕ} {f : (Fin m → Bool) → Bool}
    {g : (Fin n → Bool) → Bool} (rename : Fin m → Fin n)
    (eq : ∀ x, f (x ∘ rename) = g x)
    (lower : ∀ t, HasCircuitSize n g t → bound ≤ t)
    (circuit : HasCircuitSize m f s) : bound ≤ s := by
  apply lower s
  rw [← funext eq]
  exact relabel_size rename f s circuit

private abbrev PathDep {m : ℕ} (f : (Fin m → Bool) → Bool) (j : Fin m) :=
  ∃ x, f (Function.update x j (!x j)) ≠ f x

private abbrev PathCofactorNC {m : ℕ} (f : (Fin m → Bool) → Bool) (j : Fin m) :=
  ∀ b : Bool, ∃ x y, f (Function.update x j b) ≠ f (Function.update y j b)

private lemma two_equal_cofactors {n bound s : ℕ} (f : (Fin (n + 1) → Bool) → Bool)
    (j : Fin (n + 1)) (essential : PathDep f j) (nc : PathCofactorNC f j)
    (lower : ∀ b t, HasCircuitSize (n + 1) (fun x => f (Function.update x j b)) t → bound ≤ t)
    (circuit : HasCircuitSize (n + 1) f s) : bound + 2 ≤ s := by
  obtain ⟨b, t, count, cofactor⟩ := gate_elim_at n f j s essential nc circuit
  have := lower b t cofactor
  omega

lemma path3_lower (s : ℕ) (circuit : HasCircuitSize 3 path3 s) : 2 ≤ s := by
  have deps : ∀ j : Fin 3, PathDep path3 j := by unfold PathDep; decide +kernel
  have := dep_lower 3 path3 deps s circuit
  omega

private lemma path2_with_free_lower (s : ℕ) (circuit : HasCircuitSize 3 path2WithFree s) : 2 ≤ s := by
  have deps : ∀ j : Fin 3, PathDep path2WithFree j := by unfold PathDep; decide +kernel
  have := dep_lower 3 path2WithFree deps s circuit
  omega

lemma path4_lower (s : ℕ) (circuit : HasCircuitSize 4 path4 s) : 4 ≤ s := by
  have essential : PathDep path4 0 := ⟨fun j => decide (j = 1), by decide +kernel⟩
  have nc : PathCofactorNC path4 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ b t, HasCircuitSize 4 (fun x => path4 (Function.update x 0 b)) t → 2 ≤ t := by
    intro b
    cases b
    · exact fun s h => same_cost_relabel (![0, 0, 1, 2] : Fin 4 → Fin 3)
        (by decide +kernel) path3_lower h
    · exact fun s h => same_cost_relabel (![0, 0, 1, 2] : Fin 4 → Fin 3)
        (by decide +kernel) path2_with_free_lower h
  exact two_equal_cofactors path4 0 essential nc lower circuit

lemma path5_lower (s : ℕ) (circuit : HasCircuitSize 5 path5 s) : 5 ≤ s := by
  have essential : PathDep path5 0 := ⟨fun j => decide (j = 1), by decide +kernel⟩
  have nc : PathCofactorNC path5 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ t, HasCircuitSize 5 (fun x => path5 (Function.update x 0 false)) t → 4 ≤ t :=
    fun _ h => same_cost_relabel (![0, 0, 1, 2, 3] : Fin 5 → Fin 4)
      (by decide +kernel) path4_lower h
  have deps : ∀ j : Fin 5, PathDep path5 j := by unfold PathDep; decide +kernel
  have size := dep_lower 5 path5 deps s circuit
  have larger : HasCircuitSize 5 path5 ((s - 1) + 1) := by
    rwa [show s - 1 + 1 = s by omega]
  have smaller := PEqualNP.MetaComplexity.Helpers.Forest.one_gate_at 4 path5 0 false
    (s - 1) essential (nc false) larger
  have := lower (s - 1) smaller
  omega

private lemma path4_with_free_lower (s : ℕ) (circuit : HasCircuitSize 5 path4WithFree s) : 5 ≤ s := by
  have hne : ∃ x y : Fin 4 → Bool, path4 x ≠ path4 y :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  have relevant : ∀ j : Fin 5, PathDep path4WithFree j := by unfold PathDep; decide +kernel
  have size := dep_lower 5 path4WithFree relevant s circuit
  have larger : HasCircuitSize 5 path4WithFree ((s - 1) + 1) := by
    rwa [show s - 1 + 1 = s by omega]
  have small := PEqualNP.MetaComplexity.Helpers.PadOr.pad_down 4 (s - 1) path4 hne larger
  have := path4_lower (s - 1) small
  omega

lemma path6_lower (s : ℕ) (circuit : HasCircuitSize 6 path6 s) : 7 ≤ s := by
  have essential : PathDep path6 0 := ⟨fun j => decide (j = 1), by decide +kernel⟩
  have nc : PathCofactorNC path6 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ b t, HasCircuitSize 6 (fun x => path6 (Function.update x 0 b)) t → 5 ≤ t := by
    intro b
    cases b
    · exact fun s h => same_cost_relabel (![0, 0, 1, 2, 3, 4] : Fin 6 → Fin 5)
        (by decide +kernel) path5_lower h
    · exact fun s h => same_cost_relabel (![4, 4, 0, 1, 2, 3] : Fin 6 → Fin 5)
        (by decide +kernel) path4_with_free_lower h
  exact two_equal_cofactors path6 0 essential nc lower circuit


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

lemma operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

lemma two_readers_operand_count {gs : List Gate} {wire p q : Nat}
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

lemma operands_count_length (gs : List Gate)
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

lemma clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

lemma branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
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

lemma branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
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

lemma one_not_gate_positive {gs : List Gate} (notUsed : ∃ g ∈ gs, g.op = GateOp.not) :
    1 ≤ notGateCount gs := by
  obtain ⟨g, mem, tag⟩ := notUsed
  have kept : g ∈ gs.filter (fun q => isNotGate q.op) :=
    List.mem_filter.mpr ⟨mem, by simp [isNotGate, tag]⟩
  have pos := List.length_pos_of_mem kept
  exact pos

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace

lemma least_read_edge_live {n out : Nat} {gs : List Gate}
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

lemma branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
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

lemma in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

lemma class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]

lemma classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]

lemma class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open Relation

lemma agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
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
open PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

lemma finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace

lemma circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
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


end PEqualNP.Outside.L_meta_1549_aux

open PEqualNP.Outside.L_meta_1549_aux




lemma cycle7_lower_bound (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) : 10 ≤ C.size := by
  exact ThetaC7Base.cycle7_lower_from_paths path6_lower path4_lower C.size ⟨C, hf, le_rfl, he⟩

lemma cycle7_minimal (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    PEqualNP.MetaComplexity.IsMinimalCircuit 7 C := by
  refine ⟨hf, ?_⟩
  intro D hD hEq
  have hEvalD : ∀ x : Fin 7 → Bool,
      D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)) := by
    intro x
    exact (congrFun hEq x).trans (he x)
  have hl := cycle7_lower_bound D hD hEvalD
  omega



namespace HelperReview

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers

lemma idStats_getD (m j : ℕ) :
    (idStats m).getD j (Stat.const false) =
      if j < m then Stat.wire j else Stat.const false := by
  by_cases h : j < m <;> simp [idStats, List.getD_eq_getElem?_getD, h]

lemma idStats_snoc (m : ℕ) :
    idStats (m + 1) = idStats m ++ [Stat.wire m] := by
  simpa [idStats] using
    (List.ofFn_succ_last (f := fun i : Fin (m+1) => Stat.wire i))

lemma simplify_emitted_identity (m : ℕ) (g g' : Gate) (hg : Ok g)
    (he : (simplify g.op m
      (g.inputs.map fun i => (idStats m).getD i (Stat.const false))).1 = some g') :
    g' = normGate g ∧
      (simplify g.op m
        (g.inputs.map fun i => (idStats m).getD i (Stat.const false))).2 = Stat.wire m := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only [idStats_getD] at he ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [simplify, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpAnd, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpOr, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpNot] at he
  · rcases hop with rfl | rfl | rfl <;>
      by_cases ha : a < m <;>
      simp_all [simplify, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpAnd, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpOr, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpNot, normGate]
  · rcases hop with rfl | rfl | rfl <;>
      by_cases ha : a < m <;> by_cases hb : b < m <;>
      simp_all [simplify, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpAnd, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpOr, PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.simpNot, normGate]
  · simp at hlen

lemma elim_identity_of_full_length (n : ℕ) (gs : List Gate) :
    ∀ pre : List Gate, (∀ g ∈ gs, Ok g) →
      (elim n gs (idStats (n + pre.length), pre)).2.length = pre.length + gs.length →
      (elim n gs (idStats (n + pre.length), pre)).2 = pre ++ gs.map normGate := by
  induction gs with
  | nil => intro pre _ _; simp [elim]
  | cons g gs ih =>
    intro pre hok hlen
    have hg : Ok g := hok g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, Ok g' := fun g' h => hok g' (List.mem_cons_of_mem _ h)
    cases hs : (simplify g.op (n + pre.length)
        (g.inputs.map fun i => (idStats (n + pre.length)).getD i (Stat.const false))).1 with
    | none =>
      have hb := elim_len n gs (PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.elimStep n (idStats (n + pre.length), pre) g)
      have hb' : (elim n gs (PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.elimStep n (idStats (n + pre.length), pre) g)).2.length ≤
          pre.length + gs.length := by
        simpa only [PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.elimStep, hs, Option.toList_none, List.append_nil] using hb
      rw [elim_cons] at hlen
      simp only [List.length_cons] at hlen
      omega
    | some g' =>
      obtain ⟨he, hv⟩ := simplify_emitted_identity (n + pre.length) g g' hg hs
      have hstep : PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.elimStep n (idStats (n + pre.length), pre) g =
          (idStats (n + (pre ++ [normGate g]).length), pre ++ [normGate g]) := by
        simp only [PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.elimStep, hs, hv, he, Option.toList_some]
        congr 1
        simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using
          (idStats_snoc (n + pre.length)).symm
      have hlen' : (elim n gs
          (idStats (n + (pre ++ [normGate g]).length), pre ++ [normGate g])).2.length =
          (pre ++ [normGate g]).length + gs.length := by
        simpa only [elim_cons, hstep, List.length_cons, List.length_append,
          List.length_singleton, List.length_nil, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hlen
      rw [elim_cons, hstep, ih _ hgs hlen']
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

lemma normalized_clean_of_minimal (n : ℕ) (C : Circuit)
    (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) :
    CleanL n (C.gates.map normGate) := by
  let acc := elim n C.gates (idStats n, [])
  have hinv : ∀ x : Fin n → Bool,
      PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Inv n (List.ofFn x) (PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.wiresFrom C.gates (List.ofFn x)) acc :=
    fun x => inv_elim n _ (by simp) C.gates _ _ hm.1 (inv_id n x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val
        (PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.wiresFrom acc.2 (List.ofFn x)) = circuitFun n C x := by
    intro x
    rw [((hinv x).2 C.output).2]
    rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | inl c =>
    obtain ⟨x, y, hne⟩ := hnc
    apply False.elim
    apply hne
    rw [← hval x, ← hval y, hst]
    rfl
  | inr j =>
    let D : Circuit := ⟨acc.2, j⟩
    have hD : FanInTwo D :=
      elim_ok n C.gates (idStats n, []) (by simp)

    have he : circuitFun n D = circuitFun n C := by
      funext x
      have hx := hval x
      rw [hst] at hx
      exact hx
    have hmin := hm.2 D hD he
    have hbound := elim_len n C.gates (idStats n, [])
    have hfull : acc.2.length = C.gates.length := by
      change C.gates.length ≤ acc.2.length at hmin
      change acc.2.length ≤ [].length + C.gates.length at hbound
      simp only [List.length_nil, zero_add] at hbound
      omega
    have hid : acc.2 = C.gates.map normGate := by
      have hh := elim_identity_of_full_length n C.gates [] hm.1 (by
        simpa only [List.length_nil, Nat.add_zero, zero_add] using hfull)
      simpa only [List.length_nil, Nat.add_zero, List.nil_append] using hh
    have hclean : CleanL n acc.2 :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hm.1
        (inv_id n _) (by intro p g hp; simp at hp)
    simpa only [hid] using hclean

lemma normalized_least (n : ℕ) (C : Circuit)
    (hm : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) :
    Readers.Least n (circuitFun n C) (C.gates.map normGate) C.output := by
  refine ⟨normalized_clean_of_minimal n C hm hnc, ?_, ?_⟩
  · intro x
    change (PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false = _
    rw [wiresFrom_norm]
    rfl
  · intro gs o hcl he
    let D : Circuit := ⟨gs, o⟩
    have hD : FanInTwo D := by
      intro g hg
      exact (clean_nok n gs hcl g hg).1
    have hmin := hm.2 D hD (funext he)
    simpa only [List.length_map, Circuit.size, D] using hmin








end HelperReview


namespace H5C7Preview

open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace PetersenFirstGroup

def c7Mask : PetersenGroupBFS.MaskGraph :=
  ⟨7, fun v => (#[66, 5, 10, 20, 40, 80, 33] : Array Nat)[v]?.getD 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma c7_no_three :
    PetersenGroupBFS.fullMask c7Mask ∉ PetersenGroupBFS.frontier c7Mask 3 := by
  decide +kernel

lemma c7_groups_need_four (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 7, G.Adj u v ↔ (c7Mask.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 7))) (twins : BranchGraph.TwinSteps G ∅ groups)
    (finished : BranchGraph.EdgelessAfter G (BranchGraph.removedThrough ∅ groups)) :
    4 ≤ groups.length :=
  @PetersenMaskBridge.groups_exceed_budget c7Mask G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 7)) 3 c7_no_three groups twins finished

def c7Edges : List (Fin 7 × Fin 7) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0)]

lemma c7_no_loops : ∀ e ∈ c7Edges, e.1 ≠ e.2 := by decide

def c7Graph : SimpleGraph (Fin 7) where
  Adj a b := (a, b) ∈ c7Edges ∨ (b, a) ∈ c7Edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim
    (fun he => c7_no_loops (v, v) he rfl) (fun he => c7_no_loops (v, v) he rfl)⟩

abbrev c7GraphDecidable : DecidableRel c7Graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ c7Edges ∨ (b, a) ∈ c7Edges))

def c7F (x : Fin 7 → Bool) : Bool := c7Edges.any (fun e => x e.1 && x e.2)

lemma c7_nonconstant : ∃ x y : Fin 7 → Bool, c7F x ≠ c7F y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩

lemma c7_depends (v : Fin 7) : Dep c7F v := by
  refine ⟨fun k => decide (k.val = (v.val + 1) % 7), ?_⟩
  fin_cases v <;> decide

lemma c7_restrict_nonconstant (v : Fin 7) (b : Bool) :
    ∃ x y : Fin 7 → Bool, c7F (Function.update x v b) ≠ c7F (Function.update y v b) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  fin_cases v <;> cases b <;> decide

set_option maxRecDepth 20000 in
lemma c7_graph_edges (x : Fin 7 → Bool) : c7F x = true ↔
    ∃ u v : Fin 7, c7Graph.Adj u v ∧ x u = true ∧ x v = true := by
  simp only [c7F, List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩, he, hb⟩
    have hb' : x u = true ∧ x v = true := by simpa only [Bool.and_eq_true] using hb
    exact ⟨u, v, Or.inl he, hb'.1, hb'.2⟩
  · rintro ⟨u,v,hg,hu,hv⟩
    rcases hg with hg | hg
    · exact ⟨(u,v), hg, by simp [hu,hv]⟩
    · exact ⟨(v,u), hg, by simp [hu,hv]⟩

lemma c7_graph_matches_mask : ∀ a b : Fin 7, c7Graph.Adj a b ↔
    (c7Mask.adjacency a.val).testBit b.val = true := by
  change ∀ a b : Fin 7, ((a, b) ∈ c7Edges ∨ (b, a) ∈ c7Edges) ↔
    (c7Mask.adjacency a.val).testBit b.val = true
  decide +kernel

lemma c7_graph_alternate_neighbors : ∀ i j : Fin 7, c7Graph.Adj i j →
    ∃ u v, c7Graph.Adj i u ∧ c7Graph.Adj j v ∧
      u ≠ j ∧ v ≠ i ∧ ¬ c7Graph.Adj u v := by
  intro i j hij
  let u : Fin 7 := ⟨(i.val + if j.val = (i.val + 1) % 7 then 6 else 1) % 7, Nat.mod_lt _ (by decide)⟩
  let v : Fin 7 := ⟨(j.val + if i.val = (j.val + 1) % 7 then 6 else 1) % 7, Nat.mod_lt _ (by decide)⟩
  refine ⟨u, v, ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all [c7Graph, c7Edges, u, v]

lemma c7_marked_edges (S : Finset (Fin 7)) :
    c7F (setInput S) = true ↔ BranchGraph.containsEdge c7Graph S := by
  rw [c7_graph_edges]
  simp only [setInput, decide_eq_true_eq, BranchGraph.containsEdge]
  aesop

lemma c7_output_valid {gs : List Gate} {out : Nat} (least : Least 7 c7F gs out) :
    out < 7 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv c7_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

lemma c7_four_branches (gs : List Gate) (out : Nat) (least : Least 7 c7F gs out) :
    4 ≤ (circuitBranchWires (n := 7) gs).card := by
  classical
  letI : DecidableRel c7Graph.Adj := c7GraphDecidable
  have outValid := c7_output_valid least
  let outWire : Fin (7 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant outValid
  let label : Fin 7 → Fin (7 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (7 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 7 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue c7Graph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, c7_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 7)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge c7Graph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact c7_marked_edges S
  have independent (r) : BranchGraph.Independent c7Graph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least c7_nonconstant)
      c7Graph computes c7_graph_alternate_neighbors r
  have labels (v : Fin 7) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live
      (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup c7Graph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live c7Graph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required c7Graph label outWire branches 4 labels before twins
    (independent outWire) (c7_groups_need_four c7Graph c7_graph_matches_mask)

lemma c7_ten_has_no_not (gs : List Gate) (out : Nat) (least : Least 7 c7F gs out)
    (size : gs.length = 10) : ∀ g ∈ gs, g.op ≠ GateOp.not := by
  classical
  intro g present isNot
  have notPositive := one_not_gate_positive ⟨g, present, isNot⟩
  have outValid := c7_output_valid least
  let valEmbed : Fin (7 + gs.length) ↪ Nat := ⟨Fin.val, fun _ _ h => Fin.ext h⟩
  let branches := (circuitBranchWires (n := 7) gs).map valEmbed
  have branchLower : 4 ≤ branches.card := by
    simp only [branches, Finset.card_map]
    exact c7_four_branches gs out least
  have used := least_wire_used least c7_nonconstant c7_depends c7_restrict_nonconstant
  have doubles (w : Nat) (mem : w ∈ branches) :
      ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w := by
    obtain ⟨i, branched, eq⟩ := Finset.mem_map.mp mem
    have readers := branch_slots_of_read_edges (in_circuit_branches.mp branched)
    exact (show i.val = w from eq) ▸ readers
  have budget := branching_budget least.hcl outValid used branches doubles
  omega

end H5C7Preview
namespace HelperReview

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers

lemma normGate_op (g : Gate) : (normGate g).op = g.op := by
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma exact10_cycle7_has_no_not (C : Circuit)
    (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  have hm := cycle7_minimal C hf hs he
  have hfun : circuitFun 7 C = H5C7Preview.c7F := by
    funext x
    change C.eval (List.ofFn x) = H5C7Preview.c7F x
    rw [he x]
    simp [H5C7Preview.c7F, H5C7Preview.c7Edges, Bool.or_assoc]
  have hnc : ∃ x y : Fin 7 → Bool, circuitFun 7 C x ≠ circuitFun 7 C y := by
    simpa only [hfun] using H5C7Preview.c7_nonconstant
  have least : Readers.Least 7 H5C7Preview.c7F (C.gates.map normGate) C.output := by
    simpa only [hfun] using normalized_least 7 C hm hnc
  have noNot := H5C7Preview.c7_ten_has_no_not (C.gates.map normGate) C.output
    least (by simpa only [List.length_map, Circuit.size] using hs)
  intro g hg
  have hn := noNot (normGate g) (List.mem_map_of_mem hg)
  simpa only [normGate_op] using hn

end HelperReview


namespace HelperReview

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers

lemma normGate_identity_of_no_not (g : Gate) (hn : g.op ≠ .not) : normGate g = g := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [normGate]

lemma exact10_cycle7_clean (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) : CleanL 7 C.gates := by
  have hm := cycle7_minimal C hf hs he
  have hnc : ∃ x y : Fin 7 → Bool, circuitFun 7 C x ≠ circuitFun 7 C y := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    change C.eval (List.ofFn fun _ : Fin 7 => false) ≠ C.eval (List.ofFn fun _ : Fin 7 => true)
    rw [he, he]
    decide
  have clean := normalized_clean_of_minimal 7 C hm hnc
  have noNot := exact10_cycle7_has_no_not C hf hs he
  have unchanged : C.gates.map normGate = C.gates := by
    calc C.gates.map normGate = C.gates.map id := by
           apply List.map_congr_left
           intro g hg
           exact normGate_identity_of_no_not g (noNot g hg)
         _ = C.gates := by simp
  simpa only [unchanged] using clean

end HelperReview


namespace HelperReviewEquality

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux

noncomputable def branchValues (C : Circuit) : Finset Nat :=
  (circuitBranchWires (n := 7) C.gates).map
    (⟨Fin.val, fun _ _ h => Fin.ext h⟩ : Fin (7 + C.gates.length) ↪ Nat)

lemma raw_least (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers.Least
      7 H5C7Preview.c7F C.gates C.output := by
  have hm := cycle7_minimal C hf hs he
  have hclean := HelperReview.exact10_cycle7_clean C hf hs he
  have hfun : circuitFun 7 C = H5C7Preview.c7F := by
    funext x
    change C.eval (List.ofFn x) = H5C7Preview.c7F x
    rw [he x]
    simp [H5C7Preview.c7F, H5C7Preview.c7Edges, Bool.or_assoc]
  refine ⟨hclean, ?_, ?_⟩
  · intro x
    exact congrFun hfun x
  · intro gs out hc hd
    let D : Circuit := ⟨gs, out⟩
    have hD : FanInTwo D := by
      intro g hg
      exact (clean_nok 7 gs hc g hg).1
    have eq : circuitFun 7 D = circuitFun 7 C := by
      rw [hfun]
      exact funext hd
    exact hm.2 D hD eq

lemma exact_counts {L : List Nat} {B : Finset Nat}
    (hcard : L.toFinset.card = 16) (hbranch : B.card = 4)
    (hlen : L.length = 20) (htwo : ∀ w ∈ B, 2 ≤ L.count w) :
    ∀ w ∈ L.toFinset, L.count w = if w ∈ B then 2 else 1 := by
  classical
  have hsub : B ⊆ L.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := htwo w hw; omega))
  have lower : ∀ w ∈ L.toFinset, (if w ∈ B then 2 else 1) ≤ L.count w := by
    intro w hw
    split_ifs with hb
    · exact htwo w hb
    · have positive := List.count_pos_iff.mpr (List.mem_toFinset.mp hw)
      omega
  have countB : (∑ w ∈ L.toFinset, if w ∈ B then (1 : Nat) else 0) = B.card := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have base : (∑ w ∈ L.toFinset, if w ∈ B then (2 : Nat) else 1) = 20 := by
    have expand : ∀ w, (if w ∈ B then (2 : Nat) else 1) = 1 + if w ∈ B then 1 else 0 := by
      intro w
      split_ifs <;> rfl
    simp_rw [expand]
    rw [Finset.sum_add_distrib, countB]
    simp [hcard, hbranch]
  have totals : (∑ w ∈ L.toFinset, if w ∈ B then (2 : Nat) else 1) =
      ∑ w ∈ L.toFinset, L.count w := by
    rw [base, List.sum_toFinset_count_eq_length, hlen]
  intro w hw
  exact ((Finset.sum_eq_sum_iff_of_le lower).mp totals w hw).symm

lemma raw_exact_branch_budget (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    (branchValues C).card = 4 ∧
      (operands C.gates).length = 20 ∧
      (operands C.gates).toFinset.card = 16 ∧
      ∀ w ∈ (operands C.gates).toFinset,
        (operands C.gates).count w = if w ∈ branchValues C then 2 else 1 := by
  classical
  have least := raw_least C hf hs he
  have size : C.gates.length = 10 := hs
  have outValid := H5C7Preview.c7_output_valid least
  have used := least_wire_used least H5C7Preview.c7_nonconstant
    H5C7Preview.c7_depends H5C7Preview.c7_restrict_nonconstant
  have lower : 4 ≤ (branchValues C).card := by
    simp only [branchValues, Finset.card_map]
    exact H5C7Preview.c7_four_branches C.gates C.output least
  have doubles (w : Nat) (hw : w ∈ branchValues C) :
      ∃ p q, p ≠ q ∧
        PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers.Reads C.gates p w ∧
        PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers.Reads C.gates q w := by
    obtain ⟨i, hi, hval⟩ := Finset.mem_map.mp hw
    have readers := branch_slots_of_read_edges (in_circuit_branches.mp hi)
    exact (show i.val = w from hval) ▸ readers
  have budget := branching_budget least.hcl outValid used (branchValues C) doubles
  have bcard : (branchValues C).card = 4 := by omega
  have nots : notGateCount C.gates = 0 := by omega
  have len := operands_count_length C.gates (clean_gate_arity least.hcl)
  have llen : (operands C.gates).length = 20 := by omega
  let required := (Finset.range (7 + C.gates.length)).erase C.output
  have subset : required ⊆ (operands C.gates).toFinset := by
    intro w hw
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hw
    obtain ⟨p, hp⟩ := used w (Finset.mem_range.mp hlt) hne
    exact List.mem_toFinset.mpr (operand_mem_of_read hp)
  have rcard : required.card = 16 := by
    dsimp [required]
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range, size]
  have wlower : 16 ≤ (operands C.gates).toFinset.card := by
    simpa only [rcard] using Finset.card_le_card subset
  have twice (w : Nat) (hw : w ∈ branchValues C) : 2 ≤ (operands C.gates).count w := by
    obtain ⟨p, q, hne, hp, hq⟩ := doubles w hw
    exact two_readers_operand_count hne hp hq
  have wb := branch_card_add_wire_card_le_operands C.gates (branchValues C) twice
  have wcard : (operands C.gates).toFinset.card = 16 := by omega
  exact ⟨bcard, llen, wcard, exact_counts wcard bcard llen twice⟩

end HelperReviewEquality


namespace H5BranchSingleton

def point (v : Fin 7) (j : Fin 7) : Bool := decide (j = v)

lemma point_le {x : Fin 7 → Bool} {v : Fin 7} (hx : x v = true) : point v ≤ x := by
  intro j
  by_cases hj : j = v
  · subst j
    simp [point, hx]
  · simp [point, hj]

lemma true_of_coordinate (g : (Fin 7 → Bool) → Bool) (mono : Monotone g)
    (v : Fin 7) (hp : g (point v) = true) (x : Fin 7 → Bool) (hx : x v = true) :
    g x = true :=
  Bool.eq_true_of_true_le (by simpa [hp] using mono (point_le hx))


def cycle (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def pairPoint (v w : Fin 7) (j : Fin 7) : Bool := decide (j = v ∨ j = w)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma cofactor_depends : ∀ v u : Fin 7, u ≠ v → ∃ w : Fin 7,
    cycle (Function.update (pairPoint v w) u true) ≠ cycle (pairPoint v w) := by
  decide +kernel

lemma class_singleton (S : Finset (Fin 7)) (g : (Fin 7 → Bool) → Bool)
    (mono : Monotone g) (v : Fin 7) (hp : g (point v) = true)
    (factor : ∀ x y, (∀ j, j ∉ S → x j = y j) → g x = g y → cycle x = cycle y) :
    ∀ u ∈ S, u = v := by
  intro u hu
  by_contra different
  obtain ⟨w, depends⟩ := cofactor_depends v u different
  let x := pairPoint v w
  let y := Function.update x u true
  have hx : x v = true := by simp [x, pairPoint]
  have hy : y v = true := by simp [y, Function.update_of_ne (Ne.symm different), hx]
  have cut : g x = g y := by
    rw [true_of_coordinate g mono v hp x hx, true_of_coordinate g mono v hp y hy]
  have outside : ∀ j, j ∉ S → x j = y j := by
    intro j hj
    have different : j ≠ u := by
      rintro rfl
      exact hj hu
    simp [y, Function.update_of_ne different]
  exact depends (factor x y outside cut).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma separating_pair : ∀ v u : Fin 7, u ≠ v → ∃ t : Fin 7,
    cycle (pairPoint u t) = false ∧
      cycle (Function.update (pairPoint u t) v true) = true := by
  decide +kernel

lemma other_singletons_false (S : Finset (Fin 7)) (g : (Fin 7 → Bool) → Bool)
    (mono : Monotone g) (v : Fin 7) (hv : v ∈ S) (hp : g (point v) = true)
    (factor : ∀ x y, (∀ j, j ∉ S → x j = y j) → g x = g y → cycle x = cycle y) :
    ∀ u, u ≠ v → g (point u) = false := by
  intro u different
  cases hu : g (point u) with
  | false => rfl
  | true =>
    obtain ⟨t, hfalse, htrue⟩ := separating_pair v u different
    let x := pairPoint u t
    let y := Function.update x v true
    have gx : g x = true := true_of_coordinate g mono u hu x (by simp [x, pairPoint])
    have gy : g y = true := true_of_coordinate g mono v hp y (by simp [y])
    have outside : ∀ j, j ∉ S → x j = y j := by
      intro j hj
      have different : j ≠ v := by
        rintro rfl
        exact hj hv
      simp [y, Function.update_of_ne different]
    have same := factor x y outside (by rw [gx, gy])
    change cycle (pairPoint u t) = cycle (Function.update (pairPoint u t) v true) at same
    rw [hfalse, htrue] at same
    cases same

end H5BranchSingleton


namespace H5C7Cover

def covers (D : Finset (Fin 7)) : Prop :=
  ∀ i : Fin 7, i ∈ D ∨ i + 1 ∈ D

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma unique_internal_edge : ∀ D : Finset (Fin 7), D.card = 4 → covers D →
    ∃ p : Fin 7,
      (∀ q : Fin 7, (q ∈ D ∧ q + 1 ∈ D) ↔ q = p) ∧
      p - 1 ∉ D ∧ p + 2 ∉ D := by
  unfold covers
  decide +kernel



lemma cover_card_lower : ∀ D : Finset (Fin 7), covers D → 4 ≤ D.card := by
  unfold covers
  decide +kernel

abbrev adjacent (u v : Fin 7) : Prop := v = u + 1 ∨ u = v + 1

def earlierCover {m : Nat} (label : Fin 7 → Fin m) : Finset (Fin 7) :=
  Finset.univ.filter (fun v => ∃ w, adjacent v w ∧ label v < label w)

lemma earlierCover_mem {m : Nat} (label : Fin 7 → Fin m) (v : Fin 7) :
    v ∈ earlierCover label ↔ ∃ w, adjacent v w ∧ label v < label w := by
  simp [earlierCover]

lemma earlierCover_covers {m : Nat} (label : Fin 7 → Fin m)
    (independent : ∀ v : Fin 7, label v ≠ label (v + 1)) : covers (earlierCover label) := by
  intro v
  rcases lt_or_gt_of_ne (independent v) with forward | backward
  · exact Or.inl ((earlierCover_mem label v).mpr ⟨v + 1, Or.inl rfl, forward⟩)
  · exact Or.inr ((earlierCover_mem label (v + 1)).mpr ⟨v, Or.inr rfl, backward⟩)

lemma representative_cover {m : Nat} (label : Fin 7 → Fin m)
    (out : Fin m) (branches : Finset (Fin m)) (four : branches.card = 4)
    (allLabels : ∀ v, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ b ∈ branches, b < out)
    (independent : ∀ v : Fin 7, label v ≠ label (v + 1))
    (activeSingleton : ∀ v w, adjacent v w → label v < label w →
      ∀ u, label u = label v → u = v) :
    (earlierCover label).card = 4 ∧ covers (earlierCover label) ∧
      ∀ b ∈ branches, ∃ v ∈ earlierCover label, label v = b ∧
        ∀ u, label u = b → u = v := by
  have allLe : ∀ v, label v ≤ out := by
    intro v
    rcases allLabels v with same | member
    · exact same.le
    · exact le_of_lt (beforeOut _ member)
  have member : ∀ v ∈ earlierCover label, label v ∈ branches := by
    intro v hv
    obtain ⟨w, _, earlier⟩ := (earlierCover_mem label v).mp hv
    rcases allLabels v with same | member
    · have impossible := lt_of_lt_of_le earlier (allLe w)
      rw [same] at impossible
      exact (lt_irrefl out impossible).elim
    · exact member
  have injective : Set.InjOn label (earlierCover label) := by
    intro u hu v hv same
    obtain ⟨w, adjacent, earlier⟩ := (earlierCover_mem label u).mp hu
    exact (activeSingleton u w adjacent earlier v same.symm).symm
  have imageCard : ((earlierCover label).image label).card = (earlierCover label).card :=
    Finset.card_image_iff.mpr injective
  have imageSubset : (earlierCover label).image label ⊆ branches := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact member v hv
  have cover := earlierCover_covers label independent
  have lower := cover_card_lower (earlierCover label) cover
  have upper := Finset.card_le_card imageSubset
  have cardinal : (earlierCover label).card = 4 := by
    rw [imageCard, four] at upper
    omega
  have imageEq : (earlierCover label).image label = branches :=
    Finset.eq_of_subset_of_card_le imageSubset (by rw [imageCard, cardinal, four])
  refine ⟨cardinal, cover, ?_⟩
  intro b hb
  rw [← imageEq] at hb
  obtain ⟨v, hv, same⟩ := Finset.mem_image.mp hb
  obtain ⟨w, adjacent, earlier⟩ := (earlierCover_mem label v).mp hv
  refine ⟨v, hv, same, ?_⟩
  intro u hu
  exact activeSingleton v w adjacent earlier u (hu.trans same.symm)

end H5C7Cover




namespace Helper3WireMonotone

open PEqualNP.CircuitLowerBounds

lemma gate_true_mono (g : Gate) (hm : g.op = .and ∨ g.op = .or)
    (w₁ w₂ : List Bool)
    (h : ∀ i, w₁.getD i false = true → w₂.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w₁.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
  rcases hm with ho | ho <;> rw [ho] at he ⊢
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at he ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact h i (he _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at he ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, ht⟩ := he
    exact ⟨_, ⟨i, hi, rfl⟩, h i ht⟩

lemma fold_true_mono (gs : List Gate) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hw : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    ∀ i,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
        w₁).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
        w₂).getD i false = true := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    · simp [hlen]
    · intro g' hg'
      exact hm g' (List.mem_cons_of_mem _ hg')
    intro i hi
    by_cases hlt : i < w₁.length
    · have hx : w₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_append_left hlt] at hi
        rw [List.getD_eq_getElem _ _ hlt]
        exact hi
      have hy := hw i hx
      rw [List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_append_left (by omega)]
      rw [List.getD_eq_getElem _ _ (by omega)] at hy
      exact hy
    · by_cases heq : i = w₁.length
      · subst i
        have hv : g.op.eval (g.inputs.map fun j => w₁.getD j false) = true := by
          rw [List.getD_eq_getElem _ _ (by simp)] at hi
          simpa using hi
        have hv' := gate_true_mono g (hm g (List.mem_cons_self ..)) w₁ w₂ hw hv
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        simpa [hlen] using hv'
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi

lemma wire_true_mono {n : ℕ} (C : Circuit)
    (hm : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hx : (C.wires (List.ofFn x)).getD w false = true) :
    (C.wires (List.ofFn y)).getD w false = true := by
  apply fold_true_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) hm ?_ w hx
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact hxy ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma wire_monotone {n : ℕ} (C : Circuit)
    (hm : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD w false) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact wire_true_mono C hm x y (fun i => Bool.le_iff_imp.mp (hxy i)) w








end Helper3WireMonotone



namespace Helper3Signal

def singleton {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def pair {n : ℕ} (v w : Fin n) : Fin n → Bool := fun i => decide (i = v ∨ i = w)

lemma singleton_le_pair {n : ℕ} (v w : Fin n) : singleton v ≤ pair v w := by
  intro i
  by_cases hi : i = v
  · subst i
    simp [singleton, pair]
  · simp [singleton, pair, hi]

lemma monotone_signal_representation {n : ℕ} (W : (Fin n → Bool) → Bool)
    (v : Fin n) (mono : Monotone W) (active : W (singleton v) = true) :
    ∀ x, W x = (x v || W (Function.update x v false)) := by
  intro x
  cases hv : x v with
  | false =>
    have same : Function.update x v false = x := by
      funext i
      by_cases hi : i = v
      · subst i
        simp [hv]
      · simp [Function.update_of_ne hi]
    simp [same]
  | true =>
    have smaller : singleton v ≤ x := by
      intro i
      by_cases hi : i = v
      · subst i
        simp [singleton, hv]
      · simp [singleton, hi]
    have yes : W x = true := Bool.le_iff_imp.mp (mono smaller) active
    simp [yes]

def residual {n : ℕ} (W : (Fin n → Bool) → Bool) (v : Fin n)
    (x : Fin n → Bool) : Bool := W (Function.update x v false)


def DependsOnly {n : ℕ} (W : (Fin n → Bool) → Bool) (D : Finset (Fin n)) : Prop :=
  ∀ x y, (∀ i ∈ D, x i = y i) → W x = W y


def earlierMask {n m : ℕ} (label : Fin n → Fin m) (cut : Fin m)
    (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if label i < cut then x i else false

lemma earlierMask_monotone {n m : ℕ} (label : Fin n → Fin m) (cut : Fin m) :
    Monotone (earlierMask label cut) := by
  intro x y smaller i
  by_cases hi : label i < cut
  · simpa [earlierMask, hi] using smaller i
  · simp [earlierMask, hi]

lemma earlier_signal_monotone {n m : ℕ} (W : (Fin n → Bool) → Bool)
    (label : Fin n → Fin m) (cut : Fin m) (mono : Monotone W) :
    Monotone (fun x => W (earlierMask label cut x)) :=
  mono.comp (earlierMask_monotone label cut)

lemma earlier_signal_agrees {n m : ℕ} (W : (Fin n → Bool) → Bool)
    (label : Fin n → Fin m) (cut : Fin m) (x y : Fin n → Bool)
    (agree : ∀ i, label i < cut → x i = y i) :
    W (earlierMask label cut x) = W (earlierMask label cut y) := by
  congr 1
  funext i
  by_cases hi : label i < cut
  · simp [earlierMask, hi, agree i hi]
  · simp [earlierMask, hi]

lemma update_signal_eq_earlier_signal {n m : ℕ} (W : (Fin n → Bool) → Bool)
    (label : Fin n → Fin m) (cut : Fin m) (v : Fin n)
    (atCut : label v = cut) (only : ∀ i, label i = cut → i = v)
    (dependency : ∀ x y, (∀ i, label i ≤ cut → x i = y i) → W x = W y)
    (x : Fin n → Bool) :
    W (Function.update x v false) = W (earlierMask label cut x) := by
  apply dependency
  intro i before
  by_cases strictly : label i < cut
  · have different : i ≠ v := by
      intro same
      subst i
      simp [atCut] at strictly
    simp [earlierMask, strictly, Function.update_of_ne different]
  · have equal : label i = cut := le_antisymm before (le_of_not_gt strictly)
    have iv := only i equal
    subst i
    simp [earlierMask, atCut]

lemma earlierMask_update_atCut {n m : ℕ} (label : Fin n → Fin m) (cut : Fin m)
    (v : Fin n) (atCut : label v = cut) (x : Fin n → Bool) (b : Bool) :
    earlierMask label cut (Function.update x v b) = earlierMask label cut x := by
  funext i
  by_cases strictly : label i < cut
  · have different : i ≠ v := by
      intro same
      subst i
      simp [atCut] at strictly
    simp [earlierMask, strictly, Function.update_of_ne different]
  · simp [earlierMask, strictly]

lemma representation_collision {n : ℕ} (W H : (Fin n → Bool) → Bool) (v : Fin n)
    (representation : ∀ x, W x = (x v || H x))
    (independent : ∀ x b, H (Function.update x v b) = H x) :
    ∀ x, H x = true → W (Function.update x v false) = W (Function.update x v true) := by
  intro x yes
  rw [representation, representation, independent, independent]
  simp [yes]

lemma labeled_signal_representation {n m : ℕ} (W : (Fin n → Bool) → Bool)
    (label : Fin n → Fin m) (cut : Fin m) (v : Fin n)
    (mono : Monotone W) (active : W (singleton v) = true)
    (atCut : label v = cut) (only : ∀ i, label i = cut → i = v)
    (dependency : ∀ x y, (∀ i, label i ≤ cut → x i = y i) → W x = W y) :
    ∀ x, W x = (x v || W (earlierMask label cut x)) := by
  intro x
  rw [monotone_signal_representation W v mono active x,
    update_signal_eq_earlier_signal W label cut v atCut only dependency x]

def cycle7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def neighborValue (v : Fin 7) (x : Fin 7 → Bool) : Bool := x (v - 1) || x (v + 1)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
lemma cycle7_cofactor_identity : ∀ (v : Fin 7) (x : Fin 7 → Bool),
    cycle7 (Function.update x v true) =
      (cycle7 (Function.update x v false) || neighborValue v x) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
lemma cycle7_singleton_collision_witness : ∀ v j : Fin 7, ∃ k : Fin 7,
    (k = v - 1 ∨ k = v + 1) ∧
      cycle7 (Function.update (pair j k) v false) = false := by
  decide +kernel

def DerivativeSafe (v : Fin 7) (H : (Fin 7 → Bool) → Bool) : Prop :=
  ∀ x, H x = true → neighborValue v x = true →
    cycle7 (Function.update x v false) = true

def CollisionEq (v : Fin 7) (H : (Fin 7 → Bool) → Bool) : Prop :=
  ∀ x, H x = true → cycle7 (Function.update x v false) = cycle7 (Function.update x v true)

lemma derivativeSafe_of_collisionEq (v : Fin 7) (H : (Fin 7 → Bool) → Bool)
    (collision : CollisionEq v H) : DerivativeSafe v H := by
  intro x yes neighbor
  calc
    cycle7 (Function.update x v false) = cycle7 (Function.update x v true) := collision x yes
    _ = true := by rw [cycle7_cofactor_identity, neighbor]; simp



lemma derivativeSafe_singleton_false (v : Fin 7) (H : (Fin 7 → Bool) → Bool)
    (mono : Monotone H) (safe : DerivativeSafe v H) :
    ∀ j : Fin 7, H (singleton j) = false := by
  intro j
  by_contra notFalse
  have yes : H (singleton j) = true := Bool.eq_true_of_not_eq_false notFalse
  obtain ⟨k, neighbor, noEdge⟩ := cycle7_singleton_collision_witness v j
  have both : H (pair j k) = true :=
    Bool.le_iff_imp.mp (mono (singleton_le_pair j k)) yes
  have near : neighborValue v (pair j k) = true := by
    rcases neighbor with left | right
    · subst k
      simp [neighborValue, pair]
    · subst k
      simp [neighborValue, pair]
  have wrong := safe (pair j k) both near
  rw [noEdge] at wrong
  cases wrong

lemma collisionEq_singleton_false (v : Fin 7) (H : (Fin 7 → Bool) → Bool)
    (mono : Monotone H) (collision : CollisionEq v H) :
    ∀ j : Fin 7, H (singleton j) = false :=
  derivativeSafe_singleton_false v H mono (derivativeSafe_of_collisionEq v H collision)


end Helper3Signal



namespace H5FirstInputFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenFirstGroup PetersenCutTrace



end H5FirstInputFactor



namespace H5C7Cover

lemma earlierCover_iff_before {m : Nat} (label : Fin 7 → Fin m)
    (out : Fin m) (branches : Finset (Fin m)) (four : branches.card = 4)
    (allLabels : ∀ v, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ b ∈ branches, b < out)
    (independent : ∀ v : Fin 7, label v ≠ label (v + 1))
    (activeSingleton : ∀ v w, adjacent v w → label v < label w →
      ∀ u, label u = label v → u = v) :
    ∀ v, v ∈ earlierCover label ↔ label v < out := by
  have representatives := (representative_cover label out branches four allLabels beforeOut
    independent activeSingleton).2.2
  intro v
  constructor
  · intro hv
    obtain ⟨w, _, earlier⟩ := (earlierCover_mem label v).mp hv
    apply lt_of_lt_of_le earlier
    rcases allLabels w with same | member
    · exact same.le
    · exact le_of_lt (beforeOut _ member)
  · intro earlier
    rcases allLabels v with same | member
    · rw [same] at earlier
      exact (lt_irrefl out earlier).elim
    · obtain ⟨u, hu, _, unique⟩ := representatives (label v) member
      exact (unique v rfl).symm ▸ hu


end H5C7Cover


namespace H5C7CircuitCover

open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace PetersenFirstGroup
open H5C7Preview

lemma c7_adjacent_iff (u v : Fin 7) :
    c7Graph.Adj u v ↔ H5C7Cover.adjacent u v := by
  change ((u, v) ∈ c7Edges ∨ (v, u) ∈ c7Edges) ↔ v = u + 1 ∨ u = v + 1
  fin_cases u <;> fin_cases v <;> decide

lemma boundary_labels {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (v : Fin 7) :
    firstInputBoundary clean out live v = out ∨
      firstInputBoundary clean out live v ∈ circuitBranchWires gs := by
  have stopped := FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live
    (inputWire gs v)
  rcases stopped with outLabel | fork
  · exact Or.inl outLabel
  · exact Or.inr (in_circuit_branches.mpr fork)

lemma branches_before_output {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (b : Fin (7 + gs.length)) (member : b ∈ circuitBranchWires gs) : b < out := by
  obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
  exact lt_of_lt_of_le (read_order clean path) (wire_le_output clean out live a)

lemma boundary_adjacent_distinct {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = c7F x) :
    ∀ v : Fin 7,
      firstInputBoundary clean out live v ≠ firstInputBoundary clean out live (v + 1) := by
  have graphComputes (x : Fin 7 → Bool) :
      vl gs x out.val = PetersenScratch.edgeValue c7Graph x := by
    rw [computes, Bool.eq_iff_iff, c7_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have groupIndependent (r) :
      BranchGraph.Independent c7Graph (firstInputGroup clean out live r) :=
    firstInputGroup_independent clean out live distinct c7Graph graphComputes
      c7_graph_alternate_neighbors r
  intro v same
  have leftMember : v ∈ firstInputGroup clean out live (firstInputBoundary clean out live v) :=
    (mem_firstInputGroup clean out live _ v).mpr rfl
  have rightMember : v + 1 ∈ firstInputGroup clean out live (firstInputBoundary clean out live v) :=
    (mem_firstInputGroup clean out live _ (v + 1)).mpr same.symm
  exact groupIndependent _ v leftMember (v + 1) rightMember
    ((c7_adjacent_iff v (v + 1)).mpr (Or.inl rfl))

lemma circuit_representative_cover {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = c7F x)
    (four : (circuitBranchWires (n := 7) gs).card = 4)
    (activeSingleton : ∀ v w : Fin 7, c7Graph.Adj v w →
      firstInputBoundary clean out live v < firstInputBoundary clean out live w →
      ∀ u : Fin 7,
        firstInputBoundary clean out live u = firstInputBoundary clean out live v → u = v) :
    let label := firstInputBoundary clean out live
    (H5C7Cover.earlierCover label).card = 4 ∧
      H5C7Cover.covers (H5C7Cover.earlierCover label) ∧
      (∀ b ∈ circuitBranchWires gs, ∃ v ∈ H5C7Cover.earlierCover label, label v = b ∧
        ∀ u, label u = b → u = v) ∧
      (∀ v, v ∈ H5C7Cover.earlierCover label ↔ label v < out) := by
  let label := firstInputBoundary clean out live
  have labels := boundary_labels clean out live
  have beforeOut := branches_before_output clean out live
  have independent := boundary_adjacent_distinct clean out live distinct computes
  have active : ∀ v w : Fin 7, H5C7Cover.adjacent v w → label v < label w →
      ∀ u : Fin 7, label u = label v → u = v := by
    intro v w adjacent earlier u same
    exact activeSingleton v w ((c7_adjacent_iff v w).mpr adjacent) earlier u same
  have cover := H5C7Cover.representative_cover label out (circuitBranchWires gs)
    four labels beforeOut independent active
  refine ⟨cover.1, cover.2.1, cover.2.2, ?_⟩
  exact H5C7Cover.earlierCover_iff_before label out (circuitBranchWires gs)
    four labels beforeOut independent active


end H5C7CircuitCover


namespace PEqualNP.Outside.L_meta_1549_aux.Helper3ActualSignal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace PetersenFirstGroup

lemma actual_prefix_dependency {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length))
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (x y : Fin n → Bool)
    (agree : ∀ i, firstInputBoundary clean out live i ≤ cut → x i = y i) :
    vl gs x cut.val = vl gs y cut.val := by
  apply agree_on_input_ancestors clean
  intro i ancestral
  apply agree i
  exact FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live
    ancestral terminal

noncomputable def earlierWire {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length)) (x : Fin n → Bool) : Bool :=
  vl gs (Helper3Signal.earlierMask (firstInputBoundary clean out live) cut x) cut.val

lemma actual_signal_representation {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length)) (v : Fin n)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (atCut : firstInputBoundary clean out live v = cut)
    (only : ∀ i, firstInputBoundary clean out live i = cut → i = v)
    (mono : Monotone (fun x : Fin n → Bool => vl gs x cut.val))
    (active : vl gs (Helper3Signal.singleton v) cut.val = true) :
    ∀ x, vl gs x cut.val = (x v || earlierWire clean out live cut x) := by
  exact Helper3Signal.labeled_signal_representation
    (fun x => vl gs x cut.val) (firstInputBoundary clean out live) cut v mono active
    atCut only (actual_prefix_dependency clean out live cut terminal)

lemma actual_earlier_monotone {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length))
    (mono : Monotone (fun x : Fin n → Bool => vl gs x cut.val)) :
    Monotone (earlierWire clean out live cut) :=
  Helper3Signal.earlier_signal_monotone (fun x => vl gs x cut.val)
    (firstInputBoundary clean out live) cut mono

lemma actual_earlier_agrees {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length)) (x y : Fin n → Bool)
    (agree : ∀ i, firstInputBoundary clean out live i < cut → x i = y i) :
    earlierWire clean out live cut x = earlierWire clean out live cut y :=
  Helper3Signal.earlier_signal_agrees (fun x => vl gs x cut.val)
    (firstInputBoundary clean out live) cut x y agree

lemma actual_first_boundary_blocks {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length)) (v : Fin n) (before : cut < out)
    (atCut : firstInputBoundary clean out live v = cut) :
    ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs v) out := by
  have label : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
      (inputWire gs v) = cut := atCut
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
    (v := inputWire gs v) (w := out) (by simpa only [label] using before)
  intro route
  apply blocked
  have weaker : ∀ a b, avoid (readEdge gs) cut a b →
      FirstBranchRoute.Avoid (readEdge gs) cut a b := fun _ _ h => ⟨h.1, h.2.1⟩
  have converted := Relation.ReflTransGen.mono weaker _ _ route
  simpa only [label] using converted

lemma actual_output_collision {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length)) (v : Fin n) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (atCut : firstInputBoundary clean out live v = cut)
    (only : ∀ i, firstInputBoundary clean out live i = cut → i = v)
    (mono : Monotone (fun x : Fin n → Bool => vl gs x cut.val))
    (active : vl gs (Helper3Signal.singleton v) cut.val = true)
    (x : Fin n → Bool) (yes : earlierWire clean out live cut x = true) :
    vl gs (Function.update x v false) out.val = vl gs (Function.update x v true) out.val := by
  have representation := actual_signal_representation clean out live cut v terminal
    atCut only mono active
  have independent : ∀ y b, earlierWire clean out live cut (Function.update y v b) =
      earlierWire clean out live cut y := by
    intro y b
    unfold earlierWire
    rw [Helper3Signal.earlierMask_update_atCut (firstInputBoundary clean out live) cut v atCut]
  have sameCut := Helper3Signal.representation_collision (fun y => vl gs y cut.val)
    (earlierWire clean out live cut) v representation independent x yes
  by_cases terminalOutput : cut = out
  · simpa only [terminalOutput] using sameCut
  have before : cut < out := lt_of_le_of_ne prior terminalOutput
  apply circuit_cut_agreement clean cut out _ _ sameCut
  intro i different
  have iv : i = v := by
    by_contra outside
    apply different
    simp [Function.update_of_ne outside]
  subst i
  exact actual_first_boundary_blocks clean out live cut v before atCut

lemma actual_cycle7_collisionEq {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (7 + gs.length)) (v : Fin 7) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (atCut : firstInputBoundary clean out live v = cut)
    (only : ∀ i, firstInputBoundary clean out live i = cut → i = v)
    (mono : Monotone (fun x : Fin 7 → Bool => vl gs x cut.val))
    (active : vl gs (Helper3Signal.singleton v) cut.val = true)
    (computes : ∀ x, vl gs x out.val = Helper3Signal.cycle7 x) :
    Helper3Signal.CollisionEq v (earlierWire clean out live cut) := by
  intro x yes
  have agree := actual_output_collision clean out live cut v prior terminal atCut only mono active x yes
  simpa only [computes] using agree

lemma actual_cycle7_earlier_singletons_false {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (7 + gs.length)) (v : Fin 7) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (atCut : firstInputBoundary clean out live v = cut)
    (only : ∀ i, firstInputBoundary clean out live i = cut → i = v)
    (mono : Monotone (fun x : Fin 7 → Bool => vl gs x cut.val))
    (active : vl gs (Helper3Signal.singleton v) cut.val = true)
    (computes : ∀ x, vl gs x out.val = Helper3Signal.cycle7 x) :
    ∀ j, earlierWire clean out live cut (Helper3Signal.singleton j) = false :=
  Helper3Signal.collisionEq_singleton_false v (earlierWire clean out live cut)
    (actual_earlier_monotone clean out live cut mono)
    (actual_cycle7_collisionEq clean out live cut v prior terminal atCut only mono active computes)



end PEqualNP.Outside.L_meta_1549_aux.Helper3ActualSignal



namespace PEqualNP.Outside.L_meta_1549_aux.Helper3ActualSignal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace PetersenFirstGroup

lemma actual_wire_depends_only {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (cut : Fin (n + gs.length))
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (D : Finset (Fin n))
    (before_implies_mem : ∀ i, firstInputBoundary clean out live i ≤ cut → i ∈ D) :
    Helper3Signal.DependsOnly (fun x => vl gs x cut.val) D := by
  intro x y agree
  apply actual_prefix_dependency clean out live cut terminal x y
  intro i before
  exact agree i (before_implies_mem i before)

end PEqualNP.Outside.L_meta_1549_aux.Helper3ActualSignal



namespace H5WireProperties

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers

lemma clean_and_or {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (noNot : ∀ g ∈ gs, g.op ≠ .not) :
    ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  rcases clean p g hp with unary | binary
  · exact (noNot g hg unary.1).elim
  · exact binary.1


lemma vl_monotone {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (noNot : ∀ g ∈ gs, g.op ≠ .not) (w : Nat) :
    Monotone (fun x : Fin n → Bool => vl gs x w) := by
  exact Helper3WireMonotone.wire_monotone (⟨gs, 0⟩ : Circuit)
    (clean_and_or clean noNot) w


end H5WireProperties



namespace H5BranchSingleton


lemma singleton_activation (S : Finset (Fin 7)) (g : (Fin 7 → Bool) → Bool)
    (mono : Monotone g) (v u : Fin 7) (hv : v ∈ S)
    (adjacent : u = v + 1 ∨ v = u + 1)
    (ignore : g (pairPoint v u) = g (point v))
    (factor : ∀ x y, (∀ j, j ∉ S → x j = y j) → g x = g y → cycle x = cycle y) :
    g (point v) = true := by
  have singletonFalse : ∀ j : Fin 7, cycle (point j) = false := by decide +kernel
  have pairTrue : ∀ a b : Fin 7, b = a + 1 ∨ a = b + 1 →
      cycle (pairPoint a b) = true := by decide +kernel
  cases hvalue : g (point v) with
  | true => rfl
  | false =>
    have pairFalse : g (pairPoint v u) = false := ignore.trans hvalue
    have smaller : point u ≤ pairPoint v u := by
      intro j
      by_cases same : j = u
      · subst j
        simp [point, pairPoint]
      · simp [point, same]
    have pointFalse : g (point u) = false := by
      have bound := mono smaller
      rw [pairFalse] at bound
      exact le_antisymm bound (Bool.false_le _)
    have agree : ∀ j, j ∉ S → point u j = pairPoint v u j := by
      intro j outside
      have different : j ≠ v := by
        rintro rfl
        exact outside hv
      simp [point, pairPoint, different]
    have same := factor (point u) (pairPoint v u) agree (pointFalse.trans pairFalse.symm)
    rw [singletonFalse, pairTrue v u adjacent] at same
    cases same


end H5BranchSingleton


namespace H5C7ActiveSingleton

open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace PetersenFirstGroup
open H5C7Preview H5C7CircuitCover H5BranchSingleton

lemma c7F_eq_cycle (x : Fin 7 → Bool) : c7F x = cycle x := by
  simp [c7F, c7Edges, cycle, Bool.or_assoc]

lemma boundary_factor {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = c7F x)
    (cut : Fin (7 + gs.length)) :
    ∀ x y : Fin 7 → Bool,
      (∀ j, j ∉ firstInputGroup clean out live cut → x j = y j) →
      vl gs x cut.val = vl gs y cut.val → cycle x = cycle y := by
  intro x y outside sameCut
  have computesCycle (z : Fin 7 → Bool) : vl gs z out.val = cycle z :=
    (computes z).trans (c7F_eq_cycle z)
  have sameOut : vl gs x out.val = vl gs y out.val := by
    rcases firstInputGroup_controlled clean out live cut with equal | blocked
    · simpa only [equal] using sameCut
    · apply circuit_cut_agreement clean cut out x y sameCut
      intro i different
      apply blocked i
      by_contra absent
      exact different (outside i absent)
  exact (computesCycle x).symm.trans (sameOut.trans (computesCycle y))

lemma boundary_ignore_later {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (v u : Fin 7)
    (earlier : firstInputBoundary clean out live v < firstInputBoundary clean out live u) :
    vl gs (pairPoint v u) (firstInputBoundary clean out live v).val =
      vl gs (point v) (firstInputBoundary clean out live v).val := by
  apply agree_on_input_ancestors clean (pairPoint v u) (point v)
    (firstInputBoundary clean out live v)
  intro i route
  have different : i ≠ u := by
    intro same
    subst i
    have stopped := FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live
      (inputWire gs v)
    have bound := FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live
      route stopped
    exact (not_le_of_gt earlier) bound
  simp [pairPoint, point, different]

lemma boundary_singleton_activation {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = c7F x)
    (mono : ∀ cut : Fin (7 + gs.length), Monotone (fun x : Fin 7 → Bool => vl gs x cut.val))
    (v u : Fin 7) (adjacent : c7Graph.Adj v u)
    (earlier : firstInputBoundary clean out live v < firstInputBoundary clean out live u) :
    vl gs (point v) (firstInputBoundary clean out live v).val = true := by
  have member : v ∈ firstInputGroup clean out live (firstInputBoundary clean out live v) :=
    (mem_firstInputGroup clean out live _ v).mpr rfl
  exact singleton_activation (firstInputGroup clean out live (firstInputBoundary clean out live v))
    (fun x => vl gs x (firstInputBoundary clean out live v).val)
    (mono _) v u member ((c7_adjacent_iff v u).mp adjacent)
    (boundary_ignore_later clean out live v u earlier)
    (boundary_factor clean out live computes _)

lemma boundary_activeSingleton {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = c7F x)
    (mono : ∀ cut : Fin (7 + gs.length), Monotone (fun x : Fin 7 → Bool => vl gs x cut.val)) :
    ∀ v w : Fin 7, c7Graph.Adj v w →
      firstInputBoundary clean out live v < firstInputBoundary clean out live w →
      ∀ u : Fin 7,
        firstInputBoundary clean out live u = firstInputBoundary clean out live v → u = v := by
  intro v w adjacent earlier u same
  have activated := boundary_singleton_activation clean out live computes mono v w adjacent earlier
  have member : u ∈ firstInputGroup clean out live (firstInputBoundary clean out live v) :=
    (mem_firstInputGroup clean out live _ u).mpr same
  exact class_singleton (firstInputGroup clean out live (firstInputBoundary clean out live v))
    (fun x => vl gs x (firstInputBoundary clean out live v).val) (mono _) v activated
    (boundary_factor clean out live computes _) u member

lemma circuit_representative_cover_of_monotone {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = c7F x)
    (four : (circuitBranchWires (n := 7) gs).card = 4)
    (mono : ∀ cut : Fin (7 + gs.length), Monotone (fun x : Fin 7 → Bool => vl gs x cut.val)) :
    let label := firstInputBoundary clean out live
    (H5C7Cover.earlierCover label).card = 4 ∧
      H5C7Cover.covers (H5C7Cover.earlierCover label) ∧
      (∀ b ∈ circuitBranchWires gs, ∃ v ∈ H5C7Cover.earlierCover label, label v = b ∧
        ∀ u, label u = b → u = v) ∧
      (∀ v, v ∈ H5C7Cover.earlierCover label ↔ label v < out) :=
  circuit_representative_cover clean out live distinct computes four
    (boundary_activeSingleton clean out live computes mono)

end H5C7ActiveSingleton



namespace H5RawC7

open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace PetersenFirstGroup
open H5C7Preview

lemma raw_representative_signals (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    let least := HelperReviewEquality.raw_least C hf hs he
    let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
    let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
      (c7_output_valid least)
    let label := firstInputBoundary least.hcl out live
    let D := H5C7Cover.earlierCover label
    D.card = 4 ∧ H5C7Cover.covers D ∧
      (∀ b ∈ circuitBranchWires C.gates, ∃ v ∈ D, label v = b ∧
        ∀ u, label u = b → u = v) ∧
      (∀ v, v ∈ D ↔ label v < out) ∧
      (∀ v ∈ D, label v < out ∧ (∀ u, label u = label v → u = v) ∧
        vl C.gates (Helper3Signal.singleton v) (label v).val = true ∧
        (∀ u, u ≠ v → vl C.gates (Helper3Signal.singleton u) (label v).val = false) ∧
        Helper3Signal.DependsOnly (fun x => vl C.gates x (label v).val) D) := by
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  let label := firstInputBoundary least.hcl out live
  let D := H5C7Cover.earlierCover label
  change D.card = 4 ∧ H5C7Cover.covers D ∧
    (∀ b ∈ circuitBranchWires C.gates, ∃ v ∈ D, label v = b ∧
      ∀ u, label u = b → u = v) ∧
    (∀ v, v ∈ D ↔ label v < out) ∧
    (∀ v ∈ D, label v < out ∧ (∀ u, label u = label v → u = v) ∧
      vl C.gates (Helper3Signal.singleton v) (label v).val = true ∧
      (∀ u, u ≠ v → vl C.gates (Helper3Signal.singleton u) (label v).val = false) ∧
      Helper3Signal.DependsOnly (fun x => vl C.gates x (label v).val) D)
  have noNot := HelperReview.exact10_cycle7_has_no_not C hf hs he
  have mono (cut : Fin (7 + C.gates.length)) :
      Monotone (fun x : Fin 7 → Bool => vl C.gates x cut.val) :=
    H5WireProperties.vl_monotone least.hcl noNot cut.val
  have four : (circuitBranchWires (n := 7) C.gates).card = 4 := by
    simpa only [HelperReviewEquality.branchValues, Finset.card_map] using
      (HelperReviewEquality.raw_exact_branch_budget C hf hs he).1
  have computes (x : Fin 7 → Bool) : vl C.gates x out.val = c7F x := least.hev x
  have cover := H5C7ActiveSingleton.circuit_representative_cover_of_monotone
    least.hcl out live (predecessors_nodup least c7_nonconstant) computes four mono
  refine ⟨cover.1, cover.2.1, cover.2.2.1, cover.2.2.2, ?_⟩
  intro v hv
  obtain ⟨w, adjacent, earlier⟩ := (H5C7Cover.earlierCover_mem label v).mp hv
  have edge := (H5C7CircuitCover.c7_adjacent_iff v w).mpr adjacent
  have active := H5C7ActiveSingleton.boundary_singleton_activation
    least.hcl out live computes mono v w edge earlier
  have unique := H5C7ActiveSingleton.boundary_activeSingleton
    least.hcl out live computes mono v w edge earlier
  have before : label v < out := (cover.2.2.2 v).mp hv
  have member : v ∈ firstInputGroup least.hcl out live (label v) :=
    (mem_firstInputGroup least.hcl out live (label v) v).mpr rfl
  have others := H5BranchSingleton.other_singletons_false
    (firstInputGroup least.hcl out live (label v))
    (fun x => vl C.gates x (label v).val) (mono _) v member active
    (H5C7ActiveSingleton.boundary_factor least.hcl out live computes (label v))
  have terminal : FirstBranchRoute.Terminal (readEdge C.gates) out (label v) :=
    FirstBranchRoute.first_stops (readEdge C.gates) out (read_order least.hcl) live
      (inputWire C.gates v)
  have supported := Helper3ActualSignal.actual_wire_depends_only least.hcl out live
    (label v) terminal D (fun i prior => (cover.2.2.2 i).mpr (lt_of_le_of_lt prior before))
  exact ⟨before, unique, active, others, supported⟩

end H5RawC7

namespace RootAliasFold
open PEqualNP.CircuitLowerBounds
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

lemma getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

lemma getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]


lemma foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

lemma take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega


lemma getD_oob (w : List Bool) (i : Nat) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

end RootAliasFold



namespace SetFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open RootAliasFold



lemma or_single_value (w : List Bool) (j : ℕ) :
    GateOp.or.eval ([j].map fun k => w.getD k false) = w.getD j false := by
  simp [GateOp.eval]

lemma wire_gate_value (C : Circuit) (p : ℕ) (g : Gate)
    (hp : C.gates[p]? = some g) (w : List Bool) :
    (C.wires w).getD (w.length + p) false =
      g.op.eval (g.inputs.map fun j =>
        ((C.gates.take p).foldl step w).getD j false) := by
  have hpl := (List.getElem?_eq_some_iff.mp hp).1
  have hl := take_fold_length C.gates p hpl w
  rw [wires_eq, foldl_split C.gates p g hp w]
  rw [foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl]
  exact getD_append_singleton_last _ _

lemma set_at_agrees (C : Circuit) (p : ℕ) (g g' : Gate)
    (hp : C.gates[p]? = some g) (w : List Bool)
    (he : g'.op.eval (g'.inputs.map fun j =>
      ((C.gates.take p).foldl step w).getD j false) =
      g.op.eval (g.inputs.map fun j =>
      ((C.gates.take p).foldl step w).getD j false)) :
    (⟨C.gates.set p g', C.output⟩ : Circuit).wires w = C.wires w := by
  have hpl := (List.getElem?_eq_some_iff.mp hp).1
  have hset : (C.gates.set p g')[p]? = some g' := by simp [hpl]
  rw [wires_eq, wires_eq]
  rw [foldl_split _ p g' hset w, foldl_split C.gates p g hp w,
    List.take_set_of_le (le_refl p), List.drop_set_of_lt (Nat.lt_succ_self p)]
  congr 1
  unfold step
  exact congrArg (fun b => ((C.gates.take p).foldl step w) ++ [b]) he


def WLe (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j, a.getD j false = true → b.getD j false = true

lemma eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : WLe a b) :
    g.op.eval (g.inputs.map fun j => a.getD j false) = true →
      g.op.eval (g.inputs.map fun j => b.getD j false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map]
    intro ha v hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact h.2 j (ha _ ⟨j, hj, rfl⟩)
  · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨v, ⟨j, hj, rfl⟩, hv⟩
    exact ⟨b.getD j false, ⟨j, hj, rfl⟩, h.2 j hv⟩

lemma append_le (a b : List Bool) (u v : Bool) (h : WLe a b)
    (huv : u = true → v = true) : WLe (a ++ [u]) (b ++ [v]) := by
  have hlen := h.1
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  rcases Nat.lt_trichotomy j a.length with hlt | heq | hgt
  · rw [getD_append_left a _ j hlt] at hj
    rw [getD_append_left b _ j (by omega)]
    exact h.2 j hj
  · subst heq
    rw [getD_append_singleton_last] at hj
    rw [h.1, getD_append_singleton_last]
    exact huv hj
  · have hz : (a ++ [u]).getD j false = false :=
      getD_oob _ _ (by simp; omega)
    rw [hz] at hj
    contradiction

lemma step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : WLe a b) : WLe (step a g) (step b g) :=
  append_le a b _ _ h (eval_mono g hop a b h)

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, WLe a b → WLe (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _
      (step_mono g (hgs g (by simp)) a b h)

lemma set_gate_order (C : Circuit) (p : ℕ) (g g' : Gate)
    (hp : C.gates[p]? = some g)
    (hmono : ∀ g ∈ C.gates.drop (p + 1), g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool)
    (hv : g'.op.eval (g'.inputs.map fun j =>
        ((C.gates.take p).foldl step w).getD j false) = true →
      g.op.eval (g.inputs.map fun j =>
        ((C.gates.take p).foldl step w).getD j false) = true) :
    WLe ((⟨C.gates.set p g', C.output⟩ : Circuit).wires w) (C.wires w) := by
  have hpl := (List.getElem?_eq_some_iff.mp hp).1
  have hset : (C.gates.set p g')[p]? = some g' := by simp [hpl]
  rw [wires_eq, wires_eq]
  rw [foldl_split _ p g' hset w, foldl_split C.gates p g hp w,
    List.take_set_of_le (le_refl p), List.drop_set_of_lt (Nat.lt_succ_self p)]
  apply fold_mono _ hmono
  exact append_le _ _ _ _ ⟨rfl, fun _ h => h⟩ hv

lemma wire_prefix_value (C : Circuit) (p : ℕ) (hp : p < C.gates.length)
    (w : List Bool) (j : ℕ) (hj : j < w.length + p) :
    (C.wires w).getD j false = ((C.gates.take p).foldl step w).getD j false := by
  rw [wires_eq]
  conv_lhs => rw [← List.take_append_drop p C.gates, List.foldl_append]
  exact foldl_step_getD _ _ _ (by
    rw [take_fold_length C.gates p hp w]
    exact hj)

lemma set_or_agrees (C : Circuit) (p : ℕ) (hp : p < C.gates.length)
    (w : List Bool) (j : ℕ) (hj : j < w.length + p)
    (hv : (C.wires w).getD (w.length + p) false = (C.wires w).getD j false) :
    (⟨C.gates.set p ⟨GateOp.or, [j]⟩, C.output⟩ : Circuit).wires w = C.wires w := by
  have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp
  apply set_at_agrees C p C.gates[p] ⟨GateOp.or, [j]⟩ hg w
  rw [or_single_value]
  rw [← wire_gate_value C p C.gates[p] hg w, ← wire_prefix_value C p hp w j hj]
  exact hv.symm

lemma set_or_order (C : Circuit) (p : ℕ) (hp : p < C.gates.length)
    (hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (j : ℕ) (hj : j < w.length + p)
    (hv : (C.wires w).getD j false = true → (C.wires w).getD (w.length + p) false = true) :
    WLe ((⟨C.gates.set p ⟨GateOp.or, [j]⟩, C.output⟩ : Circuit).wires w) (C.wires w) := by
  have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp
  apply set_gate_order C p C.gates[p] ⟨GateOp.or, [j]⟩ hg
    (fun g h => hmono g (List.mem_of_mem_drop h)) w
  rw [or_single_value]
  rw [← wire_gate_value C p C.gates[p] hg w, ← wire_prefix_value C p hp w j hj]
  exact hv


lemma circuit_monotone (C : Circuit)
    (hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hle : WLe (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro j hxj
    by_cases hj : j < n
    · have hx : (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
        simp [List.getD_eq_getElem?_getD, hj]
      have hy : (List.ofFn y).getD j false = y ⟨j, hj⟩ := by
        simp [List.getD_eq_getElem?_getD, hj]
      rw [hx] at hxj
      rw [hy]
      exact hxy ⟨j, hj⟩ hxj
    · have hz : (List.ofFn x).getD j false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [hz] at hxj
      contradiction
  exact (fold_mono C.gates hmono _ _ hle).2 C.output

lemma set_or_mono_ops (C : Circuit) (p j : ℕ)
    (hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ g ∈ C.gates.set p ⟨GateOp.or, [j]⟩,
      g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with hg | hg
  · exact hmono g hg
  · rw [hg]
    exact Or.inr rfl


end SetFrontier



namespace HelperReview.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open H5C7Preview

def edgeInput (e : Fin 7 × Fin 7) (v : Fin 7) : Bool :=
  decide (v = e.1 ∨ v = e.2)

def Increasing (f : (Fin 7 → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true

lemma edgeInput_true (e : Fin 7 × Fin 7) (he : e ∈ c7Edges) :
    c7F (edgeInput e) = true := by
  apply List.any_eq_true.mpr
  exact ⟨e, he, by simp [edgeInput]⟩

lemma positive_edge_completion (f : (Fin 7 → Bool) → Bool)
    (mono : Increasing f)
    (decreases : ∀ x, f x = true → c7F x = true)
    (edges : ∀ e ∈ c7Edges, f (edgeInput e) = true) : f = c7F := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact decreases x
  · intro hx
    obtain ⟨e, he, hedges⟩ := List.any_eq_true.mp hx
    have hp : x e.1 = true ∧ x e.2 = true := by
      simpa only [Bool.and_eq_true] using hedges
    apply mono (edgeInput e) x ?_ (edges e he)
    intro v hv
    simp only [edgeInput, decide_eq_true_eq] at hv
    rcases hv with rfl | rfl
    · exact hp.1
    · exact hp.2

lemma exact10_binary (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (p : ℕ) (g : Gate) (hg : C.gates[p]? = some g) : g.inputs.length = 2 := by
  have hcg := exact10_cycle7_clean C hf hs he p g hg
  rcases hcg with ⟨hnot, j, hj, hinputs⟩ | ⟨hop, j, k, hj, hk, hinputs⟩
  · exact False.elim (exact10_cycle7_has_no_not C hf hs he g (List.mem_of_getElem? hg) hnot)
  · rw [hinputs]
    rfl

end HelperReview.Frontier



namespace HelperReview.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open H5C7Preview

lemma exact10_and_or (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have hop := (hf g hg).1
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with ha | ho | hn
  · exact Or.inl ha
  · exact Or.inr ho
  · exact False.elim (exact10_cycle7_has_no_not C hf hs he g hg hn)

lemma decreasing_edge_alias_impossible (C : Circuit)
    (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (p : ℕ) (hp : p < C.gates.length) (j : ℕ) (hj : j < 7+p)
    (dominates : ∀ x : Fin 7 → Bool,
      (C.wires (List.ofFn x)).getD j false = true →
      (C.wires (List.ofFn x)).getD (7+p) false = true)
    (edge_agreement : ∀ e ∈ c7Edges,
      (C.wires (List.ofFn (edgeInput e))).getD (7+p) false =
      (C.wires (List.ofFn (edgeInput e))).getD j false) : False := by
  let D : Circuit := ⟨C.gates.set p ⟨GateOp.or, [j]⟩, C.output⟩
  have hmono := exact10_and_or C hf hs he
  have hmonoD : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    SetFrontier.set_or_mono_ops C p j hmono
  have hfD : FanInTwo D := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hold | hreplace
    · exact hf g hold
    · subst g
      constructor
      · simp
      · simp
  have hsD : D.size = 10 := by
    simpa only [D, Circuit.size, List.length_set] using hs
  have hfun : circuitFun 7 C = c7F := by
    funext x
    change C.eval (List.ofFn x) = c7F x
    rw [he x]
    simp [c7F, c7Edges, Bool.or_assoc]

  have hdecreases : ∀ x, circuitFun 7 D x = true → c7F x = true := by
    intro x hx
    have hw := SetFrontier.set_or_order C p hp hmono (List.ofFn x) j
      (by simpa only [List.length_ofFn] using hj)
      (by simpa only [List.length_ofFn] using dominates x)
    have hc : circuitFun 7 C x = true := hw.2 C.output hx
    simpa only [hfun] using hc
  have hedges : ∀ e ∈ c7Edges, circuitFun 7 D (edgeInput e) = true := by
    intro e hE
    have hw := SetFrontier.set_or_agrees C p hp (List.ofFn (edgeInput e)) j
      (by simpa only [List.length_ofFn] using hj)
      (by simpa only [List.length_ofFn] using edge_agreement e hE)
    have hv : circuitFun 7 D (edgeInput e) = circuitFun 7 C (edgeInput e) :=
      congrArg (fun w : List Bool => w.getD C.output false) hw
    rw [hv, hfun]
    exact edgeInput_true e hE
  have hDfun : circuitFun 7 D = c7F :=
    positive_edge_completion (circuitFun 7 D)
      (fun x y hxy => SetFrontier.circuit_monotone D hmonoD 7 x y hxy)
      hdecreases hedges
  have hDC : circuitFun 7 D = circuitFun 7 C := hDfun.trans hfun.symm
  have heD (x : Fin 7 → Bool) := (congrFun hDC x).trans (he x)
  have hpD : D.gates[p]? = some ⟨GateOp.or, [j]⟩ := List.getElem?_set_self hp
  have hbinary := exact10_binary D hfD hsD heD p _ hpD
  simp at hbinary

end HelperReview.Frontier

namespace Helper6ForkSupport

def singletonInput {α : Type*} [DecidableEq α] (v : α) : α → Bool :=
  fun j => decide (j = v)

def pairInput {α : Type*} [DecidableEq α] (p q : α) : α → Bool :=
  fun j => decide (j = p ∨ j = q)

def SupportedOn {α : Type*} (H : (α → Bool) → Bool) (S : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ j ∈ S, x j = y j) → H x = H y

lemma pair_comm {α : Type*} [DecidableEq α] (p q : α) :
    pairInput p q = pairInput q p := by
  funext j
  simp only [pairInput, or_comm]

lemma pair_eq_single_of_left_absent {α : Type*} [DecidableEq α]
    (H : (α → Bool) → Bool) (S : Finset α) (support : SupportedOn H S)
    (p q : α) (absent : p ∉ S) : H (pairInput p q) = H (singletonInput q) := by
  apply support
  intro j present
  have different : j ≠ p := by
    intro eq
    subst j
    exact absent present
  simp [pairInput, singletonInput, different]

lemma pair_eq_single_of_right_absent {α : Type*} [DecidableEq α]
    (H : (α → Bool) → Bool) (S : Finset α) (support : SupportedOn H S)
    (p q : α) (absent : q ∉ S) : H (pairInput p q) = H (singletonInput p) := by
  rw [pair_comm p q]
  exact pair_eq_single_of_left_absent H S support q p absent

lemma pair_true_endpoints_mem {α : Type*} [DecidableEq α]
    (H : (α → Bool) → Bool) (S : Finset α) (support : SupportedOn H S)
    (singletons : ∀ j : α, H (singletonInput j) = false)
    (p q : α) (active : H (pairInput p q) = true) : p ∈ S ∧ q ∈ S := by
  constructor
  · by_contra absent
    have collapse := pair_eq_single_of_left_absent H S support p q absent
    rw [active, singletons q] at collapse
    cases collapse
  · by_contra absent
    have collapse := pair_eq_single_of_right_absent H S support p q absent
    rw [active, singletons p] at collapse
    cases collapse


lemma unique_edge_active {α : Type*} [DecidableEq α]
    (E : α → α → Prop) (D S : Finset α) (p q : α)
    (H : (α → Bool) → Bool) (support : SupportedOn H S)
    (singletons : ∀ j : α, H (singletonInput j) = false) (subset : S ⊆ D)
    (unique : ∀ a ∈ D, ∀ b ∈ D, E a b →
      (a = p ∧ b = q) ∨ (a = q ∧ b = p))
    (someEdge : ∃ a b : α, E a b ∧ H (pairInput a b) = true) :
    H (pairInput p q) = true ∧ p ∈ S ∧ q ∈ S := by
  obtain ⟨a, b, edge, active⟩ := someEdge
  have members := pair_true_endpoints_mem H S support singletons a b active
  rcases unique a (subset members.1) b (subset members.2) edge with forward | backward
  · rcases forward with ⟨rfl, rfl⟩
    exact ⟨active, members⟩
  · rcases backward with ⟨ha, hb⟩
    rw [ha, hb] at active members
    exact ⟨(congrArg H (pair_comm p q)).trans active, members.2, members.1⟩

lemma or_changes {a b : Bool} (changes : (a || b) ≠ a) : a = false ∧ b = true := by
  cases a <;> cases b <;> simp_all

lemma fork_change_unique_edge {α : Type*} [DecidableEq α]
    (E : α → α → Prop) (D S : Finset α) (p q v : α)
    (H : (α → Bool) → Bool) (support : SupportedOn H S)
    (singletons : ∀ j : α, H (singletonInput j) = false) (subset : S ⊆ D)
    (unique : ∀ a ∈ D, ∀ b ∈ D, E a b →
      (a = p ∧ b = q) ∨ (a = q ∧ b = p))
    (changes : ∃ a b : α, E a b ∧
      (pairInput a b v || H (pairInput a b)) ≠ pairInput a b v) :
    H (pairInput p q) = true ∧ p ∈ S ∧ q ∈ S := by
  apply unique_edge_active E D S p q H support singletons subset unique
  obtain ⟨a, b, edge, change⟩ := changes
  exact ⟨a, b, edge, (or_changes change).2⟩

lemma earlier_endpoints {α : Type*} [DecidableEq α]
    (H : (α → Bool) → Bool) (S : Finset α) (support : SupportedOn H S)
    (singletons : ∀ j : α, H (singletonInput j) = false)
    (p q v : α) (label : α → ℕ) (previous : ∀ j ∈ S, label j < label v)
    (active : H (pairInput p q) = true) :
    label p < label v ∧ label q < label v ∧ v ≠ p ∧ v ≠ q := by
  obtain ⟨hp, hq⟩ := pair_true_endpoints_mem H S support singletons p q active
  have beforeP := previous p hp
  have beforeQ := previous q hq
  refine ⟨beforeP, beforeQ, ?_, ?_⟩
  · intro eq
    subst v
    exact Nat.lt_irrefl _ beforeP
  · intro eq
    subst v
    exact Nat.lt_irrefl _ beforeQ

lemma endpoints_not_internal {α : Type*} [DecidableEq α]
    (Internal : α → Prop) (H : α → (α → Bool) → Bool) (S : α → Finset α)
    (p q : α) (label : α → ℕ)
    (support : ∀ v, Internal v → SupportedOn (H v) (S v))
    (singletons : ∀ v, Internal v → ∀ j : α, H v (singletonInput j) = false)
    (previous : ∀ v, Internal v → ∀ j ∈ S v, label j < label v)
    (active : ∀ v, Internal v → H v (pairInput p q) = true) :
    ¬ Internal p ∧ ¬ Internal q := by
  constructor
  · intro internal
    have bound := earlier_endpoints (H p) (S p) (support p internal)
      (singletons p internal) p q p label (previous p internal) (active p internal)
    exact Nat.lt_irrefl _ bound.1
  · intro internal
    have bound := earlier_endpoints (H q) (S q) (support q internal)
      (singletons q internal) p q q label (previous q internal) (active q internal)
    exact Nat.lt_irrefl _ bound.2.1



end Helper6ForkSupport

namespace Root18791Internal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open Helper6ForkSupport

def wire (C : Circuit) (w : Nat) (x : Fin 7 → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value (C : Circuit) (v : Fin 7) (x : Fin 7 → Bool) :
    wire C v.val x = x v := by
  exact PEqualNP.MetaComplexity.Helpers.vl_input C.gates x v.val v.isLt

lemma listed_edge_adjacent : ∀ e ∈ H5C7Preview.c7Edges,
    H5C7Cover.adjacent e.1 e.2 := by decide +kernel

lemma unique_oriented_edge (D : Finset (Fin 7)) (p : Fin 7)
    (unique : ∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p) :
    ∀ a ∈ D, ∀ b ∈ D, H5C7Cover.adjacent a b →
      (a = p ∧ b = p + 1) ∨ (a = p + 1 ∧ b = p) := by
  intro a ha b hb edge
  rcases edge with forward | backward
  · have ap : a = p := (unique a).mp ⟨ha, by simpa only [← forward] using hb⟩
    exact Or.inl ⟨ap, forward.trans (congrArg (fun t : Fin 7 => t + 1) ap)⟩
  · have bp : b = p := (unique b).mp ⟨hb, by simpa only [← backward] using ha⟩
    exact Or.inr ⟨backward.trans (congrArg (fun t : Fin 7 => t + 1) bp), bp⟩

lemma internal_changes_edge (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (cut : Fin (7 + C.gates.length)) (v : Fin 7)
    (internal : 7 ≤ cut.val) (H : (Fin 7 → Bool) → Bool)
    (representation : ∀ x, wire C cut.val x = (x v || H x)) :
    ∃ a b : Fin 7, H5C7Cover.adjacent a b ∧
      (pairInput a b v || H (pairInput a b)) ≠ pairInput a b v := by
  by_contra noChange
  apply HelperReview.Frontier.decreasing_edge_alias_impossible C hf hs he
    (cut.val - 7) (by have := cut.isLt; omega) v.val (by have := v.isLt; omega)
  · intro x yes
    change wire C (7 + (cut.val - 7)) x = true
    rw [show 7 + (cut.val - 7) = cut.val by omega, representation]
    have input : x v = true := by
      change wire C v.val x = true at yes
      simpa only [input_value] using yes
    simp [input]
  · intro e member
    have equal : (pairInput e.1 e.2 v || H (pairInput e.1 e.2)) = pairInput e.1 e.2 v := by
      by_contra different
      exact noChange ⟨e.1, e.2, listed_edge_adjacent e member, different⟩
    change wire C (7 + (cut.val - 7)) (HelperReview.Frontier.edgeInput e) =
      wire C v.val (HelperReview.Frontier.edgeInput e)
    rw [show 7 + (cut.val - 7) = cut.val by omega, representation, input_value]
    exact equal

lemma internal_residual_active (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (D S : Finset (Fin 7)) (p v : Fin 7)
    (cut : Fin (7 + C.gates.length)) (internal : 7 ≤ cut.val)
    (H : (Fin 7 → Bool) → Bool)
    (representation : ∀ x, wire C cut.val x = (x v || H x))
    (support : SupportedOn H S)
    (singletons : ∀ j : Fin 7, H (singletonInput j) = false)
    (subset : S ⊆ D)
    (unique : ∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p) :
    H (pairInput p (p + 1)) = true ∧ p ∈ S ∧ p + 1 ∈ S :=
  fork_change_unique_edge H5C7Cover.adjacent D S p (p + 1) v H support singletons
    subset (unique_oriented_edge D p unique)
    (internal_changes_edge C hf hs he cut v internal H representation)

lemma raw_label_equals_input (C : Circuit) (label : Fin 7 → Fin (7 + C.gates.length))
    (H : Fin 7 → (Fin 7 → Bool) → Bool) (v : Fin 7)
    (representation : ∀ x, wire C (label v).val x = (x v || H v x))
    (raw : (label v).val < 7) :
    label v = PetersenCutTrace.inputWire C.gates v := by
  have active : wire C (label v).val (singletonInput v) = true := by
    rw [representation]
    simp [singletonInput]
  have input := input_value C (⟨(label v).val, raw⟩ : Fin 7) (singletonInput v)
  rw [input] at active
  have index : (⟨(label v).val, raw⟩ : Fin 7) = v := by
    simpa only [singletonInput, decide_eq_true_eq] using active
  have values : (label v).val = v.val := congrArg (fun z : Fin 7 => z.val) index
  exact Fin.ext values

lemma edge_endpoints_are_raw (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (D : Finset (Fin 7)) (p : Fin 7)
    (label : Fin 7 → Fin (7 + C.gates.length))
    (H : Fin 7 → (Fin 7 → Bool) → Bool) (S : Fin 7 → Finset (Fin 7))
    (representation : ∀ v ∈ D, ∀ x, wire C (label v).val x = (x v || H v x))
    (support : ∀ v ∈ D, SupportedOn (H v) (S v))
    (singletons : ∀ v ∈ D, ∀ j : Fin 7, H v (singletonInput j) = false)
    (subset : ∀ v ∈ D, S v ⊆ D)
    (previous : ∀ v ∈ D, ∀ j ∈ S v, label j < label v)
    (unique : ∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p) :
    label p = PetersenCutTrace.inputWire C.gates p ∧
      label (p + 1) = PetersenCutTrace.inputWire C.gates (p + 1) := by
  have endpoints := (unique p).mpr rfl
  have active : ∀ v, v ∈ D ∧ 7 ≤ (label v).val → H v (pairInput p (p + 1)) = true := by
    intro v internal
    exact (internal_residual_active C hf hs he D (S v) p v (label v) internal.2
      (H v) (representation v internal.1) (support v internal.1)
      (singletons v internal.1) (subset v internal.1) unique).1
  have none := endpoints_not_internal
    (fun v => v ∈ D ∧ 7 ≤ (label v).val) H S p (p + 1) (fun v => (label v).val)
    (fun v hv => support v hv.1) (fun v hv => singletons v hv.1)
    (fun v hv j hj => previous v hv.1 j hj) active
  constructor
  · apply raw_label_equals_input C label H p (representation p endpoints.1)
    by_contra h
    exact none.1 ⟨endpoints.1, by omega⟩
  · apply raw_label_equals_input C label H (p + 1) (representation (p + 1) endpoints.2)
    by_contra h
    exact none.2 ⟨endpoints.2, by omega⟩

end Root18791Internal

namespace Root18791ActualInternal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace PetersenFirstGroup Helper3ActualSignal
open Helper6ForkSupport

lemma actual_edge_endpoints_raw (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (clean : CleanL 7 C.gates) (out : Fin (7 + C.gates.length)) (out_eq : out.val = C.output)
    (live : ∀ w : Fin (7 + C.gates.length), w ≠ out → ∃ z, readEdge C.gates w z)
    (D : Finset (Fin 7)) (p : Fin 7)
    (representatives : ∀ v ∈ D,
      firstInputBoundary clean out live v < out ∧
      (∀ u, firstInputBoundary clean out live u = firstInputBoundary clean out live v → u = v) ∧
      vl C.gates (Helper3Signal.singleton v) (firstInputBoundary clean out live v).val = true)
    (before_mem : ∀ v, firstInputBoundary clean out live v < out → v ∈ D)
    (unique : ∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p) :
    firstInputBoundary clean out live p = inputWire C.gates p ∧
      firstInputBoundary clean out live (p + 1) = inputWire C.gates (p + 1) := by
  let label := firstInputBoundary clean out live
  let H (v : Fin 7) := earlierWire clean out live (label v)
  let S (v : Fin 7) := D.filter (fun j => label j < label v)
  have noNot := HelperReview.exact10_cycle7_has_no_not C hf hs he
  have mono (v : Fin 7) : Monotone (fun x : Fin 7 → Bool => vl C.gates x (label v).val) :=
    H5WireProperties.vl_monotone clean noNot _
  have terminal (v : Fin 7) : FirstBranchRoute.Terminal (readEdge C.gates) out (label v) :=
    FirstBranchRoute.first_stops (readEdge C.gates) out (read_order clean) live (inputWire C.gates v)
  have computes (x : Fin 7 → Bool) : vl C.gates x out.val = Helper3Signal.cycle7 x := by
    rw [out_eq]
    exact he x
  apply Root18791Internal.edge_endpoints_are_raw C hf hs he D p label H S
  · intro v hv x
    exact actual_signal_representation clean out live (label v) v (terminal v) rfl
      (representatives v hv).2.1 (mono v) (representatives v hv).2.2 x
  · intro v hv x y agree
    apply actual_earlier_agrees clean out live (label v) x y
    intro j earlier
    apply agree j
    exact Finset.mem_filter.mpr ⟨before_mem j (lt_trans earlier (representatives v hv).1), earlier⟩
  · intro v hv j
    exact actual_cycle7_earlier_singletons_false clean out live (label v) v
      (le_of_lt (representatives v hv).1) (terminal v) rfl (representatives v hv).2.1
      (mono v) (representatives v hv).2.2 computes j
  · intro v hv j hj
    exact (Finset.mem_filter.mp hj).1
  · intro v hv j hj
    exact (Finset.mem_filter.mp hj).2
  · exact unique

lemma actual_internal_residual_active (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (clean : CleanL 7 C.gates) (out : Fin (7 + C.gates.length)) (out_eq : out.val = C.output)
    (live : ∀ w : Fin (7 + C.gates.length), w ≠ out → ∃ z, readEdge C.gates w z)
    (D : Finset (Fin 7)) (p v : Fin 7) (cut : Fin (7 + C.gates.length))
    (atCut : firstInputBoundary clean out live v = cut)
    (before : cut < out)
    (only : ∀ u, firstInputBoundary clean out live u = cut → u = v)
    (active : vl C.gates (Helper3Signal.singleton v) cut.val = true)
    (before_mem : ∀ j, firstInputBoundary clean out live j < out → j ∈ D)
    (unique : ∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p)
    (internal : 7 ≤ cut.val) :
    earlierWire clean out live cut (pairInput p (p + 1)) = true ∧
      firstInputBoundary clean out live p < cut ∧
      firstInputBoundary clean out live (p + 1) < cut := by
  let label := firstInputBoundary clean out live
  let H := earlierWire clean out live cut
  let S := D.filter (fun j => label j < cut)
  have noNot := HelperReview.exact10_cycle7_has_no_not C hf hs he
  have mono : Monotone (fun x : Fin 7 → Bool => vl C.gates x cut.val) :=
    H5WireProperties.vl_monotone clean noNot _
  have terminal : FirstBranchRoute.Terminal (readEdge C.gates) out cut := by
    rw [← atCut]
    exact FirstBranchRoute.first_stops (readEdge C.gates) out (read_order clean) live (inputWire C.gates v)
  have computes (x : Fin 7 → Bool) : vl C.gates x out.val = Helper3Signal.cycle7 x := by
    rw [out_eq]
    exact he x
  have result := Root18791Internal.internal_residual_active C hf hs he D S p v cut internal H
    (actual_signal_representation clean out live cut v terminal atCut only mono active)
    (fun x y agree => actual_earlier_agrees clean out live cut x y (fun j earlier =>
      agree j (Finset.mem_filter.mpr ⟨before_mem j (lt_trans earlier before), earlier⟩)))
    (actual_cycle7_earlier_singletons_false clean out live cut v before.le terminal atCut only mono active computes)
    (fun j hj => (Finset.mem_filter.mp hj).1) unique
  exact ⟨result.1, (Finset.mem_filter.mp result.2.1).2, (Finset.mem_filter.mp result.2.2).2⟩

end Root18791ActualInternal

namespace Root18791RawInternal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace PetersenFirstGroup Helper3ActualSignal H5C7Preview
open Helper6ForkSupport

lemma raw_critical_pair (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    let least := HelperReviewEquality.raw_least C hf hs he
    let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
    let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
      (c7_output_valid least)
    let label := firstInputBoundary least.hcl out live
    let D := H5C7Cover.earlierCover label
    ∃ p : Fin 7,
      (∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p) ∧
      p - 1 ∉ D ∧ p + 2 ∉ D ∧
      label p = inputWire C.gates p ∧ label (p + 1) = inputWire C.gates (p + 1) ∧
      ∀ cut ∈ circuitBranchWires C.gates, 7 ≤ cut.val →
        ∃ v ∈ D, label v = cut ∧
          vl C.gates (pairInput p (p + 1)) cut.val = true ∧
          vl C.gates (singletonInput p) cut.val = false ∧
          vl C.gates (singletonInput (p + 1)) cut.val = false ∧
          label p < cut ∧ label (p + 1) < cut := by
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  let label := firstInputBoundary least.hcl out live
  let D := H5C7Cover.earlierCover label
  have package := H5RawC7.raw_representative_signals C hf hs he
  change D.card = 4 ∧ H5C7Cover.covers D ∧
    (∀ b ∈ circuitBranchWires C.gates, ∃ v ∈ D, label v = b ∧
      ∀ u, label u = b → u = v) ∧
    (∀ v, v ∈ D ↔ label v < out) ∧
    (∀ v ∈ D, label v < out ∧ (∀ u, label u = label v → u = v) ∧
      vl C.gates (Helper3Signal.singleton v) (label v).val = true ∧
      (∀ u, u ≠ v → vl C.gates (Helper3Signal.singleton u) (label v).val = false) ∧
      Helper3Signal.DependsOnly (fun x => vl C.gates x (label v).val) D) at package
  obtain ⟨p, unique, alpha, beta⟩ := H5C7Cover.unique_internal_edge D package.1 package.2.1
  have perRep (v : Fin 7) (hv : v ∈ D) := package.2.2.2.2 v hv
  have representatives : ∀ v ∈ D,
      label v < out ∧ (∀ u, label u = label v → u = v) ∧
      vl C.gates (Helper3Signal.singleton v) (label v).val = true := by
    intro v hv
    exact ⟨(perRep v hv).1, (perRep v hv).2.1, (perRep v hv).2.2.1⟩
  have beforeMem : ∀ v, label v < out → v ∈ D := fun v h => (package.2.2.2.1 v).mpr h
  have raw := Root18791ActualInternal.actual_edge_endpoints_raw C hf hs he least.hcl out rfl live
    D p representatives beforeMem unique
  refine ⟨p, unique, alpha, beta, raw.1, raw.2, ?_⟩
  intro cut branch internal
  obtain ⟨v, hv, atCut, only⟩ := package.2.2.1 cut branch
  have before : cut < out := by rw [← atCut]; exact (perRep v hv).1
  have active : vl C.gates (Helper3Signal.singleton v) cut.val = true := by
    rw [← atCut]
    exact (perRep v hv).2.2.1
  have residual := Root18791ActualInternal.actual_internal_residual_active C hf hs he
    least.hcl out rfl live D p v cut atCut before only active beforeMem unique internal
  have noNot := HelperReview.exact10_cycle7_has_no_not C hf hs he
  have terminal : FirstBranchRoute.Terminal (readEdge C.gates) out cut :=
    Or.inr (in_circuit_branches.mp branch)
  have representation := actual_signal_representation least.hcl out live cut v terminal
    atCut only (H5WireProperties.vl_monotone least.hcl noNot cut.val) active
  have yes : vl C.gates (pairInput p (p + 1)) cut.val = true := by
    rw [representation, residual.1]
    simp
  have np : p ≠ v := by
    intro same
    have h := residual.2.1
    change label p < cut at h
    rw [same, atCut] at h
    exact lt_irrefl _ h
  have nq : p + 1 ≠ v := by
    intro same
    have h := residual.2.2
    change label (p + 1) < cut at h
    rw [same, atCut] at h
    exact lt_irrefl _ h
  have falseP : vl C.gates (singletonInput p) cut.val = false := by
    rw [← atCut]
    exact (perRep v hv).2.2.2.1 p np
  have falseQ : vl C.gates (singletonInput (p + 1)) cut.val = false := by
    rw [← atCut]
    exact (perRep v hv).2.2.2.1 (p + 1) nq
  exact ⟨v, hv, atCut, yes, falseP, falseQ, residual.2⟩

end Root18791RawInternal

def cofactor18791RectangleTwoTable : List Nat :=
  [13961653354498097345, 14829735428352953805, 17433981649933107441, 18446744073675997183]

def cofactor18791RectangleTwoAllowed (m : BitVec 2) (p : BitVec 6) : Bool :=
  (cofactor18791RectangleTwoTable.getD m.toNat 0).testBit p.toNat

def cofactor18791RectangleTwoEntries : List (List (BitVec 6)) :=
  [[0, 6, 7, 32, 38, 39, 40, 46, 47, 48, 54, 55, 56, 62, 63], [0, 2, 3, 6, 7, 8, 10, 11, 14, 15, 32, 34, 35, 38, 39, 40, 42, 43, 46, 47, 48, 50, 51, 54, 55, 56, 58, 59, 62, 63], [0, 4, 5, 6, 7, 16, 20, 21, 22, 23, 32, 36, 37, 38, 39, 40, 44, 45, 46, 47, 48, 52, 53, 54, 55, 56, 60, 61, 62, 63], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]

def cofactor18791RectangleTwoEntriesAt (m : BitVec 2) : List (BitVec 6) :=
  cofactor18791RectangleTwoEntries.getD m.toNat []

def cofactor18791RectangleTwoPairCheck (a b : BitVec 2) : Bool :=
  if a &&& b = 0 then
    (cofactor18791RectangleTwoEntriesAt a).all fun x =>
      (cofactor18791RectangleTwoEntriesAt b).all fun y =>
        cofactor18791RectangleTwoAllowed (a ||| b) (x &&& y) &&
        cofactor18791RectangleTwoAllowed (a ||| b) (x ||| y)
  else true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
lemma cofactor18791_rectangle_two_entries : ∀ a : BitVec 2, ∀ x : BitVec 6,
    cofactor18791RectangleTwoAllowed a x = true ↔ x ∈ cofactor18791RectangleTwoEntriesAt a := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 1000 in
lemma cofactor18791_rectangle_two_pairs : ∀ a b : BitVec 2,
    cofactor18791RectangleTwoPairCheck a b = true := by
  decide +kernel

lemma cofactor18791_rectangle_two_closed : ∀ a b : BitVec 2,
    a &&& b = 0 → ∀ x y : BitVec 6,
    cofactor18791RectangleTwoAllowed a x = true →
    cofactor18791RectangleTwoAllowed b y = true →
    cofactor18791RectangleTwoAllowed (a ||| b) (x &&& y) = true ∧
    cofactor18791RectangleTwoAllowed (a ||| b) (x ||| y) = true := by
  intro a b disjoint x y hx hy
  have checked := cofactor18791_rectangle_two_pairs a b
  simp only [cofactor18791RectangleTwoPairCheck, disjoint, ite_true] at checked
  have xmem := (cofactor18791_rectangle_two_entries a x).mp hx
  have ymem := (cofactor18791_rectangle_two_entries b y).mp hy
  simpa using ((List.all_eq_true.mp ((List.all_eq_true.mp checked) x xmem)) y ymem)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma cofactor18791_rectangle_two_absent : ∀ a : BitVec 2,
    cofactor18791RectangleTwoAllowed a 25 = false := by decide +kernel



lemma cofactor18791_path_forward {m : Nat} (R : Fin m → Fin m → Prop)
    (forward : ∀ {v w}, R v w → v < w) {v w : Fin m}
    (route : Relation.ReflTransGen R v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma cofactor18791_functional_predecessor {m : Nat} (R : Fin m → Fin m → Prop)
    (forward : ∀ {v w}, R v w → v < w) {source a b goal : Fin m}
    (routeA : Relation.ReflTransGen R source a) (edgeA : R a goal)
    (routeB : Relation.ReflTransGen R source b) (edgeB : R b goal)
    (unique : ∀ v, Relation.ReflTransGen R source v →
      ∀ x y, R v x → R v y → x = y) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := unique source Relation.ReflTransGen.refl _ _ stepB edgeA
      subst next
      have increasing := cofactor18791_path_forward R forward later
      exact (not_lt_of_ge increasing (forward edgeB)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := unique source Relation.ReflTransGen.refl _ _ stepA edgeB
        subst nextA
        have increasing := cofactor18791_path_forward R forward laterA
        exact (not_lt_of_ge increasing (forward edgeA)).elim
      have equal := unique source Relation.ReflTransGen.refl _ _ stepA stepB
      subst nextB
      have increase := forward stepA
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      apply ih nextA closer laterA edgeA laterB edgeB
      intro v route x y hx hy
      exact unique v (route.head stepA) x y hx hy

lemma cofactor18791_cut_reachable_not_port {m : Nat} (R : Fin m → Fin m → Prop)
    (ports : Finset (Fin m))
    (noIncoming : ∀ v ∈ ports, ∀ u, ¬ R u v)
    {source v : Fin m} (route : Relation.ReflTransGen R source v) (different : v ≠ source) :
    v ∉ ports := by
  intro port
  rcases route.cases_tail with same | ⟨prior, _, edge⟩
  · exact different same
  · exact noIncoming v port prior edge

lemma cofactor18791_cut_functional {m : Nat} (R : Fin m → Fin m → Prop)
    (ports : Finset (Fin m))
    (noIncoming : ∀ v ∈ ports, ∀ u, ¬ R u v)
    (otherUnique : ∀ v, v ∉ ports → ∀ x y, R v x → R v y → x = y)
    (source : Fin m) (sourceUnique : ∀ x y, R source x → R source y → x = y) :
    ∀ v, Relation.ReflTransGen R source v → ∀ x y, R v x → R v y → x = y := by
  intro v route x y hx hy
  by_cases same : v = source
  · subst v
    exact sourceUnique x y hx hy
  · exact otherUnique v (cofactor18791_cut_reachable_not_port R ports noIncoming route same)
      x y hx hy

lemma cofactor18791_cut_predecessor_disjoint {m : Nat} (R : Fin m → Fin m → Prop)
    (forward : ∀ {v w}, R v w → v < w)
    (ports : Finset (Fin m))
    (noIncoming : ∀ v ∈ ports, ∀ u, ¬ R u v)
    (otherUnique : ∀ v, v ∉ ports → ∀ x y, R v x → R v y → x = y)
    (source : Fin m) (sourceUnique : ∀ x y, R source x → R source y → x = y)
    {a b goal : Fin m} (edgeA : R a goal) (edgeB : R b goal) (different : a ≠ b) :
    ¬ (Relation.ReflTransGen R source a ∧ Relation.ReflTransGen R source b) := by
  rintro ⟨routeA, routeB⟩
  apply different
  exact cofactor18791_functional_predecessor R forward routeA edgeA routeB edgeB
    (cofactor18791_cut_functional R ports noIncoming otherUnique source sourceUnique)

def cofactor18791CutEdge {m : Nat} (raw : Fin m → Fin m → Prop)
    (ports : Finset (Fin m)) (a b : Fin m) : Prop := raw a b ∧ b ∉ ports

def cofactor18791OutputEdge {m : Nat} (raw : Fin m → Fin m → Prop)
    (ports : Finset (Fin m)) (out a b : Fin m) : Prop :=
  cofactor18791CutEdge raw ports a b ∧
    Relation.ReflTransGen (cofactor18791CutEdge raw ports) b out

lemma cofactor18791_output_forward {m : Nat} (raw : Fin m → Fin m → Prop)
    (ports : Finset (Fin m)) (out : Fin m)
    (forward : ∀ {v w}, raw v w → v < w) {v w : Fin m}
    (edge : cofactor18791OutputEdge raw ports out v w) : v < w := forward edge.1.1

lemma cofactor18791_output_no_incoming {m : Nat} (raw : Fin m → Fin m → Prop)
    (ports : Finset (Fin m)) (out : Fin m) :
    ∀ v ∈ ports, ∀ u, ¬ cofactor18791OutputEdge raw ports out u v := by
  intro v port u edge
  exact edge.1.2 port

lemma cofactor18791_output_other_unique {m : Nat} (raw : Fin m → Fin m → Prop)
    (ports : Finset (Fin m)) (out : Fin m)
    (allBranches : ∀ v, (∃ x y, raw v x ∧ raw v y ∧ x ≠ y) → v ∈ ports) :
    ∀ v, v ∉ ports → ∀ x y,
      cofactor18791OutputEdge raw ports out v x →
      cofactor18791OutputEdge raw ports out v y → x = y := by
  intro v notPort x y hx hy
  by_contra different
  exact notPort (allBranches v ⟨x, y, hx.1.1, hy.1.1, different⟩)


noncomputable def cofactor18791ReachMask {m : Nat} (R : Fin m → Fin m → Prop)
    (p q v : Fin m) : BitVec 2 := by
  classical
  exact (if Relation.ReflTransGen R p v then 1 else 0) |||
    (if Relation.ReflTransGen R q v then 2 else 0)

lemma cofactor18791_reach_mask_disjoint {m : Nat} (R : Fin m → Fin m → Prop)
    (p q a b : Fin m)
    (notP : ¬ (Relation.ReflTransGen R p a ∧ Relation.ReflTransGen R p b))
    (notQ : ¬ (Relation.ReflTransGen R q a ∧ Relation.ReflTransGen R q b)) :
    cofactor18791ReachMask R p q a &&& cofactor18791ReachMask R p q b = 0 := by
  classical
  by_cases pa : Relation.ReflTransGen R p a <;>
    by_cases pb : Relation.ReflTransGen R p b <;>
      by_cases qa : Relation.ReflTransGen R q a <;>
        by_cases qb : Relation.ReflTransGen R q b
  all_goals first
    | exact (notP ⟨pa, pb⟩).elim
    | exact (notQ ⟨qa, qb⟩).elim
    | simp [cofactor18791ReachMask, pa, pb, qa, qb]

lemma cofactor18791_reach_at_binary {m : Nat} (R : Fin m → Fin m → Prop)
    (source a b goal : Fin m) (different : goal ≠ source)
    (incoming : ∀ z, R z goal ↔ z = a ∨ z = b) :
    Relation.ReflTransGen R source goal ↔
      Relation.ReflTransGen R source a ∨ Relation.ReflTransGen R source b := by
  constructor
  · intro route
    rcases route.cases_tail with same | ⟨prior, path, edge⟩
    · exact (different same).elim
    · rcases (incoming prior).mp edge with same | same
      · subst prior
        exact Or.inl path
      · subst prior
        exact Or.inr path
  · rintro (path | path)
    · exact path.tail ((incoming a).mpr (Or.inl rfl))
    · exact path.tail ((incoming b).mpr (Or.inr rfl))

lemma cofactor18791_reach_mask_union {m : Nat} (R : Fin m → Fin m → Prop)
    (p q a b goal : Fin m) (notP : goal ≠ p) (notQ : goal ≠ q)
    (incoming : ∀ z, R z goal ↔ z = a ∨ z = b) :
    cofactor18791ReachMask R p q goal =
      cofactor18791ReachMask R p q a ||| cofactor18791ReachMask R p q b := by
  classical
  have reachP := cofactor18791_reach_at_binary R p a b goal notP incoming
  have reachQ := cofactor18791_reach_at_binary R q a b goal notQ incoming
  by_cases pa : Relation.ReflTransGen R p a <;>
    by_cases pb : Relation.ReflTransGen R p b <;>
      by_cases qa : Relation.ReflTransGen R q a <;>
        by_cases qb : Relation.ReflTransGen R q b <;>
          simp [cofactor18791ReachMask, reachP, reachQ, pa, pb, qa, qb]

lemma cofactor18791_output_source_unique_discarded {m : Nat}
    (raw : Fin m → Fin m → Prop) (ports : Finset (Fin m)) (out source dead : Fin m)
    (cap : ∀ a b c, raw source a → raw source b → raw source c →
      a = b ∨ a = c ∨ b = c)
    (readDead : raw source dead)
    (discarded : ¬ cofactor18791OutputEdge raw ports out source dead) :
    ∀ x y, cofactor18791OutputEdge raw ports out source x →
      cofactor18791OutputEdge raw ports out source y → x = y := by
  intro x y hx hy
  rcases cap dead x y readDead hx.1.1 hy.1.1 with equal | equal | equal
  · subst x
    exact (discarded hx).elim
  · subst y
    exact (discarded hy).elim
  · exact equal

lemma cofactor18791_no_path_to_leaf {m : Nat} (R : Fin m → Fin m → Prop)
    (source leaf : Fin m) (different : leaf ≠ source) (noIncoming : ∀ u, ¬ R u leaf) :
    ¬ Relation.ReflTransGen R source leaf := by
  intro route
  rcases route.cases_tail with same | ⟨prior, _, edge⟩
  · exact different same
  · exact noIncoming prior edge

lemma cofactor18791_reach_mask_leaf {m : Nat} (R : Fin m → Fin m → Prop)
    (p q leaf : Fin m) (different : p ≠ q) (noIncoming : ∀ u, ¬ R u leaf) :
    cofactor18791ReachMask R p q leaf =
      if leaf = p then 1 else if leaf = q then 2 else 0 := by
  classical
  by_cases lp : leaf = p
  · subst leaf
    have nq := cofactor18791_no_path_to_leaf R q p different noIncoming
    simp [cofactor18791ReachMask, nq, Relation.ReflTransGen.refl]
  · by_cases lq : leaf = q
    · subst leaf
      have np := cofactor18791_no_path_to_leaf R p q lp noIncoming
      simp [cofactor18791ReachMask, lp, np, Relation.ReflTransGen.refl]
    · have np := cofactor18791_no_path_to_leaf R p leaf lp noIncoming
      have nq := cofactor18791_no_path_to_leaf R q leaf lq noIncoming
      simp [cofactor18791ReachMask, lp, lq, np, nq]


lemma cofactor18791_weight_cap {α : Type} [Fintype α] [DecidableEq α]
    (weight : α → Nat) (total : ∑ i, weight i ≤ 2)
    (a b c : α) (ha : 0 < weight a) (hb : 0 < weight b) (hc : 0 < weight c) :
    a = b ∨ a = c ∨ b = c := by
  by_cases ab : a = b
  · exact Or.inl ab
  by_cases ac : a = c
  · exact Or.inr (Or.inl ac)
  by_cases bc : b = c
  · exact Or.inr (Or.inr bc)
  have three : 3 ≤ ∑ i, weight i := by
    calc
      3 = ∑ i ∈ ({a, b, c} : Finset α), (1 : Nat) := by simp [ab, ac, bc]
      _ ≤ ∑ i ∈ ({a, b, c} : Finset α), weight i := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> omega
      _ ≤ ∑ i, weight i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  omega

lemma cofactor18791_count_flatMap {α : Type} (gs : List α)
    (inputs : α → List Nat) (wire : Nat) :
    (gs.flatMap inputs).count wire = (gs.map fun g => (inputs g).count wire).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.flatMap_cons, List.count_append, ih]

lemma cofactor18791_reader_cap {α : Type} (gs : List α)
    (inputs : α → List Nat) (wire : Nat)
    (count : (gs.flatMap inputs).count wire ≤ 2)
    (a b c : Fin gs.length)
    (ha : wire ∈ inputs (gs.get a)) (hb : wire ∈ inputs (gs.get b))
    (hc : wire ∈ inputs (gs.get c)) : a = b ∨ a = c ∨ b = c := by
  let weight : Fin gs.length → Nat := fun i => (inputs (gs.get i)).count wire
  have listEq : (gs.map fun g => (inputs g).count wire) = List.ofFn weight := by
    symm
    simpa [weight] using List.ofFn_getElem_eq_map gs (fun g => (inputs g).count wire)
  rw [cofactor18791_count_flatMap, listEq, Fin.sum_ofFn] at count
  exact cofactor18791_weight_cap weight count a b c
    (List.count_pos_iff.mpr ha) (List.count_pos_iff.mpr hb) (List.count_pos_iff.mpr hc)

lemma cofactor18791_output_component_impossible {m : Nat}
    (raw : Fin m → Fin m → Prop) (ports : Finset (Fin m))
    (out p q deadP deadQ : Fin m) (profile : Fin m → BitVec 6)
    (forward : ∀ {v w}, raw v w → v < w)
    (allBranches : ∀ v, (∃ x y, raw v x ∧ raw v y ∧ x ≠ y) → v ∈ ports)
    (pPort : p ∈ ports) (qPort : q ∈ ports) (pq : p ≠ q)
    (capP : ∀ a b c, raw p a → raw p b → raw p c → a = b ∨ a = c ∨ b = c)
    (capQ : ∀ a b c, raw q a → raw q b → raw q c → a = b ∨ a = c ∨ b = c)
    (readP : raw p deadP) (readQ : raw q deadQ)
    (discardP : ¬ cofactor18791OutputEdge raw ports out p deadP)
    (discardQ : ¬ cofactor18791OutputEdge raw ports out q deadQ)
    (leaves : ∀ v ∈ ports, cofactor18791RectangleTwoAllowed
      (if v = p then 1 else if v = q then 2 else 0) (profile v) = true)
    (binary : ∀ v, v ∉ ports → ∃ a b, a ≠ b ∧
      (∀ z, raw z v ↔ z = a ∨ z = b) ∧
      (profile v = profile a &&& profile b ∨ profile v = profile a ||| profile b)) :
    profile out ≠ 25 := by
  classical
  let R := cofactor18791OutputEdge raw ports out
  have rForward : ∀ {v w}, R v w → v < w :=
    cofactor18791_output_forward raw ports out forward
  have noIncoming : ∀ v ∈ ports, ∀ u, ¬ R u v :=
    cofactor18791_output_no_incoming raw ports out
  have otherUnique : ∀ v, v ∉ ports → ∀ x y, R v x → R v y → x = y :=
    cofactor18791_output_other_unique raw ports out allBranches
  have uniqueP : ∀ x y, R p x → R p y → x = y :=
    cofactor18791_output_source_unique_discarded raw ports out p deadP capP readP discardP
  have uniqueQ : ∀ x y, R q x → R q y → x = y :=
    cofactor18791_output_source_unique_discarded raw ports out q deadQ capQ readQ discardQ
  have invariant : ∀ v : Fin m,
      Relation.ReflTransGen (cofactor18791CutEdge raw ports) v out →
      cofactor18791RectangleTwoAllowed (cofactor18791ReachMask R p q v) (profile v) = true := by
    intro v
    induction v using (measure (fun w : Fin m => w.val)).wf.induction with
    | h v ih =>
      intro active
      by_cases isPort : v ∈ ports
      · rw [cofactor18791_reach_mask_leaf R p q v pq (noIncoming v isPort)]
        exact leaves v isPort
      · obtain ⟨a, b, different, parents, operation⟩ := binary v isPort
        have incoming : ∀ z, R z v ↔ z = a ∨ z = b := by
          intro z
          constructor
          · intro edge
            exact (parents z).mp edge.1.1
          · intro parent
            exact ⟨⟨(parents z).mpr parent, isPort⟩, active⟩
        have edgeA : R a v := (incoming a).mpr (Or.inl rfl)
        have edgeB : R b v := (incoming b).mpr (Or.inr rfl)
        have activeA : Relation.ReflTransGen (cofactor18791CutEdge raw ports) a out :=
          active.head edgeA.1
        have activeB : Relation.ReflTransGen (cofactor18791CutEdge raw ports) b out :=
          active.head edgeB.1
        have notP : v ≠ p := fun same => isPort (same ▸ pPort)
        have notQ : v ≠ q := fun same => isPort (same ▸ qPort)
        have union := cofactor18791_reach_mask_union R p q a b v notP notQ incoming
        have apartP := cofactor18791_cut_predecessor_disjoint R rForward ports noIncoming
          otherUnique p uniqueP edgeA edgeB different
        have apartQ := cofactor18791_cut_predecessor_disjoint R rForward ports noIncoming
          otherUnique q uniqueQ edgeA edgeB different
        have separate := cofactor18791_reach_mask_disjoint R p q a b apartP apartQ
        have av := ih a (rForward edgeA) activeA
        have bv := ih b (rForward edgeB) activeB
        have closed := cofactor18791_rectangle_two_closed _ _ separate _ _ av bv
        rw [union]
        rcases operation with operation | operation
        · rw [operation]
          exact closed.1
        · rw [operation]
          exact closed.2
  have allowed := invariant out Relation.ReflTransGen.refl
  intro bad
  rw [bad, cofactor18791_rectangle_two_absent] at allowed
  cases allowed

namespace Root18791Profiles

def cycle (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def singleton (v : Fin 7) : Fin 7 → Bool := fun j => decide (j = v)

def rows (D : Finset (Fin 7)) (p : Fin 7) (r : Fin 6) : Fin 7 → Bool :=
  fun j => match r.val with
    | 0 => decide (j = p ∨ j = p + 1)
    | 1 => decide (j ∈ D ∧ j ≠ p + 1)
    | 2 => decide (j ∈ D ∧ j ≠ p)
    | 3 => decide (j = p ∨ j = p - 1)
    | 4 => decide (j = p + 1 ∨ j = p + 2)
    | _ => decide (j = p - 1 ∨ j = p + 2)

def good (D : Finset (Fin 7)) (p : Fin 7) : Prop :=
  D.card = 4 ∧ (∀ i : Fin 7, i ∈ D ∨ i + 1 ∈ D) ∧
    (∀ q : Fin 7, (q ∈ D ∧ q + 1 ∈ D) ↔ q = p)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma row_facts : ∀ D : Finset (Fin 7), ∀ p : Fin 7, good D p →
    p ∈ D ∧ p + 1 ∈ D ∧ p - 1 ∉ D ∧ p + 2 ∉ D ∧
    (∀ r : Fin 6, cycle (rows D p r) = (25 : BitVec 6).getLsbD r.val) ∧
    (∀ j : Fin 7, ∀ r : Fin 6,
      rows D p r j =
        (if j = p then (11 : BitVec 6) else
          if j = p + 1 then 21 else
          if j = p - 1 then 40 else
          if j = p + 2 then 48 else
          if j ∈ D then 6 else 0).getLsbD r.val) := by
  unfold good rows cycle
  decide +kernel

lemma other_branch_rows (D : Finset (Fin 7)) (p v : Fin 7)
    (valid : good D p) (member : v ∈ D) (vp : v ≠ p) (vq : v ≠ p + 1)
    (g : (Fin 7 → Bool) → Bool) (mono : Monotone g)
    (supported : ∀ x y, (∀ j ∈ D, x j = y j) → g x = g y)
    (active : g (singleton v) = true)
    (others : ∀ j, j ≠ v → g (singleton j) = false) :
    ∃ b : BitVec 6, (b = 6 ∨ b = 7) ∧
      ∀ r : Fin 6, g (rows D p r) = b.getLsbD r.val := by
  obtain ⟨pmem, qmem, alpha, beta, targets, values⟩ := row_facts D p valid
  have zero : g (fun _ => false) = false := by
    have bound := mono (show (fun _ : Fin 7 => false) ≤ singleton p from fun _ => Bool.false_le _)
    rw [others p (Ne.symm vp)] at bound
    exact le_antisymm bound (Bool.false_le _)
  have one : g (rows D p 1) = true := by
    apply Bool.le_iff_imp.mp (mono ?_) active
    intro j
    by_cases eq : j = v
    · subst j
      simp [singleton, rows, member, vq]
    · simp [singleton, eq]
  have two : g (rows D p 2) = true := by
    apply Bool.le_iff_imp.mp (mono ?_) active
    intro j
    by_cases eq : j = v
    · subst j
      simp [singleton, rows, member, vp]
    · simp [singleton, eq]
  have three : g (rows D p 3) = false := by
    rw [supported (rows D p 3) (singleton p) ?_, others p (Ne.symm vp)]
    intro j hj
    have ne : j ≠ p - 1 := fun e => alpha (e ▸ hj)
    simp [rows, singleton, ne]
  have four : g (rows D p 4) = false := by
    rw [supported (rows D p 4) (singleton (p + 1)) ?_, others (p + 1) (Ne.symm vq)]
    intro j hj
    have ne : j ≠ p + 2 := fun e => beta (e ▸ hj)
    simp [rows, singleton, ne]
  have five : g (rows D p 5) = false := by
    rw [supported (rows D p 5) (fun _ => false) ?_, zero]
    intro j hj
    have na : j ≠ p - 1 := fun e => alpha (e ▸ hj)
    have nb : j ≠ p + 2 := fun e => beta (e ▸ hj)
    simp [rows, na, nb]
  cases first : g (rows D p 0)
  · refine ⟨6, Or.inl rfl, ?_⟩
    intro r
    fin_cases r <;> first | exact first | exact one | exact two | exact three | exact four | exact five
  · refine ⟨7, Or.inr rfl, ?_⟩
    intro r
    fin_cases r <;> first | exact first | exact one | exact two | exact three | exact four | exact five





end Root18791Profiles

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace

def cofactor18791Pack (f : Fin 6 → Bool) : BitVec 6 :=
  BitVec.ofNat 6 (∑ k : Fin 6, if f k then 2 ^ k.val else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 1000 in
lemma cofactor18791_pack_bit (f : Fin 6 → Bool) (k : Fin 6) :
    (cofactor18791Pack f).getLsbD k.val = f k := by
  have finite : ∀ f : Fin 6 → Bool, ∀ k : Fin 6,
      (cofactor18791Pack f).getLsbD k.val = f k := by decide +kernel
  exact finite f k

def cofactor18791WireProfile (gs : List Gate) (D : Finset (Fin 7)) (p : Fin 7)
    (w : Fin (7 + gs.length)) : BitVec 6 :=
  cofactor18791Pack fun r => vl gs (Root18791Profiles.rows D p r) w.val

lemma cofactor18791_wire_profile_bit (gs : List Gate) (D : Finset (Fin 7)) (p : Fin 7)
    (w : Fin (7 + gs.length)) (k : Nat) (hk : k < 6) :
    (cofactor18791WireProfile gs D p w).getLsbD k =
      vl gs (Root18791Profiles.rows D p ⟨k, hk⟩) w.val :=
  cofactor18791_pack_bit _ ⟨k, hk⟩

noncomputable def cofactor18791CircuitPorts (gs : List Gate) : Finset (Fin (7 + gs.length)) := by
  classical
  exact Finset.univ.filter fun w => w.val < 7 ∨ w ∈ circuitBranchWires gs

lemma cofactor18791_circuit_port_mem (gs : List Gate) (w : Fin (7 + gs.length)) :
    w ∈ cofactor18791CircuitPorts gs ↔ w.val < 7 ∨
      FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [cofactor18791CircuitPorts, in_circuit_branches]

lemma cofactor18791_circuit_all_branches (gs : List Gate) :
    ∀ v, (∃ x y, readEdge gs v x ∧ readEdge gs v y ∧ x ≠ y) →
      v ∈ cofactor18791CircuitPorts gs := by
  intro v branch
  exact (cofactor18791_circuit_port_mem gs v).mpr (Or.inr branch)

lemma cofactor18791_input_is_port (gs : List Gate) (v : Fin 7) :
    inputWire gs v ∈ cofactor18791CircuitPorts gs := by
  apply (cofactor18791_circuit_port_mem gs _).mpr
  exact Or.inl v.isLt

lemma cofactor18791_circuit_binary (gs : List Gate) (clean : CleanL 7 gs)
    (noNot : ∀ g ∈ gs, g.op ≠ GateOp.not)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (D : Finset (Fin 7)) (p : Fin 7) :
    ∀ v, v ∉ cofactor18791CircuitPorts gs → ∃ a b, a ≠ b ∧
      (∀ z, readEdge gs z v ↔ z = a ∨ z = b) ∧
      (cofactor18791WireProfile gs D p v =
          cofactor18791WireProfile gs D p a &&& cofactor18791WireProfile gs D p b ∨
        cofactor18791WireProfile gs D p v =
          cofactor18791WireProfile gs D p a ||| cofactor18791WireProfile gs D p b) := by
  intro v notPort
  have internal : 7 ≤ v.val := by
    by_contra notInternal
    exact notPort ((cofactor18791_circuit_port_mem gs v).mpr (Or.inl (by omega)))
  let slot := v.val - 7
  have slotBound : slot < gs.length := by have := v.isLt; dsimp [slot]; omega
  let g := gs[slot]'slotBound
  have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem slotBound
  have wire : v.val = 7 + slot := by dsimp [slot]; omega
  rcases clean slot g atSlot with notGate | ⟨operation, a, b, ab, bb, inputs⟩
  · exact (noNot g (List.getElem_mem slotBound) notGate.1).elim
  have gateDistinct : g.inputs.Nodup := by
    rw [← predecessors_val_gate clean v atSlot wire]
    exact (distinct v).map Fin.val_injective
  have separate : a ≠ b := by simpa [inputs] using gateDistinct
  let av : Fin (7 + gs.length) := ⟨a, by omega⟩
  let bv : Fin (7 + gs.length) := ⟨b, by omega⟩
  have parents : ∀ z, readEdge gs z v ↔ z = av ∨ z = bv := by
    intro z
    constructor
    · rintro ⟨other, gate, atOther, otherWire, member⟩
      have same : other = slot := by omega
      subst other
      have gates : gate = g := Option.some.inj (atOther.symm.trans atSlot)
      subst gate
      rw [inputs] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member
      · exact Or.inl (Fin.ext member)
      · exact Or.inr (Fin.ext member)
    · rintro (same | same)
      · subst z
        exact ⟨slot, g, atSlot, wire, by simp [inputs, av]⟩
      · subst z
        exact ⟨slot, g, atSlot, wire, by simp [inputs, bv]⟩
  refine ⟨av, bv, fun same => separate (congrArg Fin.val same), parents, ?_⟩
  rcases operation with operation | operation
  · left
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_and, cofactor18791_wire_profile_bit gs D p v k hk,
      cofactor18791_wire_profile_bit gs D p av k hk,
      cofactor18791_wire_profile_bit gs D p bv k hk]
    rw [wire, vl_gate gs clean _ slot g atSlot]
    simp [operation, inputs, GateOp.eval, av, bv]
  · right
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_or, cofactor18791_wire_profile_bit gs D p v k hk,
      cofactor18791_wire_profile_bit gs D p av k hk,
      cofactor18791_wire_profile_bit gs D p bv k hk]
    rw [wire, vl_gate gs clean _ slot g atSlot]
    simp [operation, inputs, GateOp.eval, av, bv]

lemma cofactor18791_circuit_reader_cap (gs : List Gate)
    (source : Fin (7 + gs.length))
    (count : (gs.flatMap Gate.inputs).count source.val ≤ 2) :
    ∀ a b c : Fin (7 + gs.length), readEdge gs source a →
      readEdge gs source b → readEdge gs source c → a = b ∨ a = c ∨ b = c := by
  intro a b c readA readB readC
  obtain ⟨ia, ga, atA, wireA, memA⟩ := readA
  obtain ⟨ib, gb, atB, wireB, memB⟩ := readB
  obtain ⟨ic, gc, atC, wireC, memC⟩ := readC
  let ai : Fin gs.length := ⟨ia, (List.getElem?_eq_some_iff.mp atA).1⟩
  let bi : Fin gs.length := ⟨ib, (List.getElem?_eq_some_iff.mp atB).1⟩
  let ci : Fin gs.length := ⟨ic, (List.getElem?_eq_some_iff.mp atC).1⟩
  have eqA : gs.get ai = ga := by simpa [ai] using (List.getElem?_eq_some_iff.mp atA).2
  have eqB : gs.get bi = gb := by simpa [bi] using (List.getElem?_eq_some_iff.mp atB).2
  have eqC : gs.get ci = gc := by simpa [ci] using (List.getElem?_eq_some_iff.mp atC).2
  have cap := cofactor18791_reader_cap gs Gate.inputs source.val count ai bi ci
    (by change source.val ∈ (gs.get ai).inputs; rw [eqA]; exact memA)
    (by change source.val ∈ (gs.get bi).inputs; rw [eqB]; exact memB)
    (by change source.val ∈ (gs.get ci).inputs; rw [eqC]; exact memC)
  rcases cap with same | same | same
  · left
    apply Fin.ext
    have eq := congrArg Fin.val same
    dsimp [ai, bi] at eq
    omega
  · right; left
    apply Fin.ext
    have eq := congrArg Fin.val same
    dsimp [ai, ci] at eq
    omega
  · right; right
    apply Fin.ext
    have eq := congrArg Fin.val same
    dsimp [bi, ci] at eq
    omega

lemma cofactor18791_circuit_target_profile (gs : List Gate) (D : Finset (Fin 7))
    (p : Fin 7) (out : Fin (7 + gs.length))
    (valid : Root18791Profiles.good D p)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = Root18791Profiles.cycle x) :
    cofactor18791WireProfile gs D p out = 25 := by
  have rows := (Root18791Profiles.row_facts D p valid).2.2.2.2.1
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [cofactor18791_wire_profile_bit gs D p out k hk, computes]
  exact rows ⟨k, hk⟩

lemma cofactor18791_circuit_output_impossible (gs : List Gate) (clean : CleanL 7 gs)
    (noNot : ∀ g ∈ gs, g.op ≠ GateOp.not)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (D : Finset (Fin 7)) (p : Fin 7) (out deadP deadQ : Fin (7 + gs.length))
    (valid : Root18791Profiles.good D p)
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = Root18791Profiles.cycle x)
    (countP : (gs.flatMap Gate.inputs).count p.val ≤ 2)
    (countQ : (gs.flatMap Gate.inputs).count (p + 1).val ≤ 2)
    (readP : readEdge gs (inputWire gs p) deadP)
    (readQ : readEdge gs (inputWire gs (p + 1)) deadQ)
    (discardP : ¬ cofactor18791OutputEdge (readEdge gs) (cofactor18791CircuitPorts gs)
      out (inputWire gs p) deadP)
    (discardQ : ¬ cofactor18791OutputEdge (readEdge gs) (cofactor18791CircuitPorts gs)
      out (inputWire gs (p + 1)) deadQ)
    (leaves : ∀ w ∈ cofactor18791CircuitPorts gs, cofactor18791RectangleTwoAllowed
      (if w = inputWire gs p then 1 else if w = inputWire gs (p + 1) then 2 else 0)
      (cofactor18791WireProfile gs D p w) = true) : False := by
  have pq : inputWire gs p ≠ inputWire gs (p + 1) := by
    intro eq
    have vals := congrArg Fin.val eq
    change p.val = (p + 1).val at vals
    have same : p = p + 1 := Fin.ext vals
    have impossible : ∀ p : Fin 7, p ≠ p + 1 := by decide +kernel
    exact impossible p same
  have forbidden := cofactor18791_output_component_impossible
    (readEdge gs) (cofactor18791CircuitPorts gs) out
    (inputWire gs p) (inputWire gs (p + 1)) deadP deadQ
    (cofactor18791WireProfile gs D p) (read_order clean)
    (cofactor18791_circuit_all_branches gs)
    (cofactor18791_input_is_port gs p) (cofactor18791_input_is_port gs (p + 1)) pq
    (cofactor18791_circuit_reader_cap gs (inputWire gs p) countP)
    (cofactor18791_circuit_reader_cap gs (inputWire gs (p + 1)) countQ)
    readP readQ discardP discardQ leaves
    (cofactor18791_circuit_binary gs clean noNot distinct D p)
  exact forbidden (cofactor18791_circuit_target_profile gs D p out valid computes)

namespace Root18791Profiles

lemma allowed_ordinary (b : BitVec 6)
    (hb : b = 0 ∨ b = 6 ∨ b = 7 ∨ b = 40 ∨ b = 48) :
    cofactor18791RectangleTwoAllowed 0 b = true := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma port_profiles_allowed {m : Nat}
    (input label : Fin 7 → Fin m) (ports branches : Finset (Fin m))
    (D : Finset (Fin 7)) (p : Fin 7) (valid : good D p)
    (signal : Fin m → (Fin 7 → Bool) → Bool) (profile : Fin m → BitVec 6)
    (bits : ∀ w, ∀ r : Fin 6, (profile w).getLsbD r.val = signal w (rows D p r))
    (inputSignal : ∀ i x, signal (input i) x = x i)
    (portKind : ∀ w ∈ ports, (∃ i, w = input i) ∨ w ∈ branches)
    (representatives : ∀ w ∈ branches, ∃ v ∈ D, label v = w)
    (pRaw : label p = input p) (qRaw : label (p + 1) = input (p + 1))
    (mono : ∀ w ∈ branches, Monotone (signal w))
    (supported : ∀ w ∈ branches, ∀ x y, (∀ j ∈ D, x j = y j) → signal w x = signal w y)
    (active : ∀ v ∈ D, signal (label v) (singleton v) = true)
    (others : ∀ v ∈ D, ∀ j, j ≠ v → signal (label v) (singleton j) = false) :
    ∀ w ∈ ports, cofactor18791RectangleTwoAllowed
      (if w = input p then 1 else if w = input (p + 1) then 2 else 0) (profile w) = true := by
  have values := (row_facts D p valid).2.2.2.2.2
  have rawProfile (i : Fin 7) : profile (input i) =
      if i = p then 11 else if i = p + 1 then 21 else
      if i = p - 1 then 40 else if i = p + 2 then 48 else if i ∈ D then 6 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [bits (input i) ⟨k, hk⟩, inputSignal]
    exact values i ⟨k, hk⟩
  have pq : p + 1 ≠ p := by
    have checked : ∀ t : Fin 7, t + 1 ≠ t := by decide +kernel
    exact checked p
  intro w hw
  by_cases wp : w = input p
  · subst w
    rw [if_pos rfl, rawProfile p, if_pos rfl]
    decide +kernel
  by_cases wq : w = input (p + 1)
  · subst w
    rw [if_neg wp, if_pos rfl, rawProfile (p + 1), if_neg pq, if_pos rfl]
    decide +kernel
  rw [if_neg wp, if_neg wq]
  rcases portKind w hw with ⟨i, wi⟩ | branch
  · subst w
    have ip : i ≠ p := fun same => wp (congrArg input same)
    have iq : i ≠ p + 1 := fun same => wq (congrArg input same)
    rw [rawProfile i, if_neg ip, if_neg iq]
    apply allowed_ordinary
    split_ifs <;> simp
  · obtain ⟨v, hv, vw⟩ := representatives w branch
    have vp : v ≠ p := by
      intro same
      subst v
      exact wp (vw.symm.trans pRaw)
    have vq : v ≠ p + 1 := by
      intro same
      subst v
      exact wq (vw.symm.trans qRaw)
    have av : signal w (singleton v) = true := by simpa only [vw] using active v hv
    have ov : ∀ j, j ≠ v → signal w (singleton j) = false := by
      simpa only [vw] using others v hv
    obtain ⟨b, hb, evaluations⟩ := other_branch_rows D p v valid hv vp vq
      (signal w) (mono w branch) (supported w branch) av ov
    have eq : profile w = b := by
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [bits w ⟨k, hk⟩]
      exact evaluations ⟨k, hk⟩
    rw [eq]
    apply allowed_ordinary
    rcases hb with hb | hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hb))

end Root18791Profiles

open PEqualNP.Outside.L_meta_1549_aux

lemma root18791_cut_path_avoids {m : Nat} (raw : Fin m → Fin m → Prop)
    (ports : Finset (Fin m)) (start cut : Fin m)
    (startOutside : start ∉ ports) (cutInside : cut ∈ ports)
    {finish : Fin m} (route : Relation.ReflTransGen (cofactor18791CutEdge raw ports) start finish) :
    Relation.ReflTransGen (FirstBranchRoute.Avoid raw cut) start finish ∧ finish ∉ ports := by
  induction route with
  | refl => exact ⟨Relation.ReflTransGen.refl, startOutside⟩
  | tail _ edge ih =>
    refine ⟨ih.1.tail ⟨edge.1, ?_⟩, edge.2⟩
    intro same
    exact ih.2 (same ▸ cutInside)

lemma root18791_first_before_discarded {m : Nat} (raw : Fin m → Fin m → Prop)
    (out source dead : Fin m) (ports : Finset (Fin m))
    (forward : ∀ {v w}, raw v w → v < w)
    (live : ∀ v, v ≠ out → ∃ w, raw v w)
    (allBranches : ∀ v, FirstBranchRoute.Branches raw v → v ∈ ports)
    (before : FirstBranchRoute.first raw out forward live dead < out) :
    ¬ cofactor18791OutputEdge raw ports out source dead := by
  intro edge
  have terminal := FirstBranchRoute.first_stops raw out forward live dead
  have inPort : FirstBranchRoute.first raw out forward live dead ∈ ports := by
    rcases terminal with atOut | branch
    · exact (ne_of_lt before atOut).elim
    · exact allBranches _ branch
  have path := (root18791_cut_path_avoids raw ports dead
    (FirstBranchRoute.first raw out forward live dead) edge.1.2 inPort edge.2).1
  exact FirstBranchRoute.no_avoiding_after raw out forward live before path

namespace PEqualNP.Outside.L_meta_1549_aux.PetersenCutTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers Relation

lemma sensitive_input_ancestor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (w : Fin (n + gs.length)) (i : Fin n) (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j)
    (changes : vl gs x w.val ≠ vl gs y w.val) :
    ReflTransGen (readEdge gs) (inputWire gs i) w := by
  by_contra noPath
  apply changes
  apply agree_on_input_ancestors clean
  intro j path
  apply same
  intro eq
  subst j
  exact noPath path

lemma sensitive_input_first_successor {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (w : Fin (n + gs.length)) (internal : n ≤ w.val)
    (i : Fin n) (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j)
    (changes : vl gs x w.val ≠ vl gs y w.val) :
    ∃ c, readEdge gs (inputWire gs i) c ∧ ReflTransGen (readEdge gs) c w := by
  have path := sensitive_input_ancestor clean w i x y same changes
  rcases path.cases_head with here | ⟨c, first, rest⟩
  · have eq : i.val = w.val := congrArg Fin.val here
    have bound := i.isLt
    omega
  · exact ⟨c, first, rest⟩

lemma sensitive_input_consumed_successor {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out w : Fin (n + gs.length))
    (live : ∀ v, v ≠ out → ∃ z, readEdge gs v z)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out w)
    (internal : n ≤ w.val) (before : w < out)
    (i : Fin n) (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j)
    (changes : vl gs x w.val ≠ vl gs y w.val) :
    ∃ c, readEdge gs (inputWire gs i) c ∧
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live c < out := by
  obtain ⟨c, edge, path⟩ := sensitive_input_first_successor clean w internal i x y same changes
  exact ⟨c, edge, lt_of_le_of_lt
    (FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path terminal)
    before⟩



end PEqualNP.Outside.L_meta_1549_aux.PetersenCutTrace

namespace Root18791NoSharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace PetersenFirstGroup H5C7Preview

lemma no_internal_branches (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    ∀ cut ∈ circuitBranchWires (n := 7) C.gates, cut.val < 7 := by
  classical
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  let label := firstInputBoundary least.hcl out live
  let D := H5C7Cover.earlierCover label
  have package := H5RawC7.raw_representative_signals C hf hs he
  change D.card = 4 ∧ H5C7Cover.covers D ∧
    (∀ b ∈ circuitBranchWires C.gates, ∃ v ∈ D, label v = b ∧
      ∀ u, label u = b → u = v) ∧
    (∀ v, v ∈ D ↔ label v < out) ∧
    (∀ v ∈ D, label v < out ∧ (∀ u, label u = label v → u = v) ∧
      vl C.gates (Helper3Signal.singleton v) (label v).val = true ∧
      (∀ u, u ≠ v → vl C.gates (Helper3Signal.singleton u) (label v).val = false) ∧
      Helper3Signal.DependsOnly (fun x => vl C.gates x (label v).val) D) at package
  have critical := Root18791RawInternal.raw_critical_pair C hf hs he
  change ∃ p : Fin 7,
    (∀ r : Fin 7, (r ∈ D ∧ r + 1 ∈ D) ↔ r = p) ∧
    p - 1 ∉ D ∧ p + 2 ∉ D ∧
    label p = inputWire C.gates p ∧ label (p + 1) = inputWire C.gates (p + 1) ∧
    ∀ cut ∈ circuitBranchWires C.gates, 7 ≤ cut.val →
      ∃ v ∈ D, label v = cut ∧
        vl C.gates (Helper6ForkSupport.pairInput p (p + 1)) cut.val = true ∧
        vl C.gates (Helper6ForkSupport.singletonInput p) cut.val = false ∧
        vl C.gates (Helper6ForkSupport.singletonInput (p + 1)) cut.val = false ∧
        label p < cut ∧ label (p + 1) < cut at critical
  obtain ⟨p, unique, alpha, beta, pRaw, qRaw, internalSignals⟩ := critical
  have valid : Root18791Profiles.good D p := ⟨package.1, package.2.1, unique⟩
  have noNot := HelperReview.exact10_cycle7_has_no_not C hf hs he
  have mono (w : Fin (7 + C.gates.length)) :
      Monotone (fun x : Fin 7 → Bool => vl C.gates x w.val) :=
    H5WireProperties.vl_monotone least.hcl noNot w.val
  have leaves : ∀ w ∈ cofactor18791CircuitPorts C.gates,
      cofactor18791RectangleTwoAllowed
        (if w = inputWire C.gates p then 1 else if w = inputWire C.gates (p + 1) then 2 else 0)
        (cofactor18791WireProfile C.gates D p w) = true := by
    apply Root18791Profiles.port_profiles_allowed (inputWire C.gates) label
      (cofactor18791CircuitPorts C.gates) (circuitBranchWires C.gates) D p valid
      (fun w x => vl C.gates x w.val) (cofactor18791WireProfile C.gates D p)
    · intro w r
      exact cofactor18791_wire_profile_bit C.gates D p w r.val r.isLt
    · intro i x
      exact vl_input C.gates x i.val i.isLt
    · intro w hw
      rcases (cofactor18791_circuit_port_mem C.gates w).mp hw with primary | branch
      · exact Or.inl ⟨⟨w.val, primary⟩, Fin.ext rfl⟩
      · exact Or.inr (in_circuit_branches.mpr branch)
    · intro w hw
      obtain ⟨v, hv, atW, only⟩ := package.2.2.1 w hw
      exact ⟨v, hv, atW⟩
    · exact pRaw
    · exact qRaw
    · intro w _
      exact mono w
    · intro w hw x y agree
      obtain ⟨v, hv, atW, only⟩ := package.2.2.1 w hw
      rw [← atW]
      exact (package.2.2.2.2 v hv).2.2.2.2 x y agree
    · intro v hv
      exact (package.2.2.2.2 v hv).2.2.1
    · intro v hv
      exact (package.2.2.2.2 v hv).2.2.2.1
  have counts := (HelperReviewEquality.raw_exact_branch_budget C hf hs he).2.2.2
  have count_le (j : Nat) : (C.gates.flatMap Gate.inputs).count j ≤ 2 := by
    change (operands C.gates).count j ≤ 2
    by_cases present : j ∈ operands C.gates
    · rw [counts j (List.mem_toFinset.mpr present)]
      split_ifs <;> omega
    · simp [List.count_eq_zero.mpr present]
  intro cut branch
  by_contra notRaw
  have internal : 7 ≤ cut.val := by omega
  obtain ⟨v, hv, atCut, yes, noP, noQ, pBefore, qBefore⟩ := internalSignals cut branch internal
  have before : cut < out := by rw [← atCut]; exact (package.2.2.2.2 v hv).1
  have terminal : FirstBranchRoute.Terminal (readEdge C.gates) out cut :=
    Or.inr (in_circuit_branches.mp branch)
  have sameP : ∀ j : Fin 7, j ≠ p →
      Helper6ForkSupport.pairInput p (p + 1) j = Helper6ForkSupport.singletonInput (p + 1) j := by
    intro j hj
    simp [Helper6ForkSupport.pairInput, Helper6ForkSupport.singletonInput, hj]
  have sameQ : ∀ j : Fin 7, j ≠ p + 1 →
      Helper6ForkSupport.pairInput p (p + 1) j = Helper6ForkSupport.singletonInput p j := by
    intro j hj
    simp [Helper6ForkSupport.pairInput, Helper6ForkSupport.singletonInput, hj]
  obtain ⟨deadP, readP, consumedP⟩ := sensitive_input_consumed_successor least.hcl out cut live
    terminal internal before p _ _ sameP (by rw [yes, noQ]; decide)
  obtain ⟨deadQ, readQ, consumedQ⟩ := sensitive_input_consumed_successor least.hcl out cut live
    terminal internal before (p + 1) _ _ sameQ (by rw [yes, noP]; decide)
  exact cofactor18791_circuit_output_impossible C.gates least.hcl noNot
    (predecessors_nodup least c7_nonconstant) D p out deadP deadQ valid
    (fun x => he x) (count_le p.val) (count_le (p + 1).val) readP readQ
    (root18791_first_before_discarded (readEdge C.gates) out (inputWire C.gates p) deadP
      (cofactor18791CircuitPorts C.gates) (read_order least.hcl) live
      (cofactor18791_circuit_all_branches C.gates) consumedP)
    (root18791_first_before_discarded (readEdge C.gates) out (inputWire C.gates (p + 1)) deadQ
      (cofactor18791CircuitPorts C.gates) (read_order least.hcl) live
      (cofactor18791_circuit_all_branches C.gates) consumedQ) leaves

end Root18791NoSharing

namespace PEqualNP.Outside.L_meta_1549_aux.PetersenCutTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers Relation

lemma read_path_to_primary_eq {n : Nat} {gs : List Gate}
    {a b : Fin (n + gs.length)} (path : ReflTransGen (readEdge gs) a b)
    (primary : b.val < n) : a = b := by
  induction path with
  | refl => rfl
  | tail _ edge _ =>
    obtain ⟨p, g, hp, hb, mem⟩ := edge
    omega

lemma primary_first_boundary_eq {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ v, v ≠ out → ∃ z, readEdge gs v z) (i : Fin n)
    (primary : (PetersenFirstGroup.firstInputBoundary clean out live i).val < n) :
    PetersenFirstGroup.firstInputBoundary clean out live i = inputWire gs i := by
  have path := FirstBranchRoute.follows_is_read_path (readEdge gs) out
    (FirstBranchRoute.first_path (readEdge gs) out (read_order clean) live (inputWire gs i))
  exact (read_path_to_primary_eq path primary).symm

end PEqualNP.Outside.L_meta_1549_aux.PetersenCutTrace


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers.Readers
open PetersenCutTrace PetersenFirstGroup H5C7Preview

lemma cofactor18791_output_last (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) : C.output = 16 := by
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  have size : C.gates.length = 10 := hs
  let last : Fin (7 + C.gates.length) := ⟨16, by omega⟩
  have bound := wire_le_output least.hcl out live last
  change 16 ≤ C.output at bound
  have valid := c7_output_valid least
  omega

lemma cofactor18791_operand_before_output (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    ∀ w ∈ operands C.gates, w < C.output := by
  let least := HelperReviewEquality.raw_least C hf hs he
  have last := cofactor18791_output_last C hf hs he
  have size : C.gates.length = 10 := hs
  intro w member
  obtain ⟨g, gmem, wg⟩ := List.mem_flatMap.mp member
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp gmem
  have before := (least.hcl slot g atSlot).lt w wg
  have slotBound := (List.getElem?_eq_some_iff.mp atSlot).1
  omega

lemma cofactor18791_internal_counts (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    ∀ j, 7 ≤ j → j < 7 + C.gates.length →
      (operands C.gates).count j = if j = C.output then 0 else 1 := by
  classical
  let least := HelperReviewEquality.raw_least C hf hs he
  have counts := (HelperReviewEquality.raw_exact_branch_budget C hf hs he).2.2.2
  have used := least_wire_used least c7_nonconstant c7_depends c7_restrict_nonconstant
  have raw := Root18791NoSharing.no_internal_branches C hf hs he
  intro j internal bound
  by_cases output : j = C.output
  · rw [if_pos output]
    apply List.count_eq_zero.mpr
    intro member
    have before := cofactor18791_operand_before_output C hf hs he j member
    omega
  · obtain ⟨slot, read⟩ := used j bound output
    have member := List.mem_toFinset.mpr (operand_mem_of_read read)
    have notBranch : j ∉ HelperReviewEquality.branchValues C := by
      intro branch
      obtain ⟨w, wb, wj⟩ := Finset.mem_map.mp branch
      have earlier := raw w wb
      change w.val = j at wj
      omega
    rw [counts j member, if_neg notBranch, if_neg output]

lemma cofactor18791_cover_counts (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    let least := HelperReviewEquality.raw_least C hf hs he
    let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
    let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
      (c7_output_valid least)
    let label := firstInputBoundary least.hcl out live
    let D := H5C7Cover.earlierCover label
    D.card = 4 ∧ H5C7Cover.covers D ∧
      (∀ v : Fin 7, (operands C.gates).count v.val = if v ∈ D then 2 else 1) := by
  classical
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  let label := firstInputBoundary least.hcl out live
  let D := H5C7Cover.earlierCover label
  change D.card = 4 ∧ H5C7Cover.covers D ∧
    (∀ v : Fin 7, (operands C.gates).count v.val = if v ∈ D then 2 else 1)
  have package := H5RawC7.raw_representative_signals C hf hs he
  have raw := Root18791NoSharing.no_internal_branches C hf hs he
  have counts := (HelperReviewEquality.raw_exact_branch_budget C hf hs he).2.2.2
  have used := least_wire_used least c7_nonconstant c7_depends c7_restrict_nonconstant
  have last := cofactor18791_output_last C hf hs he
  have branchIff (v : Fin 7) : v.val ∈ HelperReviewEquality.branchValues C ↔ v ∈ D := by
    constructor
    · intro member
      obtain ⟨w, wb, wv⟩ := Finset.mem_map.mp member
      obtain ⟨u, ud, labelu, _⟩ := package.2.2.1 w wb
      change label u = w at labelu
      have primary : (label u).val < 7 := by rw [labelu]; exact raw w wb
      have primaryEq := primary_first_boundary_eq least.hcl out live u primary
      have eq : u = v := by
        apply Fin.ext
        change w.val = v.val at wv
        have value := congrArg Fin.val primaryEq
        change (label u).val = u.val at value
        rw [labelu] at value
        omega
      simpa only [eq] using ud
    · intro member
      have before : label v < out := (package.2.2.2.1 v).mp member
      have branch : label v ∈ circuitBranchWires C.gates := by
        rcases H5C7CircuitCover.boundary_labels least.hcl out live v with equal | branch
        · exact (lt_irrefl out (equal ▸ before)).elim
        · exact branch
      have primary := raw (label v) branch
      have primaryEq := primary_first_boundary_eq least.hcl out live v primary
      apply Finset.mem_map.mpr
      refine ⟨label v, branch, ?_⟩
      change (label v).val = v.val
      exact congrArg Fin.val primaryEq
  refine ⟨package.1, package.2.1, ?_⟩
  intro v
  have valid : v.val < 7 + C.gates.length := by omega
  have notOutput : v.val ≠ C.output := by omega
  obtain ⟨slot, read⟩ := used v.val valid notOutput
  have member := List.mem_toFinset.mpr (operand_mem_of_read read)
  simpa only [branchIff] using counts v.val member

lemma cofactor18791_raw_input_count_sum (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0))) :
    ∑ v : Fin 7, (operands C.gates).count v.val = 11 := by
  classical
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  let label := firstInputBoundary least.hcl out live
  let D := H5C7Cover.earlierCover label
  have budget := cofactor18791_cover_counts C hf hs he
  have split (v : Fin 7) : (if v ∈ D then 2 else 1) = 1 + if v ∈ D then 1 else 0 := by
    split_ifs <;> decide
  have each (v : Fin 7) : (operands C.gates).count v.val = if v ∈ D then 2 else 1 :=
    budget.2.2 v
  have card : D.card = 4 := budget.1
  simp_rw [each, split]
  rw [Finset.sum_add_distrib]
  simp [card]


namespace HelperOneFormula

open PEqualNP.MetaComplexity

def count {n : Nat} : DMFormula n → Fin n → Nat
  | .lit j _, i => if i = j then 1 else 0
  | .and p q, i => count p i + count q i
  | .or p q, i => count p i + count q i

def positive {n : Nat} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and p q => positive p ∧ positive q
  | .or p q => positive p ∧ positive q


lemma sum_count {n : Nat} (p : DMFormula n) : (∑ i : Fin n, count p i) = p.leaves := by
  induction p with
  | lit j b => simp [count, DMFormula.leaves]
  | and p q hp hq => simp [count, DMFormula.leaves, Finset.sum_add_distrib, hp, hq]
  | or p q hp hq => simp [count, DMFormula.leaves, Finset.sum_add_distrib, hp, hq]


lemma eval_congr_count {n : Nat} (p : DMFormula n) (x y : Fin n → Bool)
    (hxy : ∀ i, 0 < count p i → x i = y i) : p.eval x = p.eval y := by
  induction p with
  | lit i b => simp [DMFormula.eval, hxy i (by simp [count])]
  | and p q hp hq =>
    have hep := hp (fun i hi => hxy i (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)))
    have heq := hq (fun i hi => hxy i (Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)))
    simp [DMFormula.eval, hep, heq]
  | or p q hp hq =>
    have hep := hp (fun i hi => hxy i (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)))
    have heq := hq (fun i hi => hxy i (Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)))
    simp [DMFormula.eval, hep, heq]

lemma eval_congr_of_count_eq_zero {n : Nat} (p : DMFormula n) (i : Fin n)
    (hzero : count p i = 0) (x y : Fin n → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) : p.eval x = p.eval y := by
  apply eval_congr_count
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [hzero] at hj
  · exact hxy j hji

lemma count_pos_of_eval_ne {n : Nat} (p : DMFormula n) (i : Fin n)
    (x y : Fin n → Bool) (hxy : ∀ j, j ≠ i → x j = y j)
    (hne : p.eval x ≠ p.eval y) : 0 < count p i := by
  by_contra h
  have hz : count p i = 0 := Nat.eq_zero_of_not_pos h
  exact hne (eval_congr_of_count_eq_zero p i hz x y hxy)

lemma eval_update_of_count_eq_zero {n : Nat} (p : DMFormula n) (i : Fin n)
    (hzero : count p i = 0) (x : Fin n → Bool) (b : Bool) :
    p.eval (Function.update x i b) = p.eval x := by
  apply eval_congr_of_count_eq_zero p i hzero
  intro j hj
  simp [Function.update, hj]

lemma eval_monotone {n : Nat} (p : DMFormula n) (hp : positive p) : Monotone p.eval := by
  induction p with
  | lit i b =>
    have hb : b = true := hp
    subst b
    intro x y hxy
    exact hxy i
  | and p q ihp ihq =>
    intro x y hxy
    have h1 := ihp hp.1 hxy
    have h2 := ihq hp.2 hxy
    simp only [DMFormula.eval]
    cases hx : p.eval x <;> cases hy : p.eval y <;>
      cases hqx : q.eval x <;> cases hqy : q.eval y <;> simp_all
  | or p q ihp ihq =>
    intro x y hxy
    have h1 := ihp hp.1 hxy
    have h2 := ihq hp.2 hxy
    simp only [DMFormula.eval]
    cases hx : p.eval x <;> cases hy : p.eval y <;>
      cases hqx : q.eval x <;> cases hqy : q.eval y <;> simp_all

lemma eval_false_of_positive {n : Nat} (p : DMFormula n) (hp : positive p) :
    p.eval (fun _ => false) = false := by
  induction p with
  | lit i b => simp_all [positive, DMFormula.eval]
  | and p q ihp ihq => simp [DMFormula.eval, ihp hp.1, ihq hp.2]
  | or p q ihp ihq => simp [DMFormula.eval, ihp hp.1, ihq hp.2]

lemma eval_true_of_positive {n : Nat} (p : DMFormula n) (hp : positive p) :
    p.eval (fun _ => true) = true := by
  induction p with
  | lit i b => simp_all [positive, DMFormula.eval]
  | and p q ihp ihq => simp [DMFormula.eval, ihp hp.1, ihq hp.2]
  | or p q ihp ihq => simp [DMFormula.eval, ihp hp.1, ihq hp.2]

end HelperOneFormula

namespace HelperOneCover

def pathValue (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5)

def zeroPair (a b : Fin 6) (x : Fin 6 → Bool) (j : Fin 6) : Bool :=
  if j = a ∨ j = b then false else x j

def raise (a : Fin 6) (x : Fin 6 → Bool) (j : Fin 6) : Bool :=
  if j = a then true else x j

def ZeroInvariant (h : (Fin 6 → Bool) → Bool) (a b : Fin 6) : Prop :=
  ∀ x, h x = h (zeroPair a b x)

def Collision (h : (Fin 6 → Bool) → Bool) : Prop :=
  ∀ x, h x = true → (x 0 || x 5) = true → pathValue x = true

def OffWitness (h : (Fin 6 → Bool) → Bool) : Prop :=
  ∃ x, x 0 = false ∧ x 5 = false ∧ h x = true

lemma true_of_true_le {b : Bool} (hb : true ≤ b) : b = true := by
  cases b with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) hb)
  | true => rfl

lemma true_after_raise {h : (Fin 6 → Bool) → Bool} (hm : Monotone h)
    {x : Fin 6 → Bool} (hx : h x = true) (a : Fin 6) : h (raise a x) = true := by
  have hle : x ≤ raise a x := by
    intro j
    simp only [raise]
    split_ifs <;> simp
  exact true_of_true_le (by simpa [hx] using hm hle)

lemma first_cover_impossible {h : (Fin 6 → Bool) → Bool}
    (hm : Monotone h) (hc : Collision h) (hw : OffWitness h) :
    ¬ ZeroInvariant h 2 4 := by
  intro hi
  obtain ⟨x, hx0, hx5, hh⟩ := hw
  have hz : h (zeroPair 2 4 x) = true := by rw [← hi x]; exact hh
  have hy := true_after_raise hm hz 5
  have hp := hc (raise 5 (zeroPair 2 4 x)) hy (by simp [raise])
  simp [pathValue, raise, zeroPair, hx0] at hp

lemma last_cover_impossible {h : (Fin 6 → Bool) → Bool}
    (hm : Monotone h) (hc : Collision h) (hw : OffWitness h) :
    ¬ ZeroInvariant h 1 3 := by
  intro hi
  obtain ⟨x, hx0, hx5, hh⟩ := hw
  have hz : h (zeroPair 1 3 x) = true := by rw [← hi x]; exact hh
  have hy := true_after_raise hm hz 0
  have hp := hc (raise 0 (zeroPair 1 3 x)) hy (by simp [raise])
  simp [pathValue, raise, zeroPair, hx5] at hp

lemma middle_cover_upper {h : (Fin 6 → Bool) → Bool}
    (hm : Monotone h) (hc : Collision h) (hi : ZeroInvariant h 1 4)
    {x : Fin 6 → Bool} (hx : h x = true) : x 2 = true ∧ x 3 = true := by
  have hz : h (zeroPair 1 4 x) = true := by rw [← hi x]; exact hx
  have hy := true_after_raise hm hz 0
  have hp := hc (raise 0 (zeroPair 1 4 x)) hy (by simp [raise])
  simpa [pathValue, raise, zeroPair] using hp

lemma middle_cover_exact {h : (Fin 6 → Bool) → Bool}
    (hm : Monotone h) (hc : Collision h) (hw : OffWitness h)
    (hi : ZeroInvariant h 1 4) : h = fun x => x 2 && x 3 := by
  obtain ⟨w, hw0, hw5, hwtrue⟩ := hw
  obtain ⟨hw2, hw3⟩ := middle_cover_upper hm hc hi hwtrue
  have hz : h (zeroPair 1 4 w) = true := by rw [← hi w]; exact hwtrue
  funext x
  have hupper : h x = true → x 2 = true ∧ x 3 = true :=
    middle_cover_upper hm hc hi
  have hlower : x 2 = true → x 3 = true → h x = true := by
    intro hx2 hx3
    have hle : zeroPair 1 4 w ≤ x := by
      intro j
      fin_cases j <;> simp [zeroPair, hw0, hw5, hw2, hw3, hx2, hx3]
    exact true_of_true_le (by simpa [hz] using hm hle)
  cases hh : h x <;> cases hx2 : x 2 <;> cases hx3 : x 3 <;> simp_all

lemma cover_classification {h : (Fin 6 → Bool) → Bool}
    (hm : Monotone h) (hc : Collision h) (hw : OffWitness h)
    (hi : ZeroInvariant h 2 4 ∨ ZeroInvariant h 1 4 ∨ ZeroInvariant h 1 3) :
    ZeroInvariant h 1 4 ∧ h = (fun x => x 2 && x 3) ∧
      ¬ ZeroInvariant h 2 4 ∧ ¬ ZeroInvariant h 1 3 := by
  have hnfirst := first_cover_impossible hm hc hw
  have hnlast := last_cover_impossible hm hc hw
  have hmiddle : ZeroInvariant h 1 4 := by
    rcases hi with hi | hi | hi
    · exact False.elim (hnfirst hi)
    · exact hi
    · exact False.elim (hnlast hi)
  exact ⟨hmiddle, middle_cover_exact hm hc hw hmiddle, hnfirst, hnlast⟩

def PathCover (D : Finset (Fin 6)) : Prop :=
  (0 ∈ D ∨ 1 ∈ D) ∧ (1 ∈ D ∨ 2 ∈ D) ∧ (2 ∈ D ∨ 3 ∈ D) ∧
    (3 ∈ D ∨ 4 ∈ D) ∧ (4 ∈ D ∨ 5 ∈ D)

def SupportedOn (h : (Fin 6 → Bool) → Bool) (D : Finset (Fin 6)) : Prop :=
  ∀ x y, (∀ j ∈ D, x j = y j) → h x = h y

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma path_cover_classification : ∀ D : Finset (Fin 6),
    D.card = 4 → 0 ∈ D → 5 ∈ D → PathCover D →
    D = {0, 1, 3, 5} ∨ D = {0, 2, 3, 5} ∨ D = {0, 2, 4, 5} := by
  unfold PathCover
  decide +kernel

lemma supported_zero_invariant {h : (Fin 6 → Bool) → Bool} {D : Finset (Fin 6)}
    (hs : SupportedOn h D) {a b : Fin 6} (ha : a ∉ D) (hb : b ∉ D) :
    ZeroInvariant h a b := by
  intro x
  apply hs x (zeroPair a b x)
  intro j hj
  have hja : j ≠ a := by intro heq; subst j; exact ha hj
  have hjb : j ≠ b := by intro heq; subst j; exact hb hj
  simp [zeroPair, hja, hjb]

lemma supported_cover_cases {h : (Fin 6 → Bool) → Bool} {D : Finset (Fin 6)}
    (hcard : D.card = 4) (hzero : 0 ∈ D) (hfive : 5 ∈ D) (hcover : PathCover D)
    (hs : SupportedOn h D) :
    (D = {0, 1, 3, 5} ∧ ZeroInvariant h 2 4) ∨
    (D = {0, 2, 3, 5} ∧ ZeroInvariant h 1 4) ∨
    (D = {0, 2, 4, 5} ∧ ZeroInvariant h 1 3) := by
  rcases path_cover_classification D hcard hzero hfive hcover with hD | hD | hD
  · subst D
    exact Or.inl ⟨rfl, supported_zero_invariant hs (by decide) (by decide)⟩
  · subst D
    exact Or.inr (Or.inl ⟨rfl, supported_zero_invariant hs (by decide) (by decide)⟩)
  · subst D
    exact Or.inr (Or.inr ⟨rfl, supported_zero_invariant hs (by decide) (by decide)⟩)

lemma supported_cover_invariance {h : (Fin 6 → Bool) → Bool} {D : Finset (Fin 6)}
    (hcard : D.card = 4) (hzero : 0 ∈ D) (hfive : 5 ∈ D) (hcover : PathCover D)
    (hs : SupportedOn h D) :
    ZeroInvariant h 2 4 ∨ ZeroInvariant h 1 4 ∨ ZeroInvariant h 1 3 := by
  rcases supported_cover_cases hcard hzero hfive hcover hs with h | h | h
  · exact Or.inl h.2
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr h.2)

lemma supported_cover_classification {h : (Fin 6 → Bool) → Bool} {D : Finset (Fin 6)}
    (hm : Monotone h) (hc : Collision h) (hw : OffWitness h)
    (hcard : D.card = 4) (hzero : 0 ∈ D) (hfive : 5 ∈ D) (hcover : PathCover D)
    (hs : SupportedOn h D) : D = {0, 2, 3, 5} ∧ h = (fun x => x 2 && x 3) := by
  rcases supported_cover_cases hcard hzero hfive hcover hs with h | h | h
  · exact False.elim (first_cover_impossible hm hc hw h.2)
  · exact ⟨h.1, middle_cover_exact hm hc hw h.2⟩
  · exact False.elim (last_cover_impossible hm hc hw h.2)

end HelperOneCover

namespace HelperOneFinalFormula

open PEqualNP.MetaComplexity HelperOneFormula HelperOneCover

def input7 (b : Bool) (x : Fin 6 → Bool) : Fin 7 → Bool :=
  ![b, x 0, x 1, x 2, x 3, x 4, x 5]

def contextInput (x : Fin 6 → Bool) : Fin 8 → Bool :=
  ![true, x 0, x 1, x 2, x 3, x 4, x 5, true]

def index7 (j : Fin 6) : Fin 7 := ⟨j.val + 1, by omega⟩
def index8 (j : Fin 6) : Fin 8 := ⟨j.val + 1, by omega⟩

def upperValue (x : Fin 6 → Bool) : Bool := x 0 || x 5 || pathValue x

def hValue (H : DMFormula 7) (x : Fin 6 → Bool) : Bool := H.eval (input7 false x)

lemma input7_index (b : Bool) (x : Fin 6 → Bool) (j : Fin 6) :
    input7 b x (index7 j) = x j := by
  fin_cases j <;> rfl

lemma input7_update (b c : Bool) (x : Fin 6 → Bool) (j : Fin 6) :
    input7 b (Function.update x j c) = Function.update (input7 b x) (index7 j) c := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [input7, index7, Function.update]

lemma contextInput_update (c : Bool) (x : Fin 6 → Bool) (j : Fin 6) :
    contextInput (Function.update x j c) =
      Function.update (contextInput x) (index8 j) c := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [contextInput, index8, Function.update]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma upper_depends : ∀ j : Fin 6, ∃ x : Fin 6 → Bool,
    upperValue (Function.update x j false) ≠ upperValue (Function.update x j true) := by
  decide +kernel

lemma context_count_positive (C : DMFormula 8)
    (hev : ∀ x, C.eval (contextInput x) = upperValue x) (j : Fin 6) :
    0 < count C (index8 j) := by
  obtain ⟨x, hx⟩ := upper_depends j
  apply count_pos_of_eval_ne C (index8 j)
      (Function.update (contextInput x) (index8 j) false)
      (Function.update (contextInput x) (index8 j) true)
  · intro i hi
    simp [Function.update_of_ne hi]
  · simpa only [← contextInput_update, hev] using hx

lemma h_supported (C : DMFormula 8) (H : DMFormula 7) (D : Finset (Fin 6))
    (hev : ∀ x, C.eval (contextInput x) = upperValue x)
    (htotal : ∀ j : Fin 6, count C (index8 j) + count H (index7 j) =
      if j ∈ D then 2 else 1) : SupportedOn (hValue H) D := by
  have hzero : ∀ j : Fin 6, j ∉ D → count H (index7 j) = 0 := by
    intro j hj
    have hc := context_count_positive C hev j
    have ht := htotal j
    rw [ite_eq_right hj] at ht
    omega
  intro x y hxy
  apply eval_congr_count H
  intro i hi
  by_cases hz : i = 0
  · subst i
    rfl
  · have hiz : i.val ≠ 0 := by
      intro he
      exact hz (Fin.ext he)
    let j : Fin 6 := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he : index7 j = i := by
      apply Fin.ext
      simp only [index7, j]
      omega
    rw [← he, input7_index, input7_index]
    apply hxy j
    by_contra hj
    have hbad := hzero j hj
    rw [he] at hbad
    omega

lemma input7_monotone : Monotone (input7 false) := by
  intro x y hxy i
  fin_cases i
  · exact le_rfl
  all_goals exact hxy _

lemma hValue_monotone (H : DMFormula 7) (hp : positive H) : Monotone (hValue H) :=
  (eval_monotone H hp).comp input7_monotone

lemma middle_h_counts (H : DMFormula 7)
    (he : hValue H = fun x => x 2 && x 3) :
    0 < count H 3 ∧ 0 < count H 4 := by
  have dep : ∀ j : Fin 6, j = 2 ∨ j = 3 →
      ∃ x : Fin 6 → Bool,
        hValue H (Function.update x j false) ≠ hValue H (Function.update x j true) := by
    rw [he]
    decide +kernel
  have hc : ∀ j : Fin 6, j = 2 ∨ j = 3 → 0 < count H (index7 j) := by
    intro j hj
    obtain ⟨x, hx⟩ := dep j hj
    apply count_pos_of_eval_ne H (index7 j)
        (Function.update (input7 false x) (index7 j) false)
        (Function.update (input7 false x) (index7 j) true)
    · intro i hi
      simp [Function.update_of_ne hi]
    · simpa only [hValue, input7_update] using hx
  exact ⟨hc 2 (Or.inl rfl), hc 3 (Or.inr rfl)⟩

end HelperOneFinalFormula

namespace HelperOneFinalFormula

open PEqualNP.MetaComplexity HelperOneFormula HelperOneCover

lemma h_supported_le (C : DMFormula 8) (H : DMFormula 7) (D : Finset (Fin 6))
    (hev : ∀ x, C.eval (contextInput x) = upperValue x)
    (htotal : ∀ j : Fin 6, count C (index8 j) + count H (index7 j) ≤
      if j ∈ D then 2 else 1) : SupportedOn (hValue H) D := by
  have hzero : ∀ j : Fin 6, j ∉ D → count H (index7 j) = 0 := by
    intro j hj
    have hc := context_count_positive C hev j
    have ht := htotal j
    rw [ite_eq_right hj] at ht
    omega
  intro x y hxy
  apply eval_congr_count H
  intro i hi
  by_cases hz : i = 0
  · subst i
    rfl
  · have hiz : i.val ≠ 0 := by
      intro he
      exact hz (Fin.ext he)
    let j : Fin 6 := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he : index7 j = i := by
      apply Fin.ext
      simp only [index7, j]
      omega
    rw [← he, input7_index, input7_index]
    apply hxy j
    by_contra hj
    have hbad := hzero j hj
    rw [he] at hbad
    omega


end HelperOneFinalFormula

namespace HelperOneFinalFormula

open PEqualNP.MetaComplexity HelperOneFormula HelperOneCover

lemma occurrences_eq_count {n : Nat} (p : DMFormula n) (i : Fin n) :
    PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.occurrences i p = count p i := by
  induction p with
  | lit j b => simp [PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.occurrences, count, eq_comm]
  | and p q hp hq => simp [PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.occurrences, count, hp, hq]
  | or p q hp hq => simp [PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.occurrences, count, hp, hq]

lemma context_middle_pair_impossible (C : DMFormula 8)
    (hev : ∀ x, C.eval (contextInput x) = upperValue x)
    (h3 : count C 3 ≤ 1) (h4 : count C 4 ≤ 1) : False := by
  let baseA : Fin 8 → Bool := contextInput (fun _ => false)
  let baseO : Fin 8 → Bool := contextInput ![false, true, false, false, true, false]
  apply PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.fixed_pair_invariant
    3 4 C (by simpa [occurrences_eq_count] using h3)
    (by simpa [occurrences_eq_count] using h4) baseA baseO id id
  · intro a b
    have hin :
        PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.pairInput 3 4 baseA a b =
          contextInput ![false, false, a, b, false, false] := by
      funext i
      fin_cases i <;> simp [PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.pairInput,
        baseA, contextInput]
    change C.eval _ = _
    rw [hin, hev]
    simp [upperValue, pathValue]
  · intro a b
    have hin :
        PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.pairInput 3 4 baseO a b =
          contextInput ![false, true, a, b, true, false] := by
      funext i
      fin_cases i <;> simp [PEqualNP.Outside.L_meta_1549_aux.PetersenScratch.pairInput,
        baseO, contextInput]
    change C.eval _ = _
    rw [hin, hev]
    cases a <;> cases b <;> rfl

lemma final_formula_obstruction_pair
    (C : DMFormula 8) (H : DMFormula 7) (D : Finset (Fin 6))
    (hp : positive H) (hc : Collision (hValue H)) (hw : OffWitness (hValue H))
    (hcard : D.card = 4) (hzero : 0 ∈ D) (hfive : 5 ∈ D) (hcover : PathCover D)
    (hev : ∀ x, C.eval (contextInput x) = upperValue x)
    (htotal : ∀ j : Fin 6, count C (index8 j) + count H (index7 j) ≤
      if j ∈ D then 2 else 1) : False := by
  have hs := h_supported_le C H D hev htotal
  obtain ⟨hD, hh⟩ := supported_cover_classification
    (hValue_monotone H hp) hc hw hcard hzero hfive hcover hs
  obtain ⟨hh3, hh4⟩ := middle_h_counts H hh
  have h3 := htotal 2
  have h4 := htotal 3
  simp [hD, index7, index8] at h3 h4
  exact context_middle_pair_impossible C hev (by omega) (by omega)

end HelperOneFinalFormula

namespace HelperOneSemantics

open PEqualNP.MetaComplexity HelperOneFormula HelperOneCover HelperOneFinalFormula

def cycle7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def plugInput (H : DMFormula 7) (x : Fin 7 → Bool) : Fin 8 → Bool :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 0 || H.eval x]

lemma cycle7_zero (x : Fin 6 → Bool) : cycle7 (input7 false x) = pathValue x := by
  simp [cycle7, input7, pathValue]

lemma cycle7_one (x : Fin 6 → Bool) : cycle7 (input7 true x) = upperValue x := by
  simp only [cycle7, input7, upperValue, pathValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Bool.true_and, Bool.and_true]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

lemma context_cofactor (C : DMFormula 8) (H : DMFormula 7)
    (hev : ∀ x, C.eval (plugInput H x) = cycle7 x) :
    ∀ x, C.eval (contextInput x) = upperValue x := by
  intro x
  have hp : plugInput H (input7 true x) = contextInput x := by
    funext i
    fin_cases i <;> simp [plugInput, input7, contextInput]
  rw [← hp, hev, cycle7_one]

lemma context_collision (C : DMFormula 8) (H : DMFormula 7)
    (hc0 : count C 0 = 0)
    (hev : ∀ x, C.eval (plugInput H x) = cycle7 x) : Collision (hValue H) := by
  intro x hh hend
  have same : C.eval (plugInput H (input7 false x)) = C.eval (contextInput x) := by
    apply eval_congr_of_count_eq_zero C 0 hc0
    intro i hi
    fin_cases i <;> simp_all [plugInput, input7, contextInput, hValue]
  rw [hev, cycle7_zero, context_cofactor C H hev] at same
  rw [same]
  simp [upperValue, hend]

lemma original_witness (H : DMFormula 7)
    (hw : ∃ x : Fin 7 → Bool,
      x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ H.eval x = true) :
    OffWitness (hValue H) := by
  obtain ⟨x, hx0, hx1, hx6, hh⟩ := hw
  let y : Fin 6 → Bool := fun j => x j.succ
  have he : input7 false y = x := by
    funext i
    fin_cases i <;> simp [input7, y, hx0]
  refine ⟨y, hx1, hx6, ?_⟩
  simpa only [hValue, he] using hh

lemma formula_obstruction_from_c7
    (C : DMFormula 8) (H : DMFormula 7) (D : Finset (Fin 6))
    (hp : positive H) (hc0 : count C 0 = 0)
    (hev : ∀ x, C.eval (plugInput H x) = cycle7 x)
    (hw : ∃ x : Fin 7 → Bool,
      x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ H.eval x = true)
    (hcard : D.card = 4) (hzero : 0 ∈ D) (hfive : 5 ∈ D) (hcover : PathCover D)
    (htotal : ∀ j : Fin 6, count C (index8 j) + count H (index7 j) ≤
      if j ∈ D then 2 else 1) : False := by
  exact final_formula_obstruction_pair C H D hp
    (context_collision C H hc0 hev) (original_witness H hw)
    hcard hzero hfive hcover (context_cofactor C H hev) htotal

end HelperOneSemantics

namespace HelperOnePlug

open PEqualNP.MetaComplexity HelperOneFormula

def positiveBind {n m : Nat} (σ : Fin n → DMFormula m) : DMFormula n → DMFormula m
  | .lit i _ => σ i
  | .and p q => .and (positiveBind σ p) (positiveBind σ q)
  | .or p q => .or (positiveBind σ p) (positiveBind σ q)

lemma positiveBind_eval {n m : Nat} (σ : Fin n → DMFormula m)
    (p : DMFormula n) (hp : positive p) (x : Fin m → Bool) :
    (positiveBind σ p).eval x = p.eval (fun i => (σ i).eval x) := by
  induction p with
  | lit i b =>
    have hb : b = true := hp
    simp [positiveBind, DMFormula.eval, hb]
  | and p q ihp ihq => simp [positiveBind, DMFormula.eval, ihp hp.1, ihq hp.2]
  | or p q ihp ihq => simp [positiveBind, DMFormula.eval, ihp hp.1, ihq hp.2]

lemma count_bind {n m : Nat} (σ : Fin n → DMFormula m)
    (p : DMFormula n) (j : Fin m) :
    count (positiveBind σ p) j = ∑ i : Fin n, count p i * count (σ i) j := by
  induction p with
  | lit i b => simp [positiveBind, count, ite_mul]
  | and p q hp hq => simp [positiveBind, count, hp, hq, Nat.add_mul, Finset.sum_add_distrib]
  | or p q hp hq => simp [positiveBind, count, hp, hq, Nat.add_mul, Finset.sum_add_distrib]

lemma positiveBind_positive {n m : Nat} (σ : Fin n → DMFormula m)
    (hσ : ∀ i, positive (σ i)) (p : DMFormula n) : positive (positiveBind σ p) := by
  induction p with
  | lit i b => exact hσ i
  | and p q hp hq => exact ⟨hp, hq⟩
  | or p q hp hq => exact ⟨hp, hq⟩

def plug (H : DMFormula 7) : Fin 8 → DMFormula 7 :=
  ![.lit 0 true, .lit 1 true, .lit 2 true, .lit 3 true,
    .lit 4 true, .lit 5 true, .lit 6 true, .or (.lit 0 true) H]

lemma count_plug (H : DMFormula 7) (C : DMFormula 8) (j : Fin 6) :
    count (positiveBind (plug H) C) j.succ =
      count C j.succ.castSucc + count C 7 * count H j.succ := by
  rw [count_bind]
  fin_cases j <;> simp [plug, count, Fin.sum_univ_succ]

lemma count_plug_of_one (H : DMFormula 7) (C : DMFormula 8)
    (hone : count C 7 = 1) (j : Fin 6) :
    count (positiveBind (plug H) C) j.succ =
      count C j.succ.castSucc + count H j.succ := by
  rw [count_plug, hone, one_mul]

end HelperOnePlug

namespace HelperOnePlug

open PEqualNP.MetaComplexity HelperOneFormula

lemma count_plug_zero (H : DMFormula 7) (C : DMFormula 8) :
    count (positiveBind (plug H) C) 0 =
      count C 0 + count C 7 * (1 + count H 0) := by
  rw [count_bind]
  simp [plug, count, Fin.sum_univ_succ]

lemma context_zero_of_budget (H : DMFormula 7) (C : DMFormula 8)
    (hone : count C 7 = 1)
    (hraw : count (positiveBind (plug H) C) 0 ≤ 1) :
    count C 0 = 0 ∧ count H 0 = 0 := by
  rw [count_plug_zero, hone, one_mul] at hraw
  omega

end HelperOnePlug

namespace HelperOneReindex

open HelperOneFinalFormula HelperOneCover

def tailSet (D : Finset (Fin 7)) : Finset (Fin 6) :=
  Finset.univ.filter (fun j => index7 j ∈ D)

lemma mem_tailSet (D : Finset (Fin 7)) (j : Fin 6) :
    j ∈ tailSet D ↔ index7 j ∈ D := by simp [tailSet]

lemma tailSet_card (D : Finset (Fin 7)) (hz : 0 ∉ D) :
    (tailSet D).card = D.card := by
  classical
  apply Finset.card_bij (fun j _ => index7 j)
  · intro j hj
    exact (mem_tailSet D j).mp hj
  · intro a ha b hb hab
    apply Fin.ext
    have he := congrArg Fin.val hab
    simp only [index7] at he
    omega
  · intro i hi
    have hn : i.val ≠ 0 := by
      intro he
      have eq : i = 0 := Fin.ext he
      exact hz (eq ▸ hi)
    let j : Fin 6 := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he : index7 j = i := by
      apply Fin.ext
      simp only [index7, j]
      omega
    refine ⟨j, (mem_tailSet D j).mpr ?_, he⟩
    simpa only [he] using hi

lemma tailSet_cover (D : Finset (Fin 7)) (hz : 0 ∉ D)
    (hcover : ∀ i : Fin 7, i ∈ D ∨ i + 1 ∈ D) :
    0 ∈ tailSet D ∧ 5 ∈ tailSet D ∧ PathCover (tailSet D) := by
  have hfirst : (1 : Fin 7) ∈ D := (hcover 0).resolve_left hz
  have hlast : (6 : Fin 7) ∈ D := (hcover 6).resolve_right (by simpa using hz)
  refine ⟨(mem_tailSet D 0).mpr hfirst, (mem_tailSet D 5).mpr hlast, ?_⟩
  unfold PathCover
  simp only [mem_tailSet]
  exact ⟨hcover 1, hcover 2, hcover 3, hcover 4, hcover 5⟩

end HelperOneReindex

namespace HelperOneSemantics

open PEqualNP.MetaComplexity HelperOneFormula HelperOneCover HelperOneFinalFormula
open HelperOnePlug HelperOneReindex

lemma plug_semantics (C : DMFormula 8) (H : DMFormula 7) (hp : positive C)
    (x : Fin 7 → Bool) :
    (positiveBind (plug H) C).eval x = C.eval (plugInput H x) := by
  rw [positiveBind_eval _ C hp]
  congr 1
  funext i
  fin_cases i <;> simp [plug, plugInput, DMFormula.eval]

lemma formula_obstruction_original_cover
    (C : DMFormula 8) (H : DMFormula 7) (D : Finset (Fin 7))
    (hpC : positive C) (hpH : positive H) (hone : count C 7 = 1)
    (hev : ∀ x, (positiveBind (plug H) C).eval x = cycle7 x)
    (hw : ∃ x : Fin 7 → Bool,
      x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ H.eval x = true)
    (hcard : D.card = 4) (hz : 0 ∉ D)
    (hcover : ∀ i : Fin 7, i ∈ D ∨ i + 1 ∈ D)
    (htotal : ∀ j : Fin 7, count (positiveBind (plug H) C) j ≤
      if j ∈ D then 2 else 1) : False := by
  have hraw : count (positiveBind (plug H) C) 0 ≤ 1 := by
    simpa only [ite_eq_right hz] using htotal 0
  have hc0 := (context_zero_of_budget H C hone hraw).1
  have he : ∀ x, C.eval (plugInput H x) = cycle7 x := by
    intro x
    rw [← plug_semantics C H hpC x]
    exact hev x
  obtain ⟨hfirst, hlast, hpath⟩ := tailSet_cover D hz hcover
  apply formula_obstruction_from_c7 C H (tailSet D) hpH hc0 he hw
    ((tailSet_card D hz).trans hcard) hfirst hlast hpath
  intro j
  have ht := htotal j.succ
  rw [count_plug_of_one H C hone j] at ht
  have ec : j.succ.castSucc = index8 j := by apply Fin.ext; rfl
  have eh : j.succ = index7 j := by apply Fin.ext; rfl
  rw [ec, eh] at ht
  simpa only [mem_tailSet] using ht

end HelperOneSemantics


namespace HelperOneContext

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PetersenCutFormula PetersenCutTrace PetersenScratch
open HelperOneFormula HelperOnePlug

 def BinaryAndOr (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → ∃ a b,
    a < 7 + p ∧ b < 7 + p ∧ g.inputs = [a, b] ∧ (g.op = .and ∨ g.op = .or)

lemma binary_of_clean {gs : List Gate} (hc : CleanL 7 gs)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) : BinaryAndOr gs := by
  intro p g hg
  rcases hc p g hg with ⟨hn, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, hin⟩
  · have h := hops g (List.mem_iff_getElem?.mpr ⟨p, hg⟩)
    rw [hn] at h
    rcases h with h | h <;> cases h
  · exact ⟨a, b, ha, hb, hin, hop⟩

def contextFormula (gs : List Gate) (cut w : Nat) : DMFormula 8 :=
  if w = cut then .lit 7 true
  else if hw : w < 7 then .lit ⟨w, by omega⟩ true
  else match gs[w - 7]? with
    | none => .lit 0 true
    | some g => match g.op, g.inputs with
      | .and, [a, b] =>
          if ha : a < w then
            if hb : b < w then .and (contextFormula gs cut a) (contextFormula gs cut b)
            else .lit 0 true
          else .lit 0 true
      | .or, [a, b] =>
          if ha : a < w then
            if hb : b < w then .or (contextFormula gs cut a) (contextFormula gs cut b)
            else .lit 0 true
          else .lit 0 true
      | _, _ => .lit 0 true
termination_by w
 decreasing_by all_goals assumption

def fill (p : DMFormula 7) (i : Fin 8) : DMFormula 7 :=
  if hi : i.val < 7 then .lit ⟨i.val, hi⟩ true else p

lemma context_at_cut (gs : List Gate) (cut : Nat) :
    contextFormula gs cut cut = .lit 7 true := by
  rw [contextFormula]
  simp

lemma context_at_input (gs : List Gate) {cut : Nat} (hcut : 7 ≤ cut) (i : Fin 7) :
    contextFormula gs cut i.val = .lit i.castSucc true := by
  have hne : i.val ≠ cut := by have := i.isLt; omega
  rw [contextFormula]
  simp [hne, i.isLt]
  rfl

lemma context_and {gs : List Gate} {cut p a b : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .and) (hin : g.inputs = [a, b])
    (ha : a < 7 + p) (hb : b < 7 + p) (hne : 7 + p ≠ cut) :
    contextFormula gs cut (7 + p) = .and (contextFormula gs cut a) (contextFormula gs cut b) := by
  conv_lhs => rw [contextFormula]
  simp [hne, hg, hop, hin, ha, hb]

lemma context_or {gs : List Gate} {cut p a b : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .or) (hin : g.inputs = [a, b])
    (ha : a < 7 + p) (hb : b < 7 + p) (hne : 7 + p ≠ cut) :
    contextFormula gs cut (7 + p) = .or (contextFormula gs cut a) (contextFormula gs cut b) := by
  conv_lhs => rw [contextFormula]
  simp [hne, hg, hop, hin, ha, hb]

lemma full_and {gs : List Gate} {p a b : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .and) (hin : g.inputs = [a, b])
    (ha : a < 7 + p) (hb : b < 7 + p) :
    wireFormula (0 : Fin 7) gs (7 + p) =
      .and (wireFormula 0 gs a) (wireFormula 0 gs b) := by
  conv_lhs => rw [wireFormula]
  simp [hg, hop, hin, ha, hb]

lemma full_or {gs : List Gate} {p a b : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .or) (hin : g.inputs = [a, b])
    (ha : a < 7 + p) (hb : b < 7 + p) :
    wireFormula (0 : Fin 7) gs (7 + p) =
      .or (wireFormula 0 gs a) (wireFormula 0 gs b) := by
  conv_lhs => rw [wireFormula]
  simp [hg, hop, hin, ha, hb]

lemma context_positive {gs : List Gate} (hb : BinaryAndOr gs) {cut w : Nat}
    (hcut : 7 ≤ cut) (hw : w < 7 + gs.length) : positive (contextFormula gs cut w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hc : w = cut
    · subst w
      rw [context_at_cut]
      rfl
    by_cases hi : w < 7
    · rw [context_at_input gs hcut ⟨w, hi⟩]
      rfl
    obtain ⟨p, rfl⟩ : ∃ p, w = 7 + p := ⟨w - 7, by omega⟩
    have hp : p < gs.length := by omega
    let g := gs[p]
    have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
    obtain ⟨a, b, ha, hbb, hin, hop | hop⟩ := hb p g hg
    · rw [context_and hg hop hin ha hbb hc]
      exact ⟨ih a ha (by omega), ih b hbb (by omega)⟩
    · rw [context_or hg hop hin ha hbb hc]
      exact ⟨ih a ha (by omega), ih b hbb (by omega)⟩

lemma full_positive {gs : List Gate} (hb : BinaryAndOr gs) {w : Nat}
    (hw : w < 7 + gs.length) : positive (wireFormula (0 : Fin 7) gs w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < 7
    · rw [wireFormula_input 0 gs ⟨w, hi⟩]
      rfl
    obtain ⟨p, rfl⟩ : ∃ p, w = 7 + p := ⟨w - 7, by omega⟩
    have hp : p < gs.length := by omega
    let g := gs[p]
    have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
    obtain ⟨a, b, ha, hbb, hin, hop | hop⟩ := hb p g hg
    · rw [full_and hg hop hin ha hbb]
      exact ⟨ih a ha (by omega), ih b hbb (by omega)⟩
    · rw [full_or hg hop hin ha hbb]
      exact ⟨ih a ha (by omega), ih b hbb (by omega)⟩

lemma bind_context {gs : List Gate} (hb : BinaryAndOr gs) {cut w : Nat}
    (hcut : 7 ≤ cut) (hw : w < 7 + gs.length) :
    positiveBind (fill (wireFormula (0 : Fin 7) gs cut)) (contextFormula gs cut w) =
      wireFormula 0 gs w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hc : w = cut
    · subst w
      rw [context_at_cut]
      simp [positiveBind, fill]
    by_cases hi : w < 7
    · rw [context_at_input gs hcut ⟨w, hi⟩, wireFormula_input 0 gs ⟨w, hi⟩]
      simp [positiveBind, fill, hi]
    obtain ⟨p, rfl⟩ : ∃ p, w = 7 + p := ⟨w - 7, by omega⟩
    have hp : p < gs.length := by omega
    let g := gs[p]
    have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
    obtain ⟨a, b, ha, hbb, hin, hop | hop⟩ := hb p g hg
    · rw [context_and hg hop hin ha hbb hc, full_and hg hop hin ha hbb]
      simp only [positiveBind, ih a ha (by omega), ih b hbb (by omega)]
    · rw [context_or hg hop hin ha hbb hc, full_or hg hop hin ha hbb]
      simp only [positiveBind, ih a ha (by omega), ih b hbb (by omega)]

lemma count_eq_occurrences {n : Nat} (p : DMFormula n) (i : Fin n) :
    count p i = occurrences i p := by
  induction p <;> simp_all [count, occurrences, eq_comm]

lemma reader_formula_cases {gs : List Gate} {p h : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p) :
    wireFormula (0 : Fin 7) gs (7 + p) = .or (.lit 0 true) (wireFormula 0 gs h) ∨
    wireFormula (0 : Fin 7) gs (7 + p) = .or (wireFormula 0 gs h) (.lit 0 true) := by
  have hz : wireFormula (0 : Fin 7) gs 0 = .lit 0 true := by
    simpa using wireFormula_input (0 : Fin 7) gs (0 : Fin 7)
  rcases hin with hin | hin
  · left
    rw [full_or hg hop hin (by omega) hh, hz]
  · right
    rw [full_or hg hop hin hh (by omega), hz]

lemma fill_reader_eval {gs : List Gate} {p h : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (i : Fin 8) (x : Fin 7 → Bool) :
    (fill (wireFormula (0 : Fin 7) gs (7 + p)) i).eval x =
      (plug (wireFormula 0 gs h) i).eval x := by
  rcases reader_formula_cases hg hop hin hh with hr | hr
  · fin_cases i <;> simp [fill, plug, hr, DMFormula.eval]
  · fin_cases i <;> simp [fill, plug, hr, DMFormula.eval, Bool.or_comm]

lemma fill_reader_count {gs : List Gate} {p h : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (i : Fin 8) (j : Fin 7) :
    count (fill (wireFormula (0 : Fin 7) gs (7 + p)) i) j =
      count (plug (wireFormula 0 gs h) i) j := by
  rcases reader_formula_cases hg hop hin hh with hr | hr
  · fin_cases i <;> simp [fill, plug, hr, count]
  · fin_cases i <;> simp [fill, plug, hr, count]
    omega

lemma mate_positive {gs : List Gate} (hb : BinaryAndOr gs) {p h : Nat} {g : Gate}
    (hg : gs[p]? = some g) (hh : h < 7 + p) : positive (wireFormula (0 : Fin 7) gs h) := by
  have hp : p < gs.length := (List.getElem?_eq_some_iff.mp hg).1
  exact full_positive hb (by omega)

lemma context_plug_eval {gs : List Gate} (hc : CleanL 7 gs) (hb : BinaryAndOr gs)
    {p h out : Nat} {g : Gate} (hg : gs[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (hout : out < 7 + gs.length) (x : Fin 7 → Bool) :
    (contextFormula gs (7 + p) out).eval (fun i => (plug (wireFormula 0 gs h) i).eval x) =
      vl gs x out := by
  have hpos := context_positive hb (by omega : 7 ≤ 7 + p) hout
  calc
    _ = (contextFormula gs (7 + p) out).eval
        (fun i => (fill (wireFormula (0 : Fin 7) gs (7 + p)) i).eval x) := by
      congr 1
      funext i
      exact (fill_reader_eval hg hop hin hh i x).symm
    _ = (positiveBind (fill (wireFormula (0 : Fin 7) gs (7 + p)))
        (contextFormula gs (7 + p) out)).eval x :=
      (positiveBind_eval _ _ hpos x).symm
    _ = (wireFormula (0 : Fin 7) gs out).eval x := by rw [bind_context hb (by omega) hout]
    _ = vl gs x out := wireFormula_eval 0 hc x out hout

lemma actual_plug_count {gs : List Gate} (hb : BinaryAndOr gs)
    {p h out : Nat} {g : Gate} (hg : gs[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (hout : out < 7 + gs.length) (j : Fin 7) :
    count (positiveBind (plug (wireFormula (0 : Fin 7) gs h))
        (contextFormula gs (7 + p) out)) j = count (wireFormula 0 gs out) j := by
  rw [count_bind]
  calc
    _ = ∑ i : Fin 8, count (contextFormula gs (7 + p) out) i *
        count (fill (wireFormula (0 : Fin 7) gs (7 + p)) i) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fill_reader_count hg hop hin hh i j]
    _ = count (positiveBind (fill (wireFormula (0 : Fin 7) gs (7 + p)))
        (contextFormula gs (7 + p) out)) j := (count_bind _ _ j).symm
    _ = count (wireFormula 0 gs out) j := by rw [bind_context hb (by omega) hout]

lemma context_count_cut (gs : List Gate) (cut : Nat) (chosen : Fin 8) :
    count (contextFormula gs cut cut) chosen = if chosen = 7 then 1 else 0 := by
  rw [context_at_cut]
  rfl

lemma context_count_input (gs : List Gate) {cut : Nat} (hcut : 7 ≤ cut)
    (i : Fin 7) (chosen : Fin 8) :
    count (contextFormula gs cut i.val) chosen = if chosen = i.castSucc then 1 else 0 := by
  rw [context_at_input gs hcut i]
  rfl

lemma context_count_gate {gs : List Gate} (hb : BinaryAndOr gs)
    {cut p : Nat} {g : Gate} (hg : gs[p]? = some g) (hne : 7 + p ≠ cut)
    (chosen : Fin 8) :
    count (contextFormula gs cut (7 + p)) chosen =
      (g.inputs.map fun a => count (contextFormula gs cut a) chosen).sum := by
  obtain ⟨a, b, ha, hbb, hin, hop | hop⟩ := hb p g hg
  · rw [context_and hg hop hin ha hbb hne]
    simp [count, hin]
  · rw [context_or hg hop hin ha hbb hne]
    simp [count, hin]

lemma context_count_gate_fin {gs : List Gate} (hb : BinaryAndOr gs)
    {cut p : Nat} {g : Gate} (hg : gs[p]? = some g) (hne : 7 + p ≠ cut)
    (chosen : Fin 8) (v : Fin (7 + gs.length)) (hv : v.val = 7 + p)
    (parents : List (Fin (7 + gs.length))) (hparents : parents.map Fin.val = g.inputs) :
    count (contextFormula gs cut v.val) chosen =
      (parents.map fun a => count (contextFormula gs cut a.val) chosen).sum := by
  rw [hv, context_count_gate hb hg hne chosen, ← hparents, List.map_map]
  rfl

lemma context_hole_at_cut (gs : List Gate) (cut : Nat) :
    count (contextFormula gs cut cut) 7 = 1 := by
  simp [context_count_cut]

lemma context_hole_at_input (gs : List Gate) {cut a : Nat} (hcut : 7 ≤ cut)
    (ha : a < 7) : count (contextFormula gs cut a) 7 = 0 := by
  have hne : (7 : Fin 8) ≠ (⟨a, ha⟩ : Fin 7).castSucc := by
    intro heq
    have hv := congrArg Fin.val heq
    change 7 = a at hv
    omega
  have hc := context_count_input gs hcut ⟨a, ha⟩ 7
  rw [if_neg hne] at hc
  exact hc

lemma mate_eval_circuit (C : Circuit) (hc : CleanL 7 C.gates) {h : Nat}
    (hh : h < 7 + C.gates.length) (x : Fin 7 → Bool) :
    (wireFormula (0 : Fin 7) C.gates h).eval x = (C.wires (List.ofFn x)).getD h false :=
  wireFormula_eval 0 hc x h hh

lemma context_eval_circuit (C : Circuit) (hc : CleanL 7 C.gates) (hb : BinaryAndOr C.gates)
    {p h : Nat} {g : Gate} (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (hout : C.output < 7 + C.gates.length) (x : Fin 7 → Bool) :
    (contextFormula C.gates (7 + p) C.output).eval
      (fun i => (plug (wireFormula 0 C.gates h) i).eval x) = C.eval (List.ofFn x) :=
  context_plug_eval hc hb hg hop hin hh hout x

end HelperOneContext


namespace PEqualNP.Outside.L_meta_18791_aux.FlowCount

open scoped BigOperators

lemma sum_map_eq_sum_count_range (M : ℕ) (L : List ℕ) (w : ℕ → ℕ)
    (hbound : ∀ a ∈ L, a < M) :
    (L.map w).sum = ∑ i ∈ Finset.range M, L.count i * w i := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha : a < M := hbound a (by simp)
      have hL : ∀ b ∈ L, b < M := fun b hb => hbound b (by simp [hb])
      rw [List.map_cons, List.sum_cons, ih hL]
      have hcount (i : ℕ) : (a :: L).count i * w i =
          (if i = a then w a else 0) + L.count i * w i := by
        by_cases hi : i = a
        · subst i
          simp [Nat.add_mul, Nat.add_comm]
        · simp [hi, Ne.symm hi]
      simp_rw [hcount]
      rw [Finset.sum_add_distrib]
      simp [ha]

lemma weighted_conservation (n k o : ℕ) (L : List ℕ) (w : ℕ → ℕ)
    (hon : n ≤ o) (hok : o < n + k)
    (hbound : ∀ a ∈ L, a < n + k)
    (hinternal : ∀ i, n ≤ i → i < n + k → L.count i = if i = o then 0 else 1)
    (hflow : (∑ i ∈ Finset.range k, w (n + i)) = (L.map w).sum) :
    w o = ∑ i ∈ Finset.range n, L.count i * w i := by
  have hsplit := sum_map_eq_sum_count_range (n + k) L w hbound
  rw [Finset.sum_range_add] at hsplit
  have hcancel :
      (∑ i ∈ Finset.range k, L.count (n + i) * w (n + i)) + w o =
        ∑ i ∈ Finset.range k, w (n + i) := by
    have heach (i : ℕ) (hi : i ∈ Finset.range k) :
        L.count (n + i) * w (n + i) + (if n + i = o then w o else 0) = w (n + i) := by
      rw [hinternal (n + i) (by omega) (by have hi' := Finset.mem_range.mp hi; omega)]
      by_cases heq : n + i = o
      · simp [heq]
      · simp [heq]
    have hsum := Finset.sum_congr rfl heach
    rw [Finset.sum_add_distrib] at hsum
    have hsingle : (∑ i ∈ Finset.range k, if n + i = o then w o else 0) = w o := by
      have hm : o - n ∈ Finset.range k := by simp; omega
      have heq (i : ℕ) : n + i = o ↔ i = o - n := by omega
      simp_rw [heq]
      simp [hm]
    rw [hsingle] at hsum
    exact hsum
  omega

lemma weighted_conservation_single (n k o chosen : ℕ) (L : List ℕ) (w : ℕ → ℕ)
    (hon : n ≤ o) (hok : o < n + k) (hchosen : chosen < n)
    (hbound : ∀ a ∈ L, a < n + k)
    (hinternal : ∀ i, n ≤ i → i < n + k → L.count i = if i = o then 0 else 1)
    (hflow : (∑ i ∈ Finset.range k, w (n + i)) = (L.map w).sum)
    (hinputs : ∀ i, i < n → w i = if i = chosen then 1 else 0) :
    w o = L.count chosen := by
  rw [weighted_conservation n k o L w hon hok hbound hinternal hflow]
  calc
    (∑ i ∈ Finset.range n, L.count i * w i) =
        ∑ i ∈ Finset.range n, if i = chosen then L.count chosen else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hinputs i (Finset.mem_range.mp hi)]
      by_cases heq : i = chosen
      · subst i
        simp
      · simp [heq]
    _ = L.count chosen := by simp [hchosen]

end PEqualNP.Outside.L_meta_18791_aux.FlowCount


namespace PEqualNP.Outside.L_meta_18791_aux.FlowCount

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

lemma gate_balance (n : Nat) (gs : List Gate) (w : Nat → Nat)
    (recurrence : ∀ p g, gs[p]? = some g →
      w (n + p) = (g.inputs.map w).sum) :
    (∑ p ∈ Finset.range gs.length, w (n + p)) =
      ((gs.flatMap Gate.inputs).map w).sum := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    have hzero : w n = (g.inputs.map w).sum := by
      simpa using recurrence 0 g rfl
    have htail : ∀ p h, gs[p]? = some h →
        w (n + 1 + p) = (h.inputs.map w).sum := by
      intro p h hp
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        recurrence (p + 1) h (by simpa using hp)
    have ht := ih (n + 1) htail
    rw [List.length_cons, Finset.sum_range_succ']
    simpa [List.flatMap_cons, List.map_append, List.sum_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hzero] using
      congrArg (fun a => a + w n) ht

end PEqualNP.Outside.L_meta_18791_aux.FlowCount

namespace PEqualNP.Outside.L_meta_18791_aux.FlowCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PetersenCutFormula PetersenScratch

lemma wireFormula_occurrences_eq_operand_count {n : Nat}
    (fallback chosen : Fin n) {gs : List Gate} (clean : CleanL n gs)
    (out : Nat) (hon : n ≤ out) (hok : out < n + gs.length)
    (internal_counts : ∀ i, n ≤ i → i < n + gs.length →
      (operands gs).count i = if i = out then 0 else 1) :
    occurrences chosen (wireFormula fallback gs out) = (operands gs).count chosen.val := by
  let w : Nat → Nat := fun i => occurrences chosen (wireFormula fallback gs i)
  have bounds : ∀ a ∈ operands gs, a < n + gs.length := by
    intro a member
    obtain ⟨g, hg, ha⟩ := List.mem_flatMap.mp member
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hg
    have hp_lt := (List.getElem?_eq_some_iff.mp hp).1
    have prior := (clean p g hp).lt a ha
    omega
  have balance : (∑ i ∈ Finset.range gs.length, w (n + i)) =
      ((operands gs).map w).sum :=
    gate_balance n gs w (fun p g hp => wireFormula_count_gate fallback clean chosen hp)
  have inputs (i : Nat) (hi : i < n) : w i = if i = chosen.val then 1 else 0 := by
    have h := wireFormula_count_input fallback gs chosen (⟨i, hi⟩ : Fin n)
    simpa [w, Fin.ext_iff] using h
  exact weighted_conservation_single n gs.length out chosen.val (operands gs) w
    hon hok chosen.isLt bounds internal_counts balance inputs

end PEqualNP.Outside.L_meta_18791_aux.FlowCount

namespace PEqualNP.Outside.L_meta_18791_aux.FlowCount
open scoped BigOperators

lemma weighted_conservation_extra (n k o extra : ℕ) (L : List ℕ) (w : ℕ → ℕ)
    (hon : n ≤ o) (hok : o < n + k)
    (hbound : ∀ a ∈ L, a < n + k)
    (hinternal : ∀ i, n ≤ i → i < n + k → L.count i = if i = o then 0 else 1)
    (hflow : (∑ i ∈ Finset.range k, w (n + i)) = (L.map w).sum + extra) :
    w o = (∑ i ∈ Finset.range n, L.count i * w i) + extra := by
  have hsplit := sum_map_eq_sum_count_range (n + k) L w hbound
  rw [Finset.sum_range_add] at hsplit
  have hcancel :
      (∑ i ∈ Finset.range k, L.count (n + i) * w (n + i)) + w o =
        ∑ i ∈ Finset.range k, w (n + i) := by
    have heach (i : ℕ) (hi : i ∈ Finset.range k) :
        L.count (n + i) * w (n + i) + (if n + i = o then w o else 0) = w (n + i) := by
      rw [hinternal (n + i) (by omega) (by have hi' := Finset.mem_range.mp hi; omega)]
      by_cases heq : n + i = o
      · simp [heq]
      · simp [heq]
    have hsum := Finset.sum_congr rfl heach
    rw [Finset.sum_add_distrib] at hsum
    have hsingle : (∑ i ∈ Finset.range k, if n + i = o then w o else 0) = w o := by
      have hm : o - n ∈ Finset.range k := by simp; omega
      have heq (i : ℕ) : n + i = o ↔ i = o - n := by omega
      simp_rw [heq]
      simp [hm]
    rw [hsingle] at hsum
    exact hsum
  omega


end PEqualNP.Outside.L_meta_18791_aux.FlowCount

namespace PEqualNP.Outside.L_meta_18791_aux.FlowCount

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

lemma gate_balance_extra (n : ℕ) (gs : List Gate) (w e : ℕ → ℕ)
    (recurrence : ∀ p g, gs[p]? = some g →
      w (n + p) = (g.inputs.map w).sum + e (n + p)) :
    (∑ p ∈ Finset.range gs.length, w (n + p)) =
      ((gs.flatMap Gate.inputs).map w).sum +
        ∑ p ∈ Finset.range gs.length, e (n + p) := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    have hzero : w n = (g.inputs.map w).sum + e n := by
      simpa using recurrence 0 g rfl
    have htail : ∀ p h, gs[p]? = some h →
        w (n + 1 + p) = (h.inputs.map w).sum + e (n + 1 + p) := by
      intro p h hp
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        recurrence (p + 1) h (by simpa using hp)
    have ht := ih (n + 1) htail
    rw [List.length_cons, Finset.sum_range_succ', Finset.sum_range_succ']
    simpa [List.flatMap_cons, List.map_append, List.sum_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hzero] using
      congrArg (fun a => a + w n) ht

lemma one_source_weight (n : ℕ) (gs : List Gate) (out cut : ℕ) (w : ℕ → ℕ)
    (hcutn : n ≤ cut) (hcutlen : cut < n + gs.length)
    (houtn : n ≤ out) (houtlen : out < n + gs.length)
    (clean : ∀ p g, gs[p]? = some g → ∀ a ∈ g.inputs, a < n + p)
    (internal : ∀ i, n ≤ i → i < n + gs.length →
      (gs.flatMap Gate.inputs).count i = if i = out then 0 else 1)
    (raw : ∀ i, i < n → w i = 0) (source : w cut = 1)
    (recurrence : ∀ p g, gs[p]? = some g → n + p ≠ cut →
      w (n + p) = (g.inputs.map w).sum) :
    w out = 1 := by
  have before : ∀ i, i < cut → w i = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hic
      by_cases hin : i < n
      · exact raw i hin
      · have hp : i - n < gs.length := by omega
        let g := gs[i - n]
        have hget : gs[i - n]? = some g := by simp [g, hp]
        have heq : n + (i - n) = i := by omega
        have hr := recurrence (i - n) g hget (by omega)
        rw [heq] at hr
        rw [hr]
        apply List.sum_eq_zero
        intro value hvalue
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hvalue
        have hai := clean (i - n) g hget a ha
        apply ih a (by omega)
        omega
  have sourceParents : ∀ p g, gs[p]? = some g → n + p = cut →
      (g.inputs.map w).sum = 0 := by
    intro p g hp hpc
    apply List.sum_eq_zero
    intro value hvalue
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hvalue
    exact before a (by have := clean p g hp a ha; omega)
  have recurrenceExtra : ∀ p g, gs[p]? = some g →
      w (n + p) = (g.inputs.map w).sum + (if n + p = cut then 1 else 0) := by
    intro p g hp
    by_cases heq : n + p = cut
    · rw [sourceParents p g hp heq, heq, source]
      simp
    · rw [recurrence p g hp heq]
      simp [heq]
  have flow := gate_balance_extra n gs w (fun i => if i = cut then 1 else 0)
    recurrenceExtra
  have extra : (∑ p ∈ Finset.range gs.length, if n + p = cut then 1 else 0) = 1 := by
    have hc : cut - n ∈ Finset.range gs.length := by simp; omega
    have heq (p : ℕ) : n + p = cut ↔ p = cut - n := by omega
    simp_rw [heq]
    simp [hc]
  rw [extra] at flow
  have bound : ∀ a ∈ gs.flatMap Gate.inputs, a < n + gs.length := by
    intro a ha
    obtain ⟨g, hg, hag⟩ := List.mem_flatMap.mp ha
    obtain ⟨p, hp, hpg⟩ := List.mem_iff_getElem.mp hg
    have hget : gs[p]? = some g := List.getElem?_eq_some_iff.mpr ⟨hp, hpg⟩
    have := clean p g hget a hag
    omega
  have balance := weighted_conservation_extra n gs.length out 1
    (gs.flatMap Gate.inputs) w houtn houtlen bound internal flow
  have rawSum : (∑ i ∈ Finset.range n, (gs.flatMap Gate.inputs).count i * w i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [raw i (Finset.mem_range.mp hi)]
    simp
  simpa [rawSum] using balance

end PEqualNP.Outside.L_meta_18791_aux.FlowCount


namespace HelperOneContext

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open HelperOneFormula

lemma context_hole_count (gs : List Gate) (cut out : ℕ)
    (hc : CleanL 7 gs) (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hcutn : 7 ≤ cut) (hcutlen : cut < 7 + gs.length)
    (houtn : 7 ≤ out) (houtlen : out < 7 + gs.length)
    (internal : ∀ i, 7 ≤ i → i < 7 + gs.length →
      (gs.flatMap Gate.inputs).count i = if i = out then 0 else 1) :
    count (contextFormula gs cut out) 7 = 1 := by
  have hb := binary_of_clean hc hops
  apply PEqualNP.Outside.L_meta_18791_aux.FlowCount.one_source_weight 7 gs out cut
    (fun z => count (contextFormula gs cut z) 7) hcutn hcutlen houtn houtlen
  · intro p g hp a ha
    obtain ⟨u, v, hu, hv, hin, _⟩ := hb p g hp
    simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hv
  · exact internal
  · exact fun a ha => context_hole_at_input gs hcutn ha
  · exact context_hole_at_cut gs cut
  · exact fun p g hp hne => context_count_gate hb hp hne 7

end HelperOneContext


namespace HelperOneActualCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_18791_aux.FlowCount
open PetersenCutFormula PetersenScratch
open HelperOneFormula HelperOnePlug HelperOneContext HelperOneSemantics

lemma no_sharing_circuit_obstruction_of_hole_one
    (C : Circuit) (clean : CleanL 7 C.gates)
    (ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hon : 7 ≤ C.output) (hout : C.output < 7 + C.gates.length)
    (internal_counts : ∀ i, 7 ≤ i → i < 7 + C.gates.length →
      (operands C.gates).count i = if i = C.output then 0 else 1)
    (p h : Nat) (g : Gate) (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (hole_one : count (contextFormula C.gates (7 + p) C.output) 7 = 1)
    (D : Finset (Fin 7)) (hcard : D.card = 4) (hzero : 0 ∉ D)
    (hcover : ∀ i : Fin 7, i ∈ D ∨ i + 1 ∈ D)
    (budget : ∀ j : Fin 7, (operands C.gates).count j.val ≤ if j ∈ D then 2 else 1)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (witness : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      (C.wires (List.ofFn x)).getD h false = true) : False := by
  have hb : BinaryAndOr C.gates := binary_of_clean clean ops
  have hp : p < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hhrange : h < 7 + C.gates.length := by omega
  let H : DMFormula 7 := wireFormula 0 C.gates h
  let K : DMFormula 8 := contextFormula C.gates (7 + p) C.output
  have hK : positive K := context_positive hb (by omega) hout
  have hH : positive H := mate_positive hb hg hh
  apply formula_obstruction_original_cover K H D hK hH hole_one
  · intro x
    rw [positiveBind_eval _ K hK x]
    exact (context_eval_circuit C clean hb hg hop hin hh hout x).trans (computes x)
  · obtain ⟨x, hx0, hx1, hx6, hxH⟩ := witness
    refine ⟨x, hx0, hx1, hx6, ?_⟩
    change (wireFormula (0 : Fin 7) C.gates h).eval x = true
    rw [mate_eval_circuit C clean hhrange x]
    exact hxH
  · exact hcard
  · exact hzero
  · exact hcover
  · intro j
    change count (positiveBind (plug (wireFormula (0 : Fin 7) C.gates h))
      (contextFormula C.gates (7 + p) C.output)) j ≤ _
    rw [actual_plug_count hb hg hop hin hh hout j, count_eq_occurrences]
    rw [wireFormula_occurrences_eq_operand_count (0 : Fin 7) j clean C.output hon hout internal_counts]
    exact budget j

lemma context_hole_one (C : Circuit) (clean : CleanL 7 C.gates)
    (hb : BinaryAndOr C.gates) (hon : 7 ≤ C.output) (hout : C.output < 7 + C.gates.length)
    (internal_counts : ∀ i, 7 ≤ i → i < 7 + C.gates.length →
      (operands C.gates).count i = if i = C.output then 0 else 1)
    (cut : Nat) (hcutn : 7 ≤ cut) (hcutlen : cut < 7 + C.gates.length) :
    count (contextFormula C.gates cut C.output) 7 = 1 := by
  apply one_source_weight 7 C.gates C.output cut
    (fun w => count (contextFormula C.gates cut w) 7)
    hcutn hcutlen hon hout
  · intro p g hg a ha
    exact (clean p g hg).lt a ha
  · exact internal_counts
  · intro i hi
    exact context_hole_at_input C.gates hcutn hi
  · exact context_hole_at_cut C.gates cut
  · intro p g hg hne
    exact context_count_gate hb hg hne 7

lemma no_sharing_circuit_obstruction
    (C : Circuit) (clean : CleanL 7 C.gates)
    (ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hon : 7 ≤ C.output) (hout : C.output < 7 + C.gates.length)
    (internal_counts : ∀ i, 7 ≤ i → i < 7 + C.gates.length →
      (operands C.gates).count i = if i = C.output then 0 else 1)
    (p h : Nat) (g : Gate) (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [0, h] ∨ g.inputs = [h, 0]) (hh : h < 7 + p)
    (D : Finset (Fin 7)) (hcard : D.card = 4) (hzero : 0 ∉ D)
    (hcover : ∀ i : Fin 7, i ∈ D ∨ i + 1 ∈ D)
    (budget : ∀ j : Fin 7, (operands C.gates).count j.val ≤ if j ∈ D then 2 else 1)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (witness : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      (C.wires (List.ofFn x)).getD h false = true) : False := by
  have hb : BinaryAndOr C.gates := binary_of_clean clean ops
  have hp : p < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hole_one := context_hole_one C clean hb hon hout internal_counts (7 + p)
    (by omega) (by omega)
  exact no_sharing_circuit_obstruction_of_hole_one C clean ops hon hout internal_counts
    p h g hg hop hin hh hole_one D hcard hzero hcover budget computes witness

end HelperOneActualCircuit


namespace HelperReaderShape

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma binary_list_of_two_members (xs : List Nat) (hlen : xs.length ≤ 2)
    (h : Nat) (hzero : 0 ∈ xs) (hmem : h ∈ xs) (hne : h ≠ 0) :
    xs = [0,h] ∨ xs = [h,0] := by
  cases xs with
  | nil => simp at hzero
  | cons a xs =>
    cases xs with
    | nil => simp_all
    | cons b xs =>
      cases xs with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzero hmem
        rcases hzero with rfl | rfl <;> simp_all
      | cons c xs => simp at hlen

lemma reader_inputs (C : Circuit) (hf : FanInTwo C)
    (i : Fin C.gates.length) (h : Nat)
    (hzero : 0 ∈ (C.gates.get i).inputs)
    (hmem : h ∈ (C.gates.get i).inputs) (hne : h ≠ 0) :
    (C.gates.get i).inputs = [0,h] ∨ (C.gates.get i).inputs = [h,0] := by
  apply binary_list_of_two_members _ (hf _ (List.get_mem _ _)).2 h hzero hmem hne

lemma flatMap_count (gs : List Gate) (a : Nat) :
    (gs.flatMap Gate.inputs).count a = (gs.map fun g => g.inputs.count a).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [ih]

lemma unique_reader_operand_count (C : Circuit) (hf : FanInTwo C)
    (i : Fin C.gates.length) (h : Nat)
    (hzero : 0 ∈ (C.gates.get i).inputs)
    (unique : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hmem : h ∈ (C.gates.get i).inputs) (hne : h ≠ 0) :
    (C.gates.flatMap Gate.inputs).count 0 = 1 := by
  classical
  have shape := reader_inputs C hf i h hzero hmem hne
  have counts (j : Fin C.gates.length) :
      (C.gates.get j).inputs.count 0 = if j = i then 1 else 0 := by
    by_cases eq : j = i
    · subst j
      rcases shape with shape | shape <;> rw [shape] <;> simp [hne, Ne.symm hne]
    · have absent : 0 ∉ (C.gates.get j).inputs := fun h => eq (unique j h)
      rw [if_neg eq]
      exact List.count_eq_zero.mpr absent
  rw [flatMap_count]
  have values : (C.gates.map fun g => g.inputs.count 0) =
      List.ofFn (fun j : Fin C.gates.length => if j = i then 1 else 0) := by
    conv_lhs => rw [← List.ofFn_get C.gates]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact counts j
  rw [values, List.sum_ofFn]
  simp

end HelperReaderShape



namespace Root18791Final

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1549_aux
open PEqualNP.Outside.L_meta_1549_aux.PEqualNP.MetaComplexity.Helpers
open PetersenCutTrace PetersenFirstGroup H5C7Preview

lemma impossible_reader (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool,
      C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
        (x 5 && x 6) || (x 6 && x 0)))
    (i : Fin C.gates.length) (h : Nat)
    (zero : 0 ∈ (C.gates.get i).inputs)
    (sole : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (op : (C.gates.get i).op = GateOp.or)
    (mate : h ∈ (C.gates.get i).inputs) (ne : h ≠ 0) (before : h < 7 + i.val)
    (witness : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      (C.wires (List.ofFn x)).getD h false = true) : False := by
  classical
  let least := HelperReviewEquality.raw_least C hf hs he
  let out : Fin (7 + C.gates.length) := ⟨C.output, c7_output_valid least⟩
  let live := least_read_edge_live least c7_nonconstant c7_depends c7_restrict_nonconstant
    (c7_output_valid least)
  let label := firstInputBoundary least.hcl out live
  let D := H5C7Cover.earlierCover label
  have budget := cofactor18791_cover_counts C hf hs he
  change D.card = 4 ∧ H5C7Cover.covers D ∧
    (∀ v : Fin 7, (operands C.gates).count v.val = if v ∈ D then 2 else 1) at budget
  have countZero := HelperReaderShape.unique_reader_operand_count C hf i h zero sole mate ne
  have zeroOutside : (0 : Fin 7) ∉ D := by
    intro inside
    have count := budget.2.2 0
    rw [if_pos inside] at count
    change (operands C.gates).count 0 = 2 at count
    change (operands C.gates).count 0 = 1 at countZero
    omega
  have last := cofactor18791_output_last C hf hs he
  have noNot := HelperReview.exact10_cycle7_has_no_not C hf hs he
  have ops := H5WireProperties.clean_and_or least.hcl noNot
  have gateAt : C.gates[i.val]? = some (C.gates.get i) := List.getElem?_eq_getElem i.isLt
  exact HelperOneActualCircuit.no_sharing_circuit_obstruction C least.hcl ops
    (by omega) (c7_output_valid least) (cofactor18791_internal_counts C hf hs he)
    i.val h (C.gates.get i) gateAt op (HelperReaderShape.reader_inputs C hf i h zero mate ne)
    before D budget.1 zeroOutside budget.2.1 (fun j => (budget.2.2 j).le)
    he witness

end Root18791Final


end PEqualNP.Outside.L_meta_18791_aux

theorem PEqualNP.Outside.L_meta_18791 :
    ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧
      (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧
      0 ∈ (C.gates.get i).inputs ∧
      (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧
      h ∈ (C.gates.get i).inputs ∧ h ≠ 0 ∧ h < 7 + i.val ∧
      ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
        (C.wires (List.ofFn x)).getD h false = true) := by
  rintro ⟨C, i, k, h, hf, hs, he, zero, sole, op, andOp, earlier, reads, mate, ne, before, witness⟩
  exact PEqualNP.Outside.L_meta_18791_aux.Root18791Final.impossible_reader C hf hs he i h zero sole op mate ne before witness
