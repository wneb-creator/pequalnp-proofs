import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

section RowTransport

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma build_map_on (ops : α → α → Finset α) (ops' : β → β → Finset β)
    (D : α → Prop) (f : α → β)
    (closed : ∀ a b, D a → D b → ∀ z ∈ ops a b, D z)
    (injectiveOn : ∀ a b, D a → D b → f a = f b → a = b)
    (respects : ∀ a b, D a → D b → ∀ z ∈ ops a b, f z ∈ ops' (f a) (f b))
    {goal : α} {budget : ℕ} {available : Finset α}
    (initial : ∀ a ∈ available, D a) (run : build ops goal budget available) :
    build ops' (f goal) budget (available.image f) := by
  induction budget generalizing available with
  | zero =>
    exact Finset.mem_image.mpr ⟨goal, run, rfl⟩
  | succ budget ih =>
    rcases run with skip | ⟨a, ha, b, hb, distinct, z, hz, tail⟩
    · exact Or.inl (ih initial skip)
    · have da : D a := initial a ha
      have db : D b := initial b hb
      have next : ∀ u ∈ insert z available, D u := by
        intro u hu
        rcases Finset.mem_insert.mp hu with he | hu
        · rw [he]
          exact closed a b da db z hz
        · exact initial u hu
      refine Or.inr ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
        fun he => distinct (injectiveOn a b da db he),
        f z, respects a b da db z hz, ?_⟩
      simpa only [Finset.image_insert] using ih next tail

lemma live_map_on (ops : α → α → Finset α) (ops' : β → β → Finset β)
    (D : α → Prop) (f : α → β)
    (closed : ∀ a b, D a → D b → ∀ z ∈ ops a b, D z)
    (injectiveOn : ∀ a b, D a → D b → f a = f b → a = b)
    (respects : ∀ a b, D a → D b → ∀ z ∈ ops a b, f z ∈ ops' (f a) (f b))
    {goal : α} {budget : ℕ} {available : Finset α}
    (initial : ∀ a ∈ available, D a) (run : live ops goal budget available) :
    live ops' (f goal) budget (available.image f) := by
  induction budget generalizing available with
  | zero =>
    change available = {goal} at run
    simp only [live, run, Finset.image_singleton]
  | succ budget ih =>
    rcases run with skip | ⟨a, ha, b, hb, distinct, z, hz, fresh, rest, hs, tail⟩
    · exact Or.inl (ih initial skip)
    · have da : D a := initial a ha
      have db : D b := initial b hb
      have dz : D z := closed a b da db z hz
      have restIn : rest ⊆ available := by
        intro u hu
        rw [hs]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
      have next : ∀ u ∈ insert z rest, D u := by
        intro u hu
        rcases Finset.mem_insert.mp hu with he | hu
        · simpa only [he] using dz
        · exact initial u (restIn hu)
      have freshImage : f z ∉ available.image f := by
        intro hmem
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hmem
        exact fresh ((injectiveOn u z (initial u hu) dz he) ▸ hu)
      refine Or.inr ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
        fun he => distinct (injectiveOn a b da db he),
        f z, respects a b da db z hz, freshImage,
        rest.image f, ?_, ?_⟩
      · rw [hs, Finset.image_insert, Finset.image_insert]
      · simpa only [Finset.image_insert] using ih next tail

end RowTransport

def pullback {m n : ℕ} (ρ : Fin n → Fin m) (w : BitVec m) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun j => w[(ρ j).val]))).cast (by simp)

lemma pullback_bit {m n : ℕ} (ρ : Fin n → Fin m) (w : BitVec m) (j : Fin n) :
    (pullback ρ w)[j.val] = w[(ρ j).val] := by
  simp [pullback, ← BitVec.getLsbD_eq_getElem]

lemma pullback_zero {m n : ℕ} (ρ : Fin n → Fin m) : pullback ρ 0 = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa using pullback_bit ρ 0 ⟨i, hi⟩

lemma pullback_not {m n : ℕ} (ρ : Fin n → Fin m) (w : BitVec m) :
    pullback ρ (~~~w) = ~~~(pullback ρ w) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [BitVec.getElem_not, pullback_bit ρ w ⟨i, hi⟩] using
    pullback_bit ρ (~~~w) ⟨i, hi⟩

lemma pullback_and {m n : ℕ} (ρ : Fin n → Fin m) (u w : BitVec m) :
    pullback ρ (u &&& w) = pullback ρ u &&& pullback ρ w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [BitVec.getElem_and, pullback_bit ρ u ⟨i, hi⟩,
    pullback_bit ρ w ⟨i, hi⟩] using pullback_bit ρ (u &&& w) ⟨i, hi⟩

lemma pullback_or {m n : ℕ} (ρ : Fin n → Fin m) (u w : BitVec m) :
    pullback ρ (u ||| w) = pullback ρ u ||| pullback ρ w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [BitVec.getElem_or, pullback_bit ρ u ⟨i, hi⟩,
    pullback_bit ρ w ⟨i, hi⟩] using pullback_bit ρ (u ||| w) ⟨i, hi⟩

def patternEq {m : ℕ} (roots : Finset (BitVec m)) (i j : Fin m) : Prop :=
  ∀ w ∈ roots, w[i.val] = w[j.val]

def patternStable {m : ℕ} (roots : Finset (BitVec m)) (w : BitVec m) : Prop :=
  ∀ i j : Fin m, patternEq roots i j → w[i.val] = w[j.val]

lemma patternStable_root {m : ℕ} (roots : Finset (BitVec m)) (w : BitVec m)
    (hw : w ∈ roots) : patternStable roots w := by
  intro i j h
  exact h w hw

lemma patternStable_not {m : ℕ} {roots : Finset (BitVec m)} {w : BitVec m}
    (h : patternStable roots w) : patternStable roots (~~~w) := by
  intro i j he
  simp only [BitVec.getElem_not, h i j he]

lemma patternStable_and {m : ℕ} {roots : Finset (BitVec m)} {u w : BitVec m}
    (hu : patternStable roots u) (hw : patternStable roots w) :
    patternStable roots (u &&& w) := by
  intro i j he
  simp only [BitVec.getElem_and, hu i j he, hw i j he]

lemma patternStable_or {m : ℕ} {roots : Finset (BitVec m)} {u w : BitVec m}
    (hu : patternStable roots u) (hw : patternStable roots w) :
    patternStable roots (u ||| w) := by
  intro i j he
  simp only [BitVec.getElem_or, hu i j he, hw i j he]

lemma pullback_injective_stable {m n : ℕ} {roots : Finset (BitVec m)}
    (ρ : Fin n → Fin m)
    (cover : ∀ i : Fin m, ∃ j : Fin n, patternEq roots i (ρ j))
    (u w : BitVec m) (hu : patternStable roots u) (hw : patternStable roots w)
    (he : pullback ρ u = pullback ρ w) : u = w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨j, hj⟩ := cover ⟨i, hi⟩
  have hb := congrArg (fun z : BitVec n => z[j.val]) he
  rw [pullback_bit, pullback_bit] at hb
  exact (hu ⟨i, hi⟩ (ρ j) hj).trans (hb.trans (hw ⟨i, hi⟩ (ρ j) hj).symm)

def ops {width : ℕ} (x y : BitVec width) : List (BitVec width) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps {width : ℕ} (a b : BitVec width) : Finset (BitVec width) :=
  (ops a b).toFinset

lemma patternStable_ops {m : ℕ} {roots : Finset (BitVec m)}
    (u w : BitVec m) (hu : patternStable roots u) (hw : patternStable roots w)
    (z : BitVec m) (hz : z ∈ basicOps u w) : patternStable roots z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact patternStable_and hu hw
  · exact patternStable_or hu hw
  · exact patternStable_and hu (patternStable_not hw)
  · exact patternStable_and hw (patternStable_not hu)

lemma pullback_ops {m n : ℕ} (ρ : Fin n → Fin m) (u w z : BitVec m)
    (hz : z ∈ basicOps u w) : pullback ρ z ∈ basicOps (pullback ρ u) (pullback ρ w) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp [basicOps, ops, pullback_and, pullback_or, pullback_not]

lemma build_pullback {m n budget : ℕ} {roots : Finset (BitVec m)} {goal : BitVec m}
    (ρ : Fin n → Fin m)
    (cover : ∀ i : Fin m, ∃ j : Fin n, patternEq roots i (ρ j))
    (run : build basicOps goal budget roots) :
    build basicOps (pullback ρ goal) budget (roots.image (pullback ρ)) := by
  exact build_map_on basicOps basicOps (patternStable roots) (pullback ρ)
    (patternStable_ops) (pullback_injective_stable ρ cover)
    (fun a b _ _ z hz => pullback_ops ρ a b z hz)
    (patternStable_root roots) run

lemma live_pullback {m n budget : ℕ} {roots : Finset (BitVec m)} {goal : BitVec m}
    (ρ : Fin n → Fin m)
    (cover : ∀ i : Fin m, ∃ j : Fin n, patternEq roots i (ρ j))
    (run : live basicOps goal budget roots) :
    live basicOps (pullback ρ goal) budget (roots.image (pullback ρ)) := by
  exact live_map_on basicOps basicOps (patternStable roots) (pullback ρ)
    (patternStable_ops) (pullback_injective_stable ρ cover)
    (fun a b _ _ z hz => pullback_ops ρ a b z hz)
    (patternStable_root roots) run

def frontierRoots {k m : ℕ} (front : Fin k → BitVec m) : Finset (BitVec m) :=
  Finset.univ.image front

def rowsMatch {k m n : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n) : Prop :=
  ∀ i : Fin m, ∃ j : Fin n, goal[i.val] = goal'[j.val] ∧
    ∀ q : Fin k, (front q)[i.val] = (front' q)[j.val]

lemma matching_rows_pullback {k m n : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (forth : rowsMatch front goal front' goal')
    (back : rowsMatch front' goal' front goal) :
    ∃ ρ : Fin n → Fin m,
      (∀ i : Fin m, ∃ j : Fin n, patternEq (frontierRoots front) i (ρ j)) ∧
      pullback ρ goal = goal' ∧
      (frontierRoots front).image (pullback ρ) = frontierRoots front' := by
  classical
  let ρ : Fin n → Fin m := fun j => Classical.choose (back j)
  have matchρ : ∀ j : Fin n, goal'[j.val] = goal[(ρ j).val] ∧
      ∀ q : Fin k, (front' q)[j.val] = (front q)[(ρ j).val] :=
    fun j => Classical.choose_spec (back j)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, _, hj⟩ := forth i
    refine ⟨j, ?_⟩
    intro w hw
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hj q).trans ((matchρ j).2 q)
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [pullback_bit ρ goal ⟨i, hi⟩]
    exact ((matchρ ⟨i, hi⟩).1).symm
  · have column : ∀ q : Fin k, pullback ρ (front q) = front' q := by
      intro q
      apply BitVec.eq_of_getElem_eq
      intro i hi
      rw [pullback_bit ρ (front q) ⟨i, hi⟩]
      exact ((matchρ ⟨i, hi⟩).2 q).symm
    unfold frontierRoots
    rw [Finset.image_image]
    congr 1
    funext q
    exact column q

lemma build_iff_matching_rows {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (forth : rowsMatch front goal front' goal')
    (back : rowsMatch front' goal' front goal) :
    build basicOps goal budget (frontierRoots front) ↔
      build basicOps goal' budget (frontierRoots front') := by
  constructor
  · intro run
    obtain ⟨ρ, cover, hg, hr⟩ := matching_rows_pullback front goal front' goal' forth back
    simpa only [hg, hr] using build_pullback ρ cover run
  · intro run
    obtain ⟨ρ, cover, hg, hr⟩ := matching_rows_pullback front' goal' front goal back forth
    simpa only [hg, hr] using build_pullback ρ cover run

lemma live_iff_matching_rows {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (forth : rowsMatch front goal front' goal')
    (back : rowsMatch front' goal' front goal) :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') := by
  constructor
  · intro run
    obtain ⟨ρ, cover, hg, hr⟩ := matching_rows_pullback front goal front' goal' forth back
    simpa only [hg, hr] using live_pullback ρ cover run
  · intro run
    obtain ⟨ρ, cover, hg, hr⟩ := matching_rows_pullback front' goal' front goal back forth
    simpa only [hg, hr] using live_pullback ρ cover run

def labeledPatterns {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m) :
    Set (Bool × (Fin k → Bool)) :=
  Set.range (fun i : Fin m => (goal[i.val], fun q => (front q)[i.val]))

lemma rowsMatch_of_patterns_eq {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (same : labeledPatterns front goal = labeledPatterns front' goal') :
    rowsMatch front goal front' goal' := by
  intro i
  have hm : (goal[i.val], fun q => (front q)[i.val]) ∈ labeledPatterns front goal :=
    ⟨i, rfl⟩
  rw [same] at hm
  obtain ⟨j, hj⟩ := hm
  refine ⟨j, (congrArg Prod.fst hj).symm, ?_⟩
  intro q
  exact (congrArg (fun p => p.2 q) hj).symm

lemma build_iff_labeledPatterns {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (same : labeledPatterns front goal = labeledPatterns front' goal') :
    build basicOps goal budget (frontierRoots front) ↔
      build basicOps goal' budget (frontierRoots front') :=
  build_iff_matching_rows front goal front' goal'
    (rowsMatch_of_patterns_eq front goal front' goal' same)
    (rowsMatch_of_patterns_eq front' goal' front goal same.symm)

lemma live_iff_labeledPatterns {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (same : labeledPatterns front goal = labeledPatterns front' goal') :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') :=
  live_iff_matching_rows front goal front' goal'
    (rowsMatch_of_patterns_eq front goal front' goal' same)
    (rowsMatch_of_patterns_eq front' goal' front goal same.symm)

end PEqualNP.Outside.L_meta_10760
