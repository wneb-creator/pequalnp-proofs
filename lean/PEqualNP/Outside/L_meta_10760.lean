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

lemma rowsMatch_not {k m n : ℕ}
    {front : Fin k → BitVec m} {goal : BitVec m}
    {front' : Fin k → BitVec n} {goal' : BitVec n}
    (h : rowsMatch front goal front' goal') :
    rowsMatch front (~~~goal) front' (~~~goal') := by
  intro i
  obtain ⟨j, hg, hf⟩ := h i
  refine ⟨j, ?_, hf⟩
  simp only [BitVec.getElem_not, hg]

lemma build_signed_iff_matching_rows {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (forth : rowsMatch front goal front' goal')
    (back : rowsMatch front' goal' front goal) :
    (build basicOps goal budget (frontierRoots front) ∨
      build basicOps (~~~goal) budget (frontierRoots front)) ↔
    (build basicOps goal' budget (frontierRoots front') ∨
      build basicOps (~~~goal') budget (frontierRoots front')) := by
  exact or_congr (build_iff_matching_rows front goal front' goal' forth back)
    (build_iff_matching_rows front (~~~goal) front' (~~~goal')
      (rowsMatch_not forth) (rowsMatch_not back))

lemma live_signed_iff_matching_rows {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (forth : rowsMatch front goal front' goal')
    (back : rowsMatch front' goal' front goal) :
    (live basicOps goal budget (frontierRoots front) ∨
      live basicOps (~~~goal) budget (frontierRoots front)) ↔
    (live basicOps goal' budget (frontierRoots front') ∨
      live basicOps (~~~goal') budget (frontierRoots front')) := by
  exact or_congr (live_iff_matching_rows front goal front' goal' forth back)
    (live_iff_matching_rows front (~~~goal) front' (~~~goal')
      (rowsMatch_not forth) (rowsMatch_not back))

lemma build_signed_iff_swappedPatterns {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (same : labeledPatterns front goal = labeledPatterns front' (~~~goal')) :
    (build basicOps goal budget (frontierRoots front) ∨
      build basicOps (~~~goal) budget (frontierRoots front)) ↔
    (build basicOps goal' budget (frontierRoots front') ∨
      build basicOps (~~~goal') budget (frontierRoots front')) := by
  have h := build_signed_iff_matching_rows (budget := budget) front goal front' (~~~goal')
    (rowsMatch_of_patterns_eq front goal front' (~~~goal') same)
    (rowsMatch_of_patterns_eq front' (~~~goal') front goal same.symm)
  simp only [BitVec.not_not] at h
  exact h.trans or_comm

lemma live_signed_iff_swappedPatterns {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (same : labeledPatterns front goal = labeledPatterns front' (~~~goal')) :
    (live basicOps goal budget (frontierRoots front) ∨
      live basicOps (~~~goal) budget (frontierRoots front)) ↔
    (live basicOps goal' budget (frontierRoots front') ∨
      live basicOps (~~~goal') budget (frontierRoots front')) := by
  have h := live_signed_iff_matching_rows (budget := budget) front goal front' (~~~goal')
    (rowsMatch_of_patterns_eq front goal front' (~~~goal') same)
    (rowsMatch_of_patterns_eq front' (~~~goal') front goal same.symm)
  simp only [BitVec.not_not] at h
  exact h.trans or_comm

lemma frontierRoots_reindex {k l m : ℕ} (front : Fin k → BitVec m)
    (e : Fin l ≃ Fin k) : frontierRoots (front ∘ e) = frontierRoots front := by
  unfold frontierRoots
  ext w
  constructor
  · intro h
    obtain ⟨q, _, he⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨e q, Finset.mem_univ _, he⟩
  · intro h
    obtain ⟨q, _, he⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨e.symm q, Finset.mem_univ _, by simpa using he⟩

lemma build_iff_reindex {k l m budget : ℕ} (front : Fin k → BitVec m)
    (e : Fin l ≃ Fin k) (goal : BitVec m) :
    build basicOps goal budget (frontierRoots (front ∘ e)) ↔
      build basicOps goal budget (frontierRoots front) := by
  rw [frontierRoots_reindex]

lemma live_iff_reindex {k l m budget : ℕ} (front : Fin k → BitVec m)
    (e : Fin l ≃ Fin k) (goal : BitVec m) :
    live basicOps goal budget (frontierRoots (front ∘ e)) ↔
      live basicOps goal budget (frontierRoots front) := by
  rw [frontierRoots_reindex]

def rowPattern {k m : ℕ} (front : Fin k → BitVec m) (i : Fin m) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn (fun q => (front q)[i.val]))).cast (by simp)

lemma rowPattern_bit {k m : ℕ} (front : Fin k → BitVec m) (i : Fin m) (q : Fin k) :
    (rowPattern front i)[q.val] = (front q)[i.val] := by
  simp [rowPattern, ← BitVec.getLsbD_eq_getElem]

lemma rowPattern_eq_iff {k m n : ℕ} (front : Fin k → BitVec m)
    (front' : Fin k → BitVec n) (i : Fin m) (j : Fin n) :
    rowPattern front i = rowPattern front' j ↔
      ∀ q : Fin k, (front q)[i.val] = (front' q)[j.val] := by
  constructor
  · intro h q
    have he := congrArg (fun w : BitVec k => w[q.val]) h
    simpa only [rowPattern_bit] using he
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro q hq
    rw [rowPattern_bit front i ⟨q, hq⟩, rowPattern_bit front' j ⟨q, hq⟩]
    exact h ⟨q, hq⟩

def patternKey {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) : Finset (BitVec k) :=
  (Finset.univ.filter (fun i : Fin m => goal[i.val] = value)).image (rowPattern front)

abbrev positivePatterns {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m) :
    Finset (BitVec k) := patternKey front goal true

abbrev negativePatterns {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m) :
    Finset (BitVec k) := patternKey front goal false

lemma mem_patternKey {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) (p : BitVec k) :
    p ∈ patternKey front goal value ↔
      ∃ i : Fin m, goal[i.val] = value ∧ rowPattern front i = p := by
  simp only [patternKey, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

lemma rowsMatch_of_keys_eq {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = positivePatterns front' goal')
    (negative : negativePatterns front goal = negativePatterns front' goal') :
    rowsMatch front goal front' goal' := by
  intro i
  have same : patternKey front goal goal[i.val] = patternKey front' goal' goal[i.val] := by
    cases goal[i.val]
    · exact negative
    · exact positive
  have hm : rowPattern front i ∈ patternKey front goal goal[i.val] :=
    (mem_patternKey front goal goal[i.val] _).mpr ⟨i, rfl, rfl⟩
  rw [same] at hm
  obtain ⟨j, hj, hp⟩ := (mem_patternKey front' goal' goal[i.val] _).mp hm
  exact ⟨j, hj.symm, (rowPattern_eq_iff front front' i j).mp hp.symm⟩

lemma labeledPatterns_eq_of_rowsMatch {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (forth : rowsMatch front goal front' goal')
    (back : rowsMatch front' goal' front goal) :
    labeledPatterns front goal = labeledPatterns front' goal' := by
  apply Set.Subset.antisymm
  · rintro p ⟨i, rfl⟩
    obtain ⟨j, hg, hf⟩ := forth i
    exact ⟨j, Prod.ext hg.symm (funext (fun q => (hf q).symm))⟩
  · rintro p ⟨j, rfl⟩
    obtain ⟨i, hg, hf⟩ := back j
    exact ⟨i, Prod.ext hg.symm (funext (fun q => (hf q).symm))⟩

lemma labeledPatterns_eq_of_keys_eq {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = positivePatterns front' goal')
    (negative : negativePatterns front goal = negativePatterns front' goal') :
    labeledPatterns front goal = labeledPatterns front' goal' :=
  labeledPatterns_eq_of_rowsMatch front goal front' goal'
    (rowsMatch_of_keys_eq front goal front' goal' positive negative)
    (rowsMatch_of_keys_eq front' goal' front goal positive.symm negative.symm)

lemma patternKey_not {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) : patternKey front (~~~goal) value = patternKey front goal (!value) := by
  unfold patternKey
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, BitVec.getElem_not]
  cases goal[i.val] <;> cases value <;> decide

lemma labeledPatterns_eq_of_swappedKeys {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = negativePatterns front' goal')
    (negative : negativePatterns front goal = positivePatterns front' goal') :
    labeledPatterns front goal = labeledPatterns front' (~~~goal') := by
  apply labeledPatterns_eq_of_keys_eq front goal front' (~~~goal')
  · simpa only [positivePatterns, negativePatterns, patternKey_not, Bool.not_true] using positive
  · simpa only [positivePatterns, negativePatterns, patternKey_not, Bool.not_false] using negative

lemma build_iff_patternKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = positivePatterns front' goal')
    (negative : negativePatterns front goal = negativePatterns front' goal') :
    build basicOps goal budget (frontierRoots front) ↔
      build basicOps goal' budget (frontierRoots front') :=
  build_iff_labeledPatterns front goal front' goal'
    (labeledPatterns_eq_of_keys_eq front goal front' goal' positive negative)

lemma live_iff_patternKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = positivePatterns front' goal')
    (negative : negativePatterns front goal = negativePatterns front' goal') :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') :=
  live_iff_labeledPatterns front goal front' goal'
    (labeledPatterns_eq_of_keys_eq front goal front' goal' positive negative)

lemma build_signed_iff_swappedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = negativePatterns front' goal')
    (negative : negativePatterns front goal = positivePatterns front' goal') :
    (build basicOps goal budget (frontierRoots front) ∨
      build basicOps (~~~goal) budget (frontierRoots front)) ↔
    (build basicOps goal' budget (frontierRoots front') ∨
      build basicOps (~~~goal') budget (frontierRoots front')) :=
  build_signed_iff_swappedPatterns front goal front' goal'
    (labeledPatterns_eq_of_swappedKeys front goal front' goal' positive negative)

lemma live_signed_iff_swappedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : positivePatterns front goal = negativePatterns front' goal')
    (negative : negativePatterns front goal = positivePatterns front' goal') :
    (live basicOps goal budget (frontierRoots front) ∨
      live basicOps (~~~goal) budget (frontierRoots front)) ↔
    (live basicOps goal' budget (frontierRoots front') ∨
      live basicOps (~~~goal') budget (frontierRoots front')) :=
  live_signed_iff_swappedPatterns front goal front' goal'
    (labeledPatterns_eq_of_swappedKeys front goal front' goal' positive negative)

def canonicalAt {m : ℕ} (ref : Fin m) (w : BitVec m) : BitVec m :=
  if w[ref.val] then ~~~w else w

lemma canonicalAt_bit {m : ℕ} (ref : Fin m) (w : BitVec m) :
    (canonicalAt ref w)[ref.val] = false := by
  cases h : w[ref.val] <;> simp [canonicalAt, h]

lemma canonicalAt_of_false {m : ℕ} (ref : Fin m) (w : BitVec m)
    (h : w[ref.val] = false) : canonicalAt ref w = w := by
  simp only [canonicalAt, h, Bool.false_eq_true, ite_false]

lemma canonicalAt_not {m : ℕ} (ref : Fin m) (w : BitVec m) :
    canonicalAt ref (~~~w) = canonicalAt ref w := by
  cases h : w[ref.val] <;> simp [canonicalAt, h]

lemma canonicalAt_eq_iff {m : ℕ} (ref : Fin m) (u w : BitVec m) :
    canonicalAt ref u = canonicalAt ref w ↔ u = w ∨ u = ~~~w := by
  constructor
  · intro h
    cases hu : u[ref.val] <;> cases hw : w[ref.val] <;>
      simp only [canonicalAt, hu, hw, Bool.false_eq_true,
        ite_false, ite_true] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by simpa only [BitVec.not_not] using congrArg (fun z => ~~~z) h)
    · exact Or.inl (by simpa only [BitVec.not_not] using congrArg (fun z => ~~~z) h)
  · rintro (rfl | rfl)
    · rfl
    · exact canonicalAt_not ref w

lemma canonicalAt_ops {m : ℕ} (ref : Fin m) (u w z : BitVec m)
    (hz : z ∈ basicOps u w) :
    canonicalAt ref z ∈ basicOps (canonicalAt ref u) (canonicalAt ref w) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals cases hu : u[ref.val] <;> cases hw : w[ref.val] <;>
    simp [canonicalAt, basicOps, ops, hu, hw, BitVec.not_and, BitVec.not_or,
      BitVec.and_comm, BitVec.or_comm]

lemma zeroAt_ops {m : ℕ} (ref : Fin m) (u w : BitVec m)
    (hu : u[ref.val] = false) (hw : w[ref.val] = false)
    (z : BitVec m) (hz : z ∈ basicOps u w) : z[ref.val] = false := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hu, hw]

lemma pullback_rowEquiv_injective {m n : ℕ} (e : Fin n ≃ Fin m) :
    Function.Injective (pullback e) := by
  intro u w he
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hb := congrArg (fun z : BitVec n => z[(e.symm ⟨i, hi⟩).val]) he
  simpa only [pullback_bit, Equiv.apply_symm_apply] using hb

def canonicalTransport {m n : ℕ} (e : Fin n ≃ Fin m) (ref : Fin n)
    (w : BitVec m) : BitVec n := canonicalAt ref (pullback e w)

lemma canonicalTransport_injective_zero {m n : ℕ}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (u w : BitVec m) (hu : u[src.val] = false) (hw : w[src.val] = false)
    (he : canonicalTransport e dst u = canonicalTransport e dst w) : u = w := by
  rcases (canonicalAt_eq_iff dst _ _).mp he with same | opposite
  · exact pullback_rowEquiv_injective e same
  · have inv : u = ~~~w := pullback_rowEquiv_injective e (by
      simpa only [pullback_not] using opposite)
    have bad := congrArg (fun z : BitVec m => z[src.val]) inv
    simp only [BitVec.getElem_not, hu, hw, Bool.not_false] at bad
    contradiction

lemma canonicalTransport_ops {m n : ℕ} (e : Fin n ≃ Fin m) (ref : Fin n)
    (u w z : BitVec m) (hz : z ∈ basicOps u w) :
    canonicalTransport e ref z ∈
      basicOps (canonicalTransport e ref u) (canonicalTransport e ref w) :=
  canonicalAt_ops ref _ _ _ (pullback_ops e u w z hz)

lemma build_canonicalTransport {m n budget : ℕ}
    {roots : Finset (BitVec m)} {goal : BitVec m}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false)
    (run : build basicOps goal budget roots) :
    build basicOps (canonicalTransport e dst goal) budget
      (roots.image (canonicalTransport e dst)) := by
  exact build_map_on basicOps basicOps (fun w => w[src.val] = false)
    (canonicalTransport e dst) (zeroAt_ops src)
    (canonicalTransport_injective_zero e src dst)
    (fun a b _ _ z hz => canonicalTransport_ops e dst a b z hz) initial run

lemma live_canonicalTransport {m n budget : ℕ}
    {roots : Finset (BitVec m)} {goal : BitVec m}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false)
    (run : live basicOps goal budget roots) :
    live basicOps (canonicalTransport e dst goal) budget
      (roots.image (canonicalTransport e dst)) := by
  exact live_map_on basicOps basicOps (fun w => w[src.val] = false)
    (canonicalTransport e dst) (zeroAt_ops src)
    (canonicalTransport_injective_zero e src dst)
    (fun a b _ _ z hz => canonicalTransport_ops e dst a b z hz) initial run

lemma pullback_rowEquiv_inverse {m n : ℕ} (e : Fin n ≃ Fin m) (w : BitVec m) :
    pullback e.symm (pullback e w) = w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [pullback_bit e.symm (pullback e w) ⟨i, hi⟩,
    pullback_bit e w (e.symm ⟨i, hi⟩)]
  simp only [Equiv.apply_symm_apply]

lemma canonicalTransport_roundtrip {m n : ℕ}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n) (w : BitVec m) :
    canonicalTransport e.symm src (canonicalTransport e dst w) = canonicalAt src w := by
  change canonicalAt src (pullback e.symm (canonicalAt dst (pullback e w))) = _
  by_cases phase : (pullback e w)[dst.val] = true
  · have hc : canonicalAt dst (pullback e w) = ~~~(pullback e w) := by
      simp only [canonicalAt, phase, ite_true]
    rw [hc, pullback_not, pullback_rowEquiv_inverse, canonicalAt_not]
  · have hc : canonicalAt dst (pullback e w) = pullback e w := by
      simp [canonicalAt, phase]
    rw [hc, pullback_rowEquiv_inverse]

lemma canonicalTransport_roots_zero {m n : ℕ}
    (e : Fin n ≃ Fin m) (dst : Fin n) (roots : Finset (BitVec m)) :
    ∀ w ∈ roots.image (canonicalTransport e dst), w[dst.val] = false := by
  intro w hw
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
  exact canonicalAt_bit dst (pullback e u)

lemma canonicalTransport_roots_inverse {m n : ℕ}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n) (roots : Finset (BitVec m))
    (initial : ∀ w ∈ roots, w[src.val] = false) :
    (roots.image (canonicalTransport e dst)).image (canonicalTransport e.symm src) = roots := by
  rw [Finset.image_image]
  have inv : ∀ w ∈ roots,
      canonicalTransport e.symm src (canonicalTransport e dst w) = w := by
    intro w hw
    rw [canonicalTransport_roundtrip, canonicalAt_of_false src w (initial w hw)]
  ext w
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    change canonicalTransport e.symm src (canonicalTransport e dst u) = w at he
    rw [inv u hu] at he
    exact he ▸ hu
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, inv w hw⟩

lemma build_iff_canonicalTransport {m n budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false) (targetZero : goal[src.val] = false) :
    build basicOps goal budget roots ↔
      build basicOps (canonicalTransport e dst goal) budget
        (roots.image (canonicalTransport e dst)) := by
  constructor
  · exact build_canonicalTransport e src dst initial
  · intro run
    have back := build_canonicalTransport e.symm dst src
      (canonicalTransport_roots_zero e dst roots) run
    simpa only [canonicalTransport_roundtrip, canonicalAt_of_false src goal targetZero,
      canonicalTransport_roots_inverse e src dst roots initial] using back

lemma live_iff_canonicalTransport {m n budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false) (targetZero : goal[src.val] = false) :
    live basicOps goal budget roots ↔
      live basicOps (canonicalTransport e dst goal) budget
        (roots.image (canonicalTransport e dst)) := by
  constructor
  · exact live_canonicalTransport e src dst initial
  · intro run
    have back := live_canonicalTransport e.symm dst src
      (canonicalTransport_roots_zero e dst roots) run
    simpa only [canonicalTransport_roundtrip, canonicalAt_of_false src goal targetZero,
      canonicalTransport_roots_inverse e src dst roots initial] using back

lemma build_iff_canonicalAutomorphism {m budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Equiv.Perm (Fin m)) (ref : Fin m)
    (initial : ∀ w ∈ roots, w[ref.val] = false) (targetZero : goal[ref.val] = false)
    (goalFixed : canonicalTransport e ref goal = goal) :
    build basicOps goal budget roots ↔
      build basicOps goal budget (roots.image (canonicalTransport e ref)) := by
  simpa only [goalFixed] using build_iff_canonicalTransport roots goal e ref ref initial targetZero

lemma live_iff_canonicalAutomorphism {m budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Equiv.Perm (Fin m)) (ref : Fin m)
    (initial : ∀ w ∈ roots, w[ref.val] = false) (targetZero : goal[ref.val] = false)
    (goalFixed : canonicalTransport e ref goal = goal) :
    live basicOps goal budget roots ↔
      live basicOps goal budget (roots.image (canonicalTransport e ref)) := by
  simpa only [goalFixed] using live_iff_canonicalTransport roots goal e ref ref initial targetZero

def canonicalPullback {m n : ℕ} (ρ : Fin n → Fin m) (ref : Fin n)
    (w : BitVec m) : BitVec n := canonicalAt ref (pullback ρ w)

lemma canonicalPullback_injective_stable_zero {m n : ℕ}
    {roots : Finset (BitVec m)} (ρ : Fin n → Fin m)
    (cover : ∀ i : Fin m, ∃ j : Fin n, patternEq roots i (ρ j))
    (src : Fin m) (dst : Fin n) (u w : BitVec m)
    (hu : patternStable roots u ∧ u[src.val] = false)
    (hw : patternStable roots w ∧ w[src.val] = false)
    (he : canonicalPullback ρ dst u = canonicalPullback ρ dst w) : u = w := by
  rcases (canonicalAt_eq_iff dst _ _).mp he with same | opposite
  · exact pullback_injective_stable ρ cover u w hu.1 hw.1 same
  · have inv : u = ~~~w := pullback_injective_stable ρ cover u (~~~w)
      hu.1 (patternStable_not hw.1) (by simpa only [pullback_not] using opposite)
    have bad := congrArg (fun z : BitVec m => z[src.val]) inv
    simp only [BitVec.getElem_not, hu.2, hw.2, Bool.not_false] at bad
    contradiction

lemma canonicalPullback_ops {m n : ℕ} (ρ : Fin n → Fin m) (ref : Fin n)
    (u w z : BitVec m) (hz : z ∈ basicOps u w) :
    canonicalPullback ρ ref z ∈
      basicOps (canonicalPullback ρ ref u) (canonicalPullback ρ ref w) :=
  canonicalAt_ops ref _ _ _ (pullback_ops ρ u w z hz)

lemma build_canonicalPullback {m n budget : ℕ}
    {roots : Finset (BitVec m)} {goal : BitVec m}
    (ρ : Fin n → Fin m)
    (cover : ∀ i : Fin m, ∃ j : Fin n, patternEq roots i (ρ j))
    (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false)
    (run : build basicOps goal budget roots) :
    build basicOps (canonicalPullback ρ dst goal) budget
      (roots.image (canonicalPullback ρ dst)) := by
  exact build_map_on basicOps basicOps
    (fun w => patternStable roots w ∧ w[src.val] = false)
    (canonicalPullback ρ dst)
    (fun a b ha hb z hz => ⟨patternStable_ops a b ha.1 hb.1 z hz,
      zeroAt_ops src a b ha.2 hb.2 z hz⟩)
    (canonicalPullback_injective_stable_zero ρ cover src dst)
    (fun a b _ _ z hz => canonicalPullback_ops ρ dst a b z hz)
    (fun w hw => ⟨patternStable_root roots w hw, initial w hw⟩) run

lemma live_canonicalPullback {m n budget : ℕ}
    {roots : Finset (BitVec m)} {goal : BitVec m}
    (ρ : Fin n → Fin m)
    (cover : ∀ i : Fin m, ∃ j : Fin n, patternEq roots i (ρ j))
    (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false)
    (run : live basicOps goal budget roots) :
    live basicOps (canonicalPullback ρ dst goal) budget
      (roots.image (canonicalPullback ρ dst)) := by
  exact live_map_on basicOps basicOps
    (fun w => patternStable roots w ∧ w[src.val] = false)
    (canonicalPullback ρ dst)
    (fun a b ha hb z hz => ⟨patternStable_ops a b ha.1 hb.1 z hz,
      zeroAt_ops src a b ha.2 hb.2 z hz⟩)
    (canonicalPullback_injective_stable_zero ρ cover src dst)
    (fun a b _ _ z hz => canonicalPullback_ops ρ dst a b z hz)
    (fun w hw => ⟨patternStable_root roots w hw, initial w hw⟩) run

def phasedFront {k m : ℕ} (front : Fin k → BitVec m) (signs : Fin k → Bool)
    (q : Fin k) : BitVec m := if signs q then ~~~(front q) else front q

lemma canonicalAt_phase {m : ℕ} (ref : Fin m) (w : BitVec m) (phase : Bool)
    (hz : w[ref.val] = false) : canonicalAt ref (if phase then ~~~w else w) = w := by
  cases phase <;> simp only [Bool.false_eq_true, ite_false, ite_true, canonicalAt_not,
    canonicalAt_of_false ref w hz]

lemma canonicalAt_phasedRoots {k m : ℕ} (front : Fin k → BitVec m)
    (signs : Fin k → Bool) (ref : Fin m)
    (zero : ∀ q : Fin k, (front q)[ref.val] = false) :
    (frontierRoots (phasedFront front signs)).image (canonicalAt ref) = frontierRoots front := by
  unfold frontierRoots
  rw [Finset.image_image]
  congr 1
  funext q
  exact canonicalAt_phase ref (front q) (signs q) (zero q)

lemma phasedPatterns_pullback {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs : Fin k → Bool) (goalFlip : Bool) (dst : Fin n)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (same : labeledPatterns front goal =
      labeledPatterns (phasedFront front' signs) (if goalFlip then ~~~goal' else goal')) :
    ∃ ρ : Fin n → Fin m,
      (∀ i : Fin m, ∃ j : Fin n, patternEq (frontierRoots front) i (ρ j)) ∧
      canonicalPullback ρ dst goal = goal' ∧
      (frontierRoots front).image (canonicalPullback ρ dst) = frontierRoots front' := by
  obtain ⟨ρ, cover, hg, hr⟩ := matching_rows_pullback front goal
    (phasedFront front' signs) (if goalFlip then ~~~goal' else goal')
    (rowsMatch_of_patterns_eq _ _ _ _ same)
    (rowsMatch_of_patterns_eq _ _ _ _ same.symm)
  refine ⟨ρ, cover, ?_, ?_⟩
  · unfold canonicalPullback
    rw [hg]
    exact canonicalAt_phase dst goal' goalFlip targetGoalZero
  · change (frontierRoots front).image (canonicalAt dst ∘ pullback ρ) = frontierRoots front'
    rw [← Finset.image_image, hr, canonicalAt_phasedRoots front' signs dst targetZero]

lemma build_of_phasedPatterns {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs : Fin k → Bool) (goalFlip : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (same : labeledPatterns front goal =
      labeledPatterns (phasedFront front' signs) (if goalFlip then ~~~goal' else goal'))
    (run : build basicOps goal budget (frontierRoots front)) :
    build basicOps goal' budget (frontierRoots front') := by
  obtain ⟨ρ, cover, hg, hr⟩ := phasedPatterns_pullback front goal front' goal'
    signs goalFlip dst targetZero targetGoalZero same
  have initial : ∀ w ∈ frontierRoots front, w[src.val] = false := by
    intro w hw
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
    exact sourceZero q
  simpa only [hg, hr] using build_canonicalPullback ρ cover src dst initial run

lemma live_of_phasedPatterns {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs : Fin k → Bool) (goalFlip : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (same : labeledPatterns front goal =
      labeledPatterns (phasedFront front' signs) (if goalFlip then ~~~goal' else goal'))
    (run : live basicOps goal budget (frontierRoots front)) :
    live basicOps goal' budget (frontierRoots front') := by
  obtain ⟨ρ, cover, hg, hr⟩ := phasedPatterns_pullback front goal front' goal'
    signs goalFlip dst targetZero targetGoalZero same
  have initial : ∀ w ∈ frontierRoots front, w[src.val] = false := by
    intro w hw
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
    exact sourceZero q
  simpa only [hg, hr] using live_canonicalPullback ρ cover src dst initial run

lemma build_of_phasedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs : Fin k → Bool) (goalFlip : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (positive : positivePatterns front goal = positivePatterns (phasedFront front' signs)
      (if goalFlip then ~~~goal' else goal'))
    (negative : negativePatterns front goal = negativePatterns (phasedFront front' signs)
      (if goalFlip then ~~~goal' else goal'))
    (run : build basicOps goal budget (frontierRoots front)) :
    build basicOps goal' budget (frontierRoots front') :=
  build_of_phasedPatterns front goal front' goal' signs goalFlip src dst
    sourceZero targetZero targetGoalZero
    (labeledPatterns_eq_of_keys_eq _ _ _ _ positive negative) run

lemma live_of_phasedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs : Fin k → Bool) (goalFlip : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (positive : positivePatterns front goal = positivePatterns (phasedFront front' signs)
      (if goalFlip then ~~~goal' else goal'))
    (negative : negativePatterns front goal = negativePatterns (phasedFront front' signs)
      (if goalFlip then ~~~goal' else goal'))
    (run : live basicOps goal budget (frontierRoots front)) :
    live basicOps goal' budget (frontierRoots front') :=
  live_of_phasedPatterns front goal front' goal' signs goalFlip src dst
    sourceZero targetZero targetGoalZero
    (labeledPatterns_eq_of_keys_eq _ _ _ _ positive negative) run

end PEqualNP.Outside.L_meta_10760
