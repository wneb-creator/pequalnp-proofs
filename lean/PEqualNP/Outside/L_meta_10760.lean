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


lemma rowsMatch_cancel_phases {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs signs' : Fin k → Bool) (flip flip' : Bool)
    (same : rowsMatch (phasedFront front signs) (if flip then ~~~goal else goal)
      (phasedFront front' signs') (if flip' then ~~~goal' else goal')) :
    rowsMatch front goal (phasedFront front' (fun q => Bool.xor (signs q) (signs' q)))
      (if Bool.xor flip flip' then ~~~goal' else goal') := by
  intro i
  obtain ⟨j, hg, hf⟩ := same i
  refine ⟨j, ?_, ?_⟩
  · cases flip <;> cases flip' <;> simpa using hg
  · intro q
    have h := hf q
    cases hs : signs q <;> cases ht : signs' q <;>
      simpa [phasedFront, hs, ht] using h

lemma labeledPatterns_cancel_phases {k m n : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs signs' : Fin k → Bool) (flip flip' : Bool)
    (same : labeledPatterns (phasedFront front signs) (if flip then ~~~goal else goal) =
      labeledPatterns (phasedFront front' signs') (if flip' then ~~~goal' else goal')) :
    labeledPatterns front goal =
      labeledPatterns (phasedFront front' (fun q => Bool.xor (signs q) (signs' q)))
        (if Bool.xor flip flip' then ~~~goal' else goal') := by
  apply labeledPatterns_eq_of_rowsMatch
  · exact rowsMatch_cancel_phases front goal front' goal' signs signs' flip flip'
      (rowsMatch_of_patterns_eq _ _ _ _ same)
  · intro j
    obtain ⟨i, hg, hf⟩ := (rowsMatch_of_patterns_eq _ _ _ _ same.symm) j
    refine ⟨i, ?_, ?_⟩
    · cases flip <;> cases flip' <;> simpa using hg
    · intro q
      have h := hf q
      cases hs : signs q <;> cases ht : signs' q <;>
        simpa [phasedFront, hs, ht] using h

lemma live_of_commonPhasedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs signs' : Fin k → Bool) (flip flip' : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (positive : positivePatterns (phasedFront front signs) (if flip then ~~~goal else goal) =
      positivePatterns (phasedFront front' signs') (if flip' then ~~~goal' else goal'))
    (negative : negativePatterns (phasedFront front signs) (if flip then ~~~goal else goal) =
      negativePatterns (phasedFront front' signs') (if flip' then ~~~goal' else goal'))
    (run : live basicOps goal budget (frontierRoots front)) :
    live basicOps goal' budget (frontierRoots front') :=
  live_of_phasedPatterns front goal front' goal'
    (fun q => Bool.xor (signs q) (signs' q)) (Bool.xor flip flip') src dst
    sourceZero targetZero targetGoalZero
    (labeledPatterns_cancel_phases front goal front' goal' signs signs' flip flip'
      (labeledPatterns_eq_of_keys_eq _ _ _ _ positive negative)) run


lemma live_iff_commonPhasedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (signs signs' : Fin k → Bool) (flip flip' : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (sourceGoalZero : goal[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (positive : positivePatterns (phasedFront front signs) (if flip then ~~~goal else goal) =
      positivePatterns (phasedFront front' signs') (if flip' then ~~~goal' else goal'))
    (negative : negativePatterns (phasedFront front signs) (if flip then ~~~goal else goal) =
      negativePatterns (phasedFront front' signs') (if flip' then ~~~goal' else goal')) :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') :=
  ⟨live_of_commonPhasedKeys front goal front' goal' signs signs' flip flip' src dst
      sourceZero targetZero targetGoalZero positive negative,
    live_of_commonPhasedKeys front' goal' front goal signs' signs flip' flip dst src
      targetZero sourceZero sourceGoalZero positive.symm negative.symm⟩

lemma live_iff_commonPermutedKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (perm perm' : Fin k ≃ Fin k) (signs signs' : Fin k → Bool)
    (flip flip' : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (sourceGoalZero : goal[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (positive : positivePatterns (phasedFront (front ∘ perm) signs)
        (if flip then ~~~goal else goal) =
      positivePatterns (phasedFront (front' ∘ perm') signs')
        (if flip' then ~~~goal' else goal'))
    (negative : negativePatterns (phasedFront (front ∘ perm) signs)
        (if flip then ~~~goal else goal) =
      negativePatterns (phasedFront (front' ∘ perm') signs')
        (if flip' then ~~~goal' else goal')) :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') := by
  simpa only [frontierRoots_reindex] using
    live_iff_commonPhasedKeys (front ∘ perm) goal (front' ∘ perm') goal'
      signs signs' flip flip' src dst
      (fun q => sourceZero (perm q)) sourceGoalZero
      (fun q => targetZero (perm' q)) targetGoalZero positive negative

def transformPattern {k : ℕ} (perm : Fin k ≃ Fin k) (signs : Fin k → Bool)
    (p : BitVec k) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn (fun q : Fin k =>
    if signs q then !(p[(perm q).val]) else p[(perm q).val]))).cast (by simp)

lemma transformPattern_bit {k : ℕ} (perm : Fin k ≃ Fin k) (signs : Fin k → Bool)
    (p : BitVec k) (q : Fin k) :
    (transformPattern perm signs p)[q.val] =
      if signs q then !(p[(perm q).val]) else p[(perm q).val] := by
  simp [transformPattern, ← BitVec.getLsbD_eq_getElem]

lemma rowPattern_transform {k m : ℕ} (front : Fin k → BitVec m)
    (perm : Fin k ≃ Fin k) (signs : Fin k → Bool) (i : Fin m) :
    rowPattern (phasedFront (front ∘ perm) signs) i =
      transformPattern perm signs (rowPattern front i) := by
  apply BitVec.eq_of_getElem_eq
  intro q hq
  rw [rowPattern_bit _ i ⟨q, hq⟩, transformPattern_bit perm signs _ ⟨q, hq⟩]
  cases hs : signs ⟨q, hq⟩ <;>
    simp [phasedFront, hs, Function.comp_apply, rowPattern_bit]

lemma patternKey_transform {k m : ℕ} (front : Fin k → BitVec m)
    (perm : Fin k ≃ Fin k) (signs : Fin k → Bool) (goal : BitVec m)
    (value : Bool) :
    patternKey (phasedFront (front ∘ perm) signs) goal value =
      (patternKey front goal value).image (transformPattern perm signs) := by
  unfold patternKey
  rw [Finset.image_image]
  congr 1
  funext i
  exact rowPattern_transform front perm signs i

lemma patternKey_transform_flip {k m : ℕ} (front : Fin k → BitVec m)
    (perm : Fin k ≃ Fin k) (signs : Fin k → Bool) (goal : BitVec m)
    (goalFlip value : Bool) :
    patternKey (phasedFront (front ∘ perm) signs)
        (if goalFlip then ~~~goal else goal) value =
      (patternKey front goal (if goalFlip then !value else value)).image
        (transformPattern perm signs) := by
  cases goalFlip <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, patternKey_not, patternKey_transform]

lemma positivePatterns_transform {k m : ℕ} (front : Fin k → BitVec m)
    (perm : Fin k ≃ Fin k) (signs : Fin k → Bool) (goal : BitVec m)
    (goalFlip : Bool) :
    positivePatterns (phasedFront (front ∘ perm) signs)
        (if goalFlip then ~~~goal else goal) =
      (if goalFlip then negativePatterns front goal else positivePatterns front goal).image
        (transformPattern perm signs) := by
  cases goalFlip <;>
    simp only [positivePatterns, negativePatterns, Bool.false_eq_true, ite_false, ite_true,
      patternKey_not, Bool.not_true, patternKey_transform]

lemma negativePatterns_transform {k m : ℕ} (front : Fin k → BitVec m)
    (perm : Fin k ≃ Fin k) (signs : Fin k → Bool) (goal : BitVec m)
    (goalFlip : Bool) :
    negativePatterns (phasedFront (front ∘ perm) signs)
        (if goalFlip then ~~~goal else goal) =
      (if goalFlip then positivePatterns front goal else negativePatterns front goal).image
        (transformPattern perm signs) := by
  cases goalFlip <;>
    simp only [positivePatterns, negativePatterns, Bool.false_eq_true, ite_false, ite_true,
      patternKey_not, Bool.not_false, patternKey_transform]

lemma live_iff_transformedPatternKeys {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (perm perm' : Fin k ≃ Fin k) (signs signs' : Fin k → Bool)
    (flip flip' : Bool) (src : Fin m) (dst : Fin n)
    (sourceZero : ∀ q : Fin k, (front q)[src.val] = false)
    (sourceGoalZero : goal[src.val] = false)
    (targetZero : ∀ q : Fin k, (front' q)[dst.val] = false)
    (targetGoalZero : goal'[dst.val] = false)
    (positive :
      (if flip then negativePatterns front goal else positivePatterns front goal).image
        (transformPattern perm signs) =
      (if flip' then negativePatterns front' goal' else positivePatterns front' goal').image
        (transformPattern perm' signs'))
    (negative :
      (if flip then positivePatterns front goal else negativePatterns front goal).image
        (transformPattern perm signs) =
      (if flip' then positivePatterns front' goal' else negativePatterns front' goal').image
        (transformPattern perm' signs')) :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') := by
  apply live_iff_commonPermutedKeys front goal front' goal' perm perm' signs signs'
    flip flip' src dst sourceZero sourceGoalZero targetZero targetGoalZero
  · simpa only [positivePatterns_transform] using positive
  · simpa only [negativePatterns_transform] using negative

def canonical64 (w : BitVec 64) : BitVec 64 :=
  if w.toNat ≤ (~~~w).toNat then w else ~~~w

def sampleInputs64 : List (BitVec 64) := [0x844a844a8952aaa, 0x1089308931264ccc, 0x2111c111c23870f0, 0x421e021e03c07f00, 0x83e003e003ff8000, 0xfc0003fffc000000, 0xfffffc0000000000]

def sampleGoal64 : BitVec 64 := 0xffdfebdfbbbf6ca0

def signedRoots64 : Finset (BitVec 64) := (sampleInputs64.map canonical64).toFinset

namespace S64

def firstRoot (i : Fin 7) : BitVec 64 :=
  min (sampleInputs64.getD i.val 0) (~~~(sampleInputs64.getD i.val 0))

def firstOp (i j : Fin 7) (o : Fin 4) : BitVec 64 :=
  (ops (firstRoot i) (firstRoot j)).getD o.val 0

def symRowData : List Nat := [0, 26, 15, 37, 8, 33, 22, 41, 4, 30, 19, 40, 12, 36, 25, 2, 28, 17, 39, 10, 35, 24, 6, 32, 21, 14, 1, 27, 16, 38, 9, 34, 23, 5, 31, 20, 13, 3, 29, 18, 11, 7, 42, 58, 53, 63, 49, 62, 57, 46, 61, 56, 52, 44, 60, 55, 51, 48, 43, 59, 54, 50, 47, 45]

def symRow (i : Fin 64) : Fin 64 :=
  ⟨symRowData.getD i.val 0 % 64, Nat.mod_lt _ (by decide)⟩

lemma symRow_involutive : Function.Involutive symRow := by
  change ∀ i : Fin 64, symRow (symRow i) = i
  decide +kernel

def symEquiv : Equiv.Perm (Fin 64) :=
  ⟨symRow, symRow, symRow_involutive, symRow_involutive⟩

abbrev symWord (w : BitVec 64) : BitVec 64 :=
  canonicalTransport symEquiv ⟨63, by decide⟩ w

def caseData : List (Fin 7 × Fin 7 × Fin 4) := [(1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 0, 3), (2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 0, 3), (2, 1, 0), (2, 1, 1), (2, 1, 2), (2, 1, 3), (3, 0, 0), (3, 0, 1), (3, 0, 2), (3, 0, 3), (3, 1, 0), (3, 1, 1), (3, 1, 2), (3, 1, 3), (3, 2, 0), (3, 2, 1), (3, 2, 2), (3, 2, 3), (4, 0, 0), (4, 0, 1), (4, 0, 2), (4, 0, 3), (4, 1, 0), (4, 1, 1), (4, 1, 2), (4, 1, 3), (4, 2, 0), (4, 2, 1), (4, 2, 2), (4, 2, 3), (4, 3, 0), (4, 3, 1), (4, 3, 2), (4, 3, 3), (5, 0, 0), (5, 0, 1), (5, 0, 2), (5, 0, 3), (5, 1, 0), (5, 1, 1), (5, 1, 2), (5, 1, 3), (5, 2, 0), (5, 2, 1), (5, 2, 2), (5, 2, 3), (5, 3, 0), (5, 3, 1), (5, 3, 2), (5, 3, 3), (5, 4, 0), (5, 4, 1), (5, 4, 2), (5, 4, 3), (6, 0, 0), (6, 0, 1), (6, 0, 2), (6, 0, 3), (6, 1, 0), (6, 1, 1), (6, 1, 2), (6, 1, 3), (6, 2, 0), (6, 2, 1), (6, 2, 2), (6, 2, 3), (6, 3, 0), (6, 3, 1), (6, 3, 2), (6, 3, 3), (6, 4, 0), (6, 4, 1), (6, 4, 2), (6, 4, 3), (6, 5, 0), (6, 5, 1), (6, 5, 2), (6, 5, 3)]

def caseWord (c : Fin 84) : BitVec 64 :=
  let t := caseData.getD c.val (0, 0, 0)
  firstOp t.1 t.2.1 t.2.2

def symCaseData : List Nat := [57, 56, 58, 59, 55, 54, 52, 53, 39, 38, 36, 37, 51, 50, 48, 49, 35, 34, 32, 33, 20, 21, 23, 22, 45, 44, 46, 47, 29, 28, 30, 31, 18, 19, 17, 16, 10, 11, 9, 8, 41, 40, 42, 43, 25, 24, 26, 27, 14, 15, 13, 12, 6, 7, 5, 4, 1, 0, 2, 3, 82, 83, 80, 81, 78, 79, 76, 77, 72, 73, 74, 75, 68, 69, 70, 71, 66, 67, 64, 65, 62, 63, 60, 61]

def symCase (c : Fin 84) : Fin 84 :=
  ⟨symCaseData.getD c.val 0 % 84, Nat.mod_lt _ (by decide)⟩

def representativeData : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 40, 42, 43, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]

def representative (r : Fin 45) : Fin 84 :=
  ⟨representativeData.getD r.val 0 % 84, Nat.mod_lt _ (by decide)⟩

def caseIndex (i j : Fin 7) (o : Fin 4) : Fin 84 :=
  ⟨(2 * i.val * (i.val - 1) + 4 * j.val + o.val) % 84, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 8000000 in
lemma caseIndex_correct : ∀ i j : Fin 7, ∀ o : Fin 4, j < i →
    caseWord (caseIndex i j o) = firstOp i j o := by decide +kernel

lemma symGoal_fixed : symWord (~~~sampleGoal64) = ~~~sampleGoal64 := by decide +kernel

lemma symRoots_fixed : signedRoots64.image symWord = signedRoots64 := by decide +kernel

set_option maxHeartbeats 8000000 in
lemma symCases_correct : ∀ c : Fin 84, symWord (caseWord c) = caseWord (symCase c) := by
  decide +kernel

lemma symCase_involutive : Function.Involutive symCase := by
  change ∀ c : Fin 84, symCase (symCase c) = c
  decide +kernel

lemma representatives_cover : ∀ c : Fin 84, ∃ r : Fin 45,
    c = representative r ∨ symCase c = representative r := by decide +kernel

lemma symRoots_zero : ∀ w ∈ signedRoots64, w[63] = false := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  simp only [sampleInputs64, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma caseWords_zero : ∀ c : Fin 84, (caseWord c)[63] = false := by decide +kernel

lemma live_case_symmetry (c : Fin 84) (budget : ℕ) :
    live basicOps (~~~sampleGoal64) budget (insert (caseWord c) signedRoots64) ↔
      live basicOps (~~~sampleGoal64) budget (insert (caseWord (symCase c)) signedRoots64) := by
  have initial : ∀ w ∈ insert (caseWord c) signedRoots64, w[63] = false := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact caseWords_zero c
    · exact symRoots_zero w hw
  have h := live_iff_canonicalAutomorphism (budget := budget) (insert (caseWord c) signedRoots64)
    (~~~sampleGoal64) symEquiv ⟨63, by decide⟩ initial (by decide +kernel) symGoal_fixed
  change live basicOps (~~~sampleGoal64) budget (insert (caseWord c) signedRoots64) ↔
    live basicOps (~~~sampleGoal64) budget
      ((insert (caseWord c) signedRoots64).image symWord) at h
  simpa only [Finset.image_insert, symCases_correct, symRoots_fixed] using h

lemma reject84_of_reject45 (budget : ℕ)
    (reject : ∀ r : Fin 45, ¬ live basicOps (~~~sampleGoal64) budget
      (insert (caseWord (representative r)) signedRoots64)) :
    ∀ c : Fin 84, ¬ live basicOps (~~~sampleGoal64) budget
      (insert (caseWord c) signedRoots64) := by
  intro c run
  obtain ⟨r, same | mapped⟩ := representatives_cover c
  · exact reject r (same ▸ run)
  · exact reject r (mapped ▸ (live_case_symmetry c budget).mp run)

lemma rejection_from_45_64 (budget : ℕ)
    (reject : ∀ r : Fin 45, ¬ live basicOps (~~~sampleGoal64) budget
      (insert (caseWord (representative r)) signedRoots64)) :
    ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps (~~~sampleGoal64) budget (insert (firstOp i j o) signedRoots64) := by
  intro i j hji o
  have h := reject84_of_reject45 budget reject (caseIndex i j o)
  rwa [caseIndex_correct i j o hji] at h

end S64

def swapColor (a b c : ℕ) : ℕ := if c = a then b else if c = b then a else c

lemma swapColor_involutive (a b : ℕ) : Function.Involutive (swapColor a b) := by
  intro c
  by_cases hab : a = b
  · subst b
    by_cases hca : c = a
    · subst c
      simp [swapColor]
    · simp [swapColor, hca]
  · by_cases hca : c = a
    · subst c
      simp [swapColor, Ne.symm hab]
    · by_cases hcb : c = b
      · subst c
        simp [swapColor, Ne.symm hab]
      · simp [swapColor, hca, hcb]

lemma swapColor_injective (a b : ℕ) : Function.Injective (swapColor a b) := by
  intro c d h
  have he := congrArg (swapColor a b) h
  simpa only [swapColor_involutive a b c, swapColor_involutive a b d] using he

lemma swapColor_lt {a b c colors : ℕ}
    (ha : a < colors) (hb : b < colors) (hc : c < colors) :
    swapColor a b c < colors := by
  unfold swapColor
  split_ifs <;> assumption

lemma swapColor_fix_below {a used c : ℕ} (ha : used ≤ a) (hc : c < used) :
    swapColor a used c = c := by
  have hca : c ≠ a := by omega
  have hcu : c ≠ used := by omega
  simp only [swapColor, hca, hcu, ite_false]

lemma color_first_unused {α : Type} (D : α → Prop) (E : α → α → Prop)
    (f : α → ℕ) (used colors : ℕ) (v : α) (hv : D v)
    (bound : ∀ x, D x → f x < colors)
    (proper : ∀ x y, D x → D y → E x y → f x ≠ f y)
    (fresh : used ≤ f v) :
    ∃ g : α → ℕ,
      (∀ x, D x → g x < colors) ∧
      (∀ x y, D x → D y → E x y → g x ≠ g y) ∧
      (∀ x, f x < used → g x = f x) ∧ g v = used := by
  have hfv : f v < colors := bound v hv
  have hu : used < colors := by omega
  refine ⟨fun x => swapColor (f v) used (f x), ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact swapColor_lt hfv hu (bound x hx)
  · intro x y hx hy hedge he
    exact proper x y hx hy hedge (swapColor_injective (f v) used he)
  · intro x hx
    exact swapColor_fix_below fresh hx
  · simp only [swapColor, ite_true]

def uniqueSep {width : Nat} (S : Finset (BitVec width)) (a : BitVec width)
    (p q : Fin width) : Prop :=
  a[p.val] ≠ a[q.val] ∧ ∀ w ∈ S, w ≠ a → w[p.val] = w[q.val]

def criticalPair {width : Nat} (target : BitVec width) (S : Finset (BitVec width))
    (a b : BitVec width) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∃ p q ra rb sa sb : Fin width,
    target[p.val] = true ∧ target[q.val] = false ∧
    target[ra.val] = false ∧ target[rb.val] = false ∧
    target[sa.val] = true ∧ target[sb.val] = true ∧
    uniqueSep S a p ra ∧ uniqueSep S b p rb ∧
    uniqueSep S a sa q ∧ uniqueSep S b sb q ∧
    a[p.val] = a[sa.val] ∧ b[p.val] = b[sb.val]

def uniqueSepCheck {width : Nat} (ws : List (BitVec width)) (a : BitVec width)
    (p q : Fin width) : Bool :=
  (a[p.val] != a[q.val]) && ws.all (fun w => w == a || w[p.val] == w[q.val])

lemma uniqueSepCheck_sound {width : Nat} {ws : List (BitVec width)} {a : BitVec width}
    {p q : Fin width} (h : uniqueSepCheck ws a p q = true) :
    uniqueSep ws.toFinset a p q := by
  simp only [uniqueSepCheck, Bool.and_eq_true, bne_iff_ne, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  intro w hw hne
  exact (h.2 w (List.mem_toFinset.mp hw)).resolve_left hne

def criticalWitnessCheck {width : Nat} (target : BitVec width)
    (ws : List (BitVec width)) (a b : BitVec width) (p q ra rb sa sb : Fin width) : Bool :=
  decide (a ∈ ws) && decide (b ∈ ws) && (a != b) &&
  target[p.val] && !target[q.val] && !target[ra.val] && !target[rb.val] &&
  target[sa.val] && target[sb.val] &&
  uniqueSepCheck ws a p ra && uniqueSepCheck ws b p rb &&
  uniqueSepCheck ws a sa q && uniqueSepCheck ws b sb q &&
  (a[p.val] == a[sa.val]) && (b[p.val] == b[sb.val])

lemma criticalWitnessCheck_sound {width : Nat} {target : BitVec width}
    {ws : List (BitVec width)} {a b : BitVec width} {p q ra rb sa sb : Fin width}
    (h : criticalWitnessCheck target ws a b p q ra rb sa sb = true) :
    criticalPair target ws.toFinset a b := by
  simp only [criticalWitnessCheck, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    Bool.not_eq_true', beq_iff_eq, and_assoc] at h
  obtain ⟨ha, hb, hab, hp, hq, hra, hrb, hsa, hsb, u₁, u₂, u₃, u₄, pa, pb⟩ := h
  exact ⟨List.mem_toFinset.mpr ha, List.mem_toFinset.mpr hb, hab,
    p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    uniqueSepCheck_sound u₁, uniqueSepCheck_sound u₂,
    uniqueSepCheck_sound u₃, uniqueSepCheck_sound u₄, pa, pb⟩

lemma patternKey_map {k l m : ℕ} (front : Fin k → BitVec m)
    (front' : Fin l → BitVec m) (goal : BitVec m) (value : Bool)
    (step : BitVec k → BitVec l)
    (rows : ∀ i : Fin m, rowPattern front' i = step (rowPattern front i)) :
    patternKey front' goal value = (patternKey front goal value).image step := by
  unfold patternKey
  rw [Finset.image_image]
  congr 1
  funext i
  exact rows i

def transitionOp {width : ℕ} (o : Fin 4) (a b : BitVec width) : BitVec width :=
  (ops a b).getD o.val 0

def transitionBit (o : Fin 4) (a b : Bool) : Bool :=
  ([a && b, a || b, a && !b, b && !a] : List Bool).getD o.val false

lemma transitionOp_bit {width : ℕ} (o : Fin 4) (a b : BitVec width) (i : Fin width) :
    (transitionOp o a b)[i.val] = transitionBit o a[i.val] b[i.val] := by
  fin_cases o <;> simp [transitionOp, transitionBit, ops]

def stepFront {k l m : ℕ} (front : Fin k → BitVec m) (a b : Fin k) (o : Fin 4)
    (select : Fin l → Option (Fin k)) (q : Fin l) : BitVec m :=
  match select q with
  | some t => front t
  | none => transitionOp o (front a) (front b)

def stepPattern {k l : ℕ} (a b : Fin k) (o : Fin 4)
    (select : Fin l → Option (Fin k)) (p : BitVec k) : BitVec l :=
  (BitVec.ofBoolListLE (List.ofFn (fun q : Fin l =>
    match select q with
    | some t => p[t.val]
    | none => transitionBit o p[a.val] p[b.val]))).cast (by simp)

lemma stepPattern_bit {k l : ℕ} (a b : Fin k) (o : Fin 4)
    (select : Fin l → Option (Fin k)) (p : BitVec k) (q : Fin l) :
    (stepPattern a b o select p)[q.val] =
      match select q with
      | some t => p[t.val]
      | none => transitionBit o p[a.val] p[b.val] := by
  simp [stepPattern, ← BitVec.getLsbD_eq_getElem]

lemma rowPattern_stepFront {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k)) (i : Fin m) :
    rowPattern (stepFront front a b o select) i =
      stepPattern a b o select (rowPattern front i) := by
  apply BitVec.eq_of_getElem_eq
  intro q hq
  rw [rowPattern_bit _ i ⟨q, hq⟩, stepPattern_bit a b o select _ ⟨q, hq⟩]
  cases hs : select ⟨q, hq⟩ <;>
    simp only [stepFront, hs, transitionOp_bit, rowPattern_bit]

lemma patternKey_stepFront {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k))
    (goal : BitVec m) (value : Bool) :
    patternKey (stepFront front a b o select) goal value =
      (patternKey front goal value).image (stepPattern a b o select) :=
  patternKey_map front (stepFront front a b o select) goal value
    (stepPattern a b o select) (rowPattern_stepFront front a b o select)

lemma positivePatterns_stepFront {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k)) (goal : BitVec m) :
    positivePatterns (stepFront front a b o select) goal =
      (positivePatterns front goal).image (stepPattern a b o select) :=
  patternKey_stepFront front a b o select goal true

lemma negativePatterns_stepFront {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k)) (goal : BitVec m) :
    negativePatterns (stepFront front a b o select) goal =
      (negativePatterns front goal).image (stepPattern a b o select) :=
  patternKey_stepFront front a b o select goal false

lemma transitionOp_zeroAt {width : ℕ} (o : Fin 4) (a b : BitVec width) (ref : Fin width)
    (ha : a[ref.val] = false) (hb : b[ref.val] = false) :
    (transitionOp o a b)[ref.val] = false := by
  rw [transitionOp_bit, ha, hb]
  fin_cases o <;> rfl

lemma stepFront_zeroAt {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k)) (ref : Fin m)
    (zero : ∀ t : Fin k, (front t)[ref.val] = false) :
    ∀ q : Fin l, (stepFront front a b o select q)[ref.val] = false := by
  intro q
  cases hs : select q with
  | none => simpa only [stepFront, hs] using
      transitionOp_zeroAt o (front a) (front b) ref (zero a) (zero b)
  | some t => simpa only [stepFront, hs] using zero t

def bitmapOfPatterns {k : ℕ} (key : Finset (BitVec k)) : BitVec (2 ^ k) :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin (2 ^ k) =>
    decide (BitVec.ofNat k i.val ∈ key)))).cast (by simp)

lemma bitmapOfPatterns_bit {k : ℕ} (key : Finset (BitVec k)) (p : BitVec k) :
    (bitmapOfPatterns key).getLsbD p.toNat = true ↔ p ∈ key := by
  simp [bitmapOfPatterns, -BitVec.getLsbD_eq_getElem, p.isLt]

lemma bitmapOfPatterns_eq_iff {k : ℕ} (key key' : Finset (BitVec k)) :
    bitmapOfPatterns key = bitmapOfPatterns key' ↔ key = key' := by
  constructor
  · intro h
    apply Finset.ext
    intro p
    rw [← bitmapOfPatterns_bit, ← bitmapOfPatterns_bit, h]
  · rintro rfl
    rfl

def patternBitmap {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) : BitVec (2 ^ k) :=
  bitmapOfPatterns (patternKey front goal value)

lemma patternBitmap_bit {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) (p : BitVec k) :
    (patternBitmap front goal value).getLsbD p.toNat = true ↔
      p ∈ patternKey front goal value :=
  bitmapOfPatterns_bit _ _

lemma patternBitmap_getElem {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) (p : BitVec k) :
    (patternBitmap front goal value)[p.toNat]'p.isLt = true ↔
      p ∈ patternKey front goal value := by
  rw [← BitVec.getLsbD_eq_getElem]
  exact patternBitmap_bit _ _ _ _

lemma patternBitmap_testBit {k m : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (value : Bool) (p : BitVec k) :
    (patternBitmap front goal value).toNat.testBit p.toNat = true ↔
      p ∈ patternKey front goal value := by
  rw [← BitVec.getElem_eq_testBit_toNat _ _ p.isLt]
  exact patternBitmap_getElem _ _ _ _

lemma patternBitmap_eq_iff {k m n : ℕ} (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n) (value value' : Bool) :
    patternBitmap front goal value = patternBitmap front' goal' value' ↔
      patternKey front goal value = patternKey front' goal' value' :=
  bitmapOfPatterns_eq_iff _ _

lemma bitmapOfPatterns_image_bit {k l : ℕ} (key : Finset (BitVec k))
    (step : BitVec k → BitVec l) (p : BitVec l) :
    (bitmapOfPatterns (key.image step)).getLsbD p.toNat = true ↔
      ∃ q ∈ key, step q = p := by
  rw [bitmapOfPatterns_bit, Finset.mem_image]

lemma patternBitmap_stepFront {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k))
    (goal : BitVec m) (value : Bool) :
    patternBitmap (stepFront front a b o select) goal value =
      bitmapOfPatterns ((patternKey front goal value).image (stepPattern a b o select)) := by
  unfold patternBitmap
  rw [patternKey_stepFront]

lemma patternBitmap_stepFront_bit {k l m : ℕ} (front : Fin k → BitVec m)
    (a b : Fin k) (o : Fin 4) (select : Fin l → Option (Fin k))
    (goal : BitVec m) (value : Bool) (p : BitVec l) :
    (patternBitmap (stepFront front a b o select) goal value).getLsbD p.toNat = true ↔
      ∃ q ∈ patternKey front goal value, stepPattern a b o select q = p := by
  rw [patternBitmap_stepFront, bitmapOfPatterns_image_bit]

lemma live_iff_patternBitmaps {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : patternBitmap front goal true = patternBitmap front' goal' true)
    (negative : patternBitmap front goal false = patternBitmap front' goal' false) :
    live basicOps goal budget (frontierRoots front) ↔
      live basicOps goal' budget (frontierRoots front') :=
  live_iff_patternKeys front goal front' goal'
    ((patternBitmap_eq_iff _ _ _ _ true true).mp positive)
    ((patternBitmap_eq_iff _ _ _ _ false false).mp negative)

lemma build_iff_patternBitmaps {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : patternBitmap front goal true = patternBitmap front' goal' true)
    (negative : patternBitmap front goal false = patternBitmap front' goal' false) :
    build basicOps goal budget (frontierRoots front) ↔
      build basicOps goal' budget (frontierRoots front') :=
  build_iff_patternKeys front goal front' goal'
    ((patternBitmap_eq_iff _ _ _ _ true true).mp positive)
    ((patternBitmap_eq_iff _ _ _ _ false false).mp negative)

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

def sortedLabelKey (a b : ℕ) : ℕ × ℕ := (min a b, max a b)

lemma sortedLabelKey_eq_iff (a b c d : ℕ) :
    sortedLabelKey a b = sortedLabelKey c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have hmin := congrArg Prod.fst h
    have hmax := congrArg Prod.snd h
    simp only [sortedLabelKey] at hmin hmax
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp [sortedLabelKey, min_comm, max_comm]

lemma sortedLabelKey_injective_tagged (f : ℕ → Bool) (a b c d : ℕ)
    (ha : f a = true) (_hb : f b = false) (_hc : f c = true) (hd : f d = false)
    (h : sortedLabelKey a b = sortedLabelKey c d) : a = c ∧ b = d := by
  rcases (sortedLabelKey_eq_iff _ _ _ _).mp h with same | swapped
  · exact same
  · have hf := congrArg f swapped.1
    simp only [ha, hd, Bool.true_eq_false] at hf

lemma live_signed_iff_swappedBitmaps {k m n budget : ℕ}
    (front : Fin k → BitVec m) (goal : BitVec m)
    (front' : Fin k → BitVec n) (goal' : BitVec n)
    (positive : patternBitmap front goal true = patternBitmap front' goal' false)
    (negative : patternBitmap front goal false = patternBitmap front' goal' true) :
    (live basicOps goal budget (frontierRoots front) ∨
      live basicOps (~~~goal) budget (frontierRoots front)) ↔
    (live basicOps goal' budget (frontierRoots front') ∨
      live basicOps (~~~goal') budget (frontierRoots front')) :=
  live_signed_iff_swappedKeys front goal front' goal'
    ((patternBitmap_eq_iff _ _ _ _ true false).mp positive)
    ((patternBitmap_eq_iff _ _ _ _ false true).mp negative)

lemma live_mono_budget {α : Type} [DecidableEq α] (ops : α → α → Finset α)
    (goal : α) {j k : ℕ} {s : Finset α} (le : j ≤ k) (run : live ops goal j s) :
    live ops goal k s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction d with
  | zero => simpa using run
  | succ d ih => exact Or.inl ih

lemma not_live_of_larger_failure {α : Type} [DecidableEq α] (ops : α → α → Finset α)
    (goal : α) {j k : ℕ} {s : Finset α} (le : j ≤ k) (fail : ¬live ops goal k s) :
    ¬live ops goal j s :=
  fun run => fail (live_mono_budget ops goal le run)

end PEqualNP.Outside.L_meta_10760
