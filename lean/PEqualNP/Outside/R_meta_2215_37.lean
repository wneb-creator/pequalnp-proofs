import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2215_37
(geometry :
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  ∀ s : Finset (Fin 13), s.card = 4 →
    let t : Finset (Fin 13) := Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p + l ∉ D
    t.card ≤ 3)
(search :
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 25) =>
    if i.val < 12 then decide (Fin.ofNat 13 (i.val + 1) ∈ s)
    else decide (Fin.ofNat 13 (i.val - 12) ∈ t)
  let off := fun (s : Finset (Fin 13)) =>
    Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p + l ∉ D
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ),
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 61 ∧
    C.output < 25 + C.size ∧ q < 25 + C.size ∧
    let read := fun s t => C.eval (List.ofFn (vec s t))
    let aux := fun s t => (C.wires (List.ofFn (vec s t))).getD q false
    (∀ p l : Fin 13, p + l ∈ D →
      (p ≠ 0 → read {p} {l} = true) ∧ (p = 0 → aux ∅ {l} = true)) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 →
      read s (off s) = false ∧ read (off s) s = false ∧
      aux s (off s \ D) = false ∧ aux (off s) (s \ D) = false)
 :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 25) =>
    if i.val < 12 then decide (Fin.ofNat 13 (i.val + 1) ∈ s)
    else decide (Fin.ofNat 13 (i.val - 12) ∈ t)
  let off := fun (s : Finset (Fin 13)) =>
    Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p + l ∉ D
  obtain ⟨C, q, hm, size, ho, hq, tests⟩ := search
  let read := fun s t => C.eval (List.ofFn (vec s t))
  let aux := fun s t => (C.wires (List.ofFn (vec s t))).getD q false
  change (∀ p l : Fin 13, p + l ∈ D →
      (p ≠ 0 → read {p} {l} = true) ∧ (p = 0 → aux ∅ {l} = true)) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 →
      read s (off s) = false ∧ read (off s) s = false ∧
      aux s (off s \ D) = false ∧ aux (off s) (s \ D) = false) at tests
  have rectangles (s t : Finset (Fin 13))
      (miss : ∀ p ∈ s, ∀ l ∈ t, p + l ∉ D) : s.card ≤ 3 ∨ t.card ≤ 3 := by
    by_cases hs : s.card ≤ 3
    · exact Or.inl hs
    · right
      obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ s.card)
      apply le_trans (Finset.card_le_card ?_) (geometry u hcard)
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => miss p (hu hp) l hl⟩
  have monoWire (x y : Fin 25 → Bool)
      (hxy : ∀ j, x j = true → y j = true) (i : ℕ) :
      (C.wires (List.ofFn x)).getD i false = true →
        (C.wires (List.ofFn y)).getD i false = true := by
    let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    let Le := fun (w z : List Bool) =>
      ∀ j : ℕ, w.getD j false = true → z.getD j false = true
    have extend (gs : List PEqualNP.CircuitLowerBounds.Gate)
        (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w z : List Bool)
        (len : w.length = z.length) (le : Le w z) :
        Le (gs.foldl step w) (gs.foldl step z) := by
      induction gs generalizing w z with
      | nil => exact le
      | cons g gs ih =>
        apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g)
          (by simp [step, len])
        have gate : g.op.eval (g.inputs.map fun j => w.getD j false) = true →
            g.op.eval (g.inputs.map fun j => z.getD j false) = true := by
          rcases ok g (by simp) with hop | hop
          · rw [hop]
            change (g.inputs.map fun j => w.getD j false).all id = true →
              (g.inputs.map fun j => z.getD j false).all id = true
            simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
            intro h j hj
            exact le j (h j hj)
          · rw [hop]
            change (g.inputs.map fun j => w.getD j false).any id = true →
              (g.inputs.map fun j => z.getD j false).any id = true
            simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
            rintro ⟨j, hj, ha⟩
            exact ⟨j, hj, le j ha⟩
        intro j
        by_cases small : j < w.length
        · simpa only [step, List.getD_append _ _ _ _ small,
            List.getD_append _ _ _ _ (len ▸ small)] using le j
        · have big : w.length ≤ j := by omega
          simp only [step, List.getD_append_right _ _ _ _ big,
            List.getD_append_right _ _ _ _ (len ▸ big), ← len]
          cases e : j - w.length with
          | zero => exact gate
          | succ k => simp
    have init : Le (List.ofFn x) (List.ofFn y) := by
      intro j
      by_cases hj : j < 25
      · rw [List.getD_eq_getElem (List.ofFn x) false
              (by simpa only [List.length_ofFn] using hj),
            List.getD_eq_getElem (List.ofFn y) false
              (by simpa only [List.length_ofFn] using hj)]
        simp only [List.getElem_ofFn]
        exact hxy ⟨j, hj⟩
      · rw [List.getD_eq_default (List.ofFn x) false
              (by simp only [List.length_ofFn]; omega)]
        intro h
        exact Bool.noConfusion h
    exact extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp) init i
  have mono {s t u v : Finset (Fin 13)} (hs : s ⊆ u) (ht : t ⊆ v) (j : ℕ) :
      (C.wires (List.ofFn (vec s t))).getD j false = true →
        (C.wires (List.ofFn (vec u v))).getD j false = true := by
    apply monoWire
    intro i
    by_cases hi : i.val < 12
    · simpa only [vec, ite_eq_left hi, decide_eq_true_eq] using
        (hs (x := Fin.ofNat 13 (i.val + 1)))
    · simpa only [vec, ite_eq_right hi, decide_eq_true_eq] using
        (ht (x := Fin.ofNat 13 (i.val - 12)))
  let pt (p : Fin 13) : Fin 25 := ⟨p.val - 1, by omega⟩
  let ln (l : Fin 13) : Fin 25 := ⟨12 + l.val, by omega⟩
  have pointInv (i : Fin 25) (hi : i.val < 12) :
      pt (Fin.ofNat 13 (i.val + 1)) = i := by
    apply Fin.ext
    change (i.val + 1) % 13 - 1 = i.val
    omega
  have pointNZ (i : Fin 25) (hi : i.val < 12) : Fin.ofNat 13 (i.val + 1) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change (i.val + 1) % 13 = 0 at hv
    omega
  have lineInv (i : Fin 25) (hi : 12 ≤ i.val) :
      ln (Fin.ofNat 13 (i.val - 12)) = i := by
    apply Fin.ext
    change 12 + (i.val - 12) % 13 = i.val
    omega
  have points (p : Fin 13) (hp : p ≠ 0) :
      Fin.ofNat 13 ((pt p).val + 1) = p := by
    have hn : p.val ≠ 0 := fun h => hp (Fin.ext h)
    apply Fin.ext
    change (p.val - 1 + 1) % 13 = p.val
    omega
  have lines (l : Fin 13) : Fin.ofNat 13 ((ln l).val - 12) = l := by
    apply Fin.ext
    change (12 + l.val - 12) % 13 = l.val
    omega
  have table : ∀ u v : Fin 25,
      (u.val < 12 ∧ 12 ≤ v.val ∧
        (u.val + v.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ↔
      u.val < 12 ∧ 12 ≤ v.val ∧
        Fin.ofNat 13 (u.val + 1) + Fin.ofNat 13 (v.val - 12) ∈ D := by
    dsimp only [D]
    intro u v
    by_cases hu : u.val < 12
    · by_cases hv : 12 ≤ v.val
      · simp only [hu, hv, true_and]
        have hval : (Fin.ofNat 13 (u.val + 1) +
            Fin.ofNat 13 (v.val - 12)).val = (u.val + v.val + 2) % 13 := by
          change ((u.val + 1) % 13 + (v.val - 12) % 13) % 13 = _
          omega
        simp only [List.mem_cons, List.not_mem_nil, or_false,
          Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        change (_ = 0 ∨ _ = 1 ∨ _ = 3 ∨ _ = 9) ↔
          (_ = 0 ∨ _ = 1 ∨ _ = 3 ∨ _ = 9)
        rw [hval]
      · simp [hv]
    · simp [hu]
  refine ⟨C, q, hm, size, ho, hq, ?_⟩
  intro x
  dsimp only
  let s := Finset.univ.filter fun p : Fin 13 => p ≠ 0 ∧ x (pt p) = true
  let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
  have smem {p : Fin 13} (hp : p ∈ s) : p ≠ 0 ∧ x (pt p) = true :=
    (Finset.mem_filter.mp hp).2
  have tmem {l : Fin 13} (hl : l ∈ t) : x (ln l) = true :=
    (Finset.mem_filter.mp hl).2
  have repr : vec s t = x := by
    funext i
    by_cases hi : i.val < 12
    · simp only [vec, ite_eq_left hi, s, Finset.mem_filter, Finset.mem_univ,
        true_and, pointInv i hi]
      cases x i with
      | false => simp
      | true => exact decide_eq_true_eq.mpr ⟨pointNZ i hi, rfl⟩
    · simp only [vec, ite_eq_right hi, t, Finset.mem_filter, Finset.mem_univ,
        true_and, lineInv i (by omega)]
      cases x i <;> rfl
  have arr : (∃ u v : Fin 25,
      (u.val < 12 ∧ 12 ≤ v.val ∧
        (u.val + v.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧
      x u = true ∧ x v = true) ↔ ∃ p ∈ s, ∃ l ∈ t, p + l ∈ D := by
    constructor
    · rintro ⟨u, v, he, hx, hy⟩
      obtain ⟨hu, hv, hnear⟩ := (table u v).mp he
      refine ⟨Fin.ofNat 13 (u.val + 1), ?_, Fin.ofNat 13 (v.val - 12), ?_, hnear⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pointNZ u hu,
          by rw [pointInv u hu]; exact hx⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [lineInv v hv]; exact hy⟩
    · rintro ⟨p, hp, l, hl, hnear⟩
      refine ⟨pt p, ln l, (table _ _).mpr ⟨?_, ?_, ?_⟩, (smem hp).2, tmem hl⟩
      · dsimp only [pt]
        omega
      · dsimp only [ln]
        omega
      · simpa only [points p (smem hp).1, lines l] using hnear
  have mainGraph : read s t = true ↔ ∃ p ∈ s, ∃ l ∈ t, p + l ∈ D := by
    constructor
    · intro yes
      by_contra no
      have miss : ∀ p ∈ s, ∀ l ∈ t, p + l ∉ D :=
        fun p hp l hl h => no ⟨p, hp, l, hl, h⟩
      rcases rectangles s t miss with hs | ht
      · have sub : t ⊆ off s := by
          intro l hl
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => miss p hp l hl⟩
        have bad := mono (Finset.Subset.rfl : s ⊆ s) sub C.output yes
        change read s (off s) = true at bad
        rw [(tests.2 s hs).1] at bad
        exact Bool.noConfusion bad
      · have sub : s ⊆ off t := by
          intro p hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl =>
            by simpa only [add_comm] using miss p hp l hl⟩
        have bad := mono sub (Finset.Subset.rfl : t ⊆ t) C.output yes
        change read (off t) t = true at bad
        rw [(tests.2 t ht).2.1] at bad
        exact Bool.noConfusion bad
    · rintro ⟨p, hp, l, hl, hnear⟩
      exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
        C.output ((tests.1 p l hnear).1 (smem hp).1)
  constructor
  · simpa only [read, repr] using mainGraph.trans arr.symm
  · intro rejected
    have noF : read s t = false := by simpa only [read, repr] using rejected
    have miss : ∀ p ∈ s, ∀ l ∈ t, p + l ∉ D := by
      intro p hp l hl hnear
      have yes := mainGraph.mpr ⟨p, hp, l, hl, hnear⟩
      rw [noF] at yes
      exact Bool.noConfusion yes
    have auxMeaning : aux s t = true ↔ ∃ l ∈ t, l ∈ D := by
      constructor
      · intro yes
        by_contra no
        have outside : ∀ l ∈ t, l ∉ D := fun l hl hd => no ⟨l, hl, hd⟩
        rcases rectangles s t miss with hs | ht
        · have sub : t ⊆ off s \ D := by
            intro l hl
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, fun p hp => miss p hp l hl⟩, outside l hl⟩
          have bad := mono (Finset.Subset.rfl : s ⊆ s) sub q yes
          change aux s (off s \ D) = true at bad
          rw [(tests.2 s hs).2.2.1] at bad
          exact Bool.noConfusion bad
        · have sub : s ⊆ off t := by
            intro p hp
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl =>
              by simpa only [add_comm] using miss p hp l hl⟩
          have sub' : t ⊆ t \ D := fun l hl => Finset.mem_sdiff.mpr ⟨hl, outside l hl⟩
          have bad := mono sub sub' q yes
          change aux (off t) (t \ D) = true at bad
          rw [(tests.2 t ht).2.2.2] at bad
          exact Bool.noConfusion bad
      · rintro ⟨l, hl, hd⟩
        exact mono (Finset.empty_subset s) (Finset.singleton_subset_iff.mpr hl) q
          ((tests.1 0 l (by simpa using hd)).2 rfl)
    have targetMeaning : (x 12 || x 13 || x 15 || x 21) = true ↔ ∃ l ∈ t, l ∈ D := by
      simp [D, t, ln, Bool.or_eq_true, or_assoc, and_or_left, exists_or]
    have eqaux : aux s t = (x 12 || x 13 || x 15 || x 21) :=
      Bool.eq_iff_iff.mpr (auxMeaning.trans targetMeaning.symm)
    simpa only [aux, repr] using eqaux
