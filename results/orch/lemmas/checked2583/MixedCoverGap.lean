import PlaneGeometry
namespace PEqualNP.Outside.L_meta_2583.PlaneGeometry

lemma lines_intersect {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hne : l ≠ m) : ∃! p : Fin N, I p l ∧ I p m := by
  let P := Finset.univ.filter (fun p => I p l)
  let family := fun p : Fin N => (Finset.univ.filter (fun k => I p k)).erase l
  have disjoint : (P : Set (Fin N)).PairwiseDisjoint family := by
    intro p hp p' hp' hpp
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have pk : I p k := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
    have p'k : I p' k := (Finset.mem_filter.mp (Finset.mem_erase.mp hk').2).2
    have pl : I p l := (Finset.mem_filter.mp hp).2
    have p'l : I p' l := (Finset.mem_filter.mp hp').2
    exact (Finset.ne_of_mem_erase hk) ((hu p p' hpp).unique ⟨pk, p'k⟩ ⟨pl, p'l⟩)
  have each : ∀ p ∈ P, (family p).card = q := by
    intro p hp
    rw [Finset.card_erase_of_mem (by simpa [P] using hp), lines_through q N I hq hN hl hu p]
    rfl
  have card : (P.biUnion family).card = (Finset.univ.erase l).card := by
    rw [Finset.card_biUnion disjoint, Finset.sum_congr rfl each, Finset.sum_const,
      smul_eq_mul, show P.card = q + 1 from hl l,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, hN]
    rw [Nat.add_sub_cancel]
    ring
  have sub : P.biUnion family ⊆ Finset.univ.erase l := by
    intro k hk
    obtain ⟨p, hp, hk⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hk, Finset.mem_univ _⟩
  have same := Finset.eq_of_subset_of_card_le sub card.ge
  have mm : m ∈ P.biUnion family := by rw [same]; simp [hne.symm]
  obtain ⟨p, hp, hm⟩ := Finset.mem_biUnion.mp mm
  have pl : I p l := (Finset.mem_filter.mp hp).2
  have pm : I p m := (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2
  refine ⟨p, ⟨pl, pm⟩, ?_⟩
  intro p' h'
  by_contra diff
  exact hne ((hu p' p diff).unique ⟨h'.1, pl⟩ ⟨h'.2, pm⟩)

lemma regular_independent_bound {N d : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (U V S T : Finset (Fin N)) (hd : 0 < d) (hS : S ⊆ U) (hT : T ⊆ V)
    (rows : ∀ p ∈ U, (V.filter (fun l => I p l)).card = d)
    (cols : ∀ l ∈ V, (U.filter (fun p => I p l)).card = d)
    (none : ∀ p ∈ S, ∀ l ∈ T, ¬ I p l) : S.card + T.card ≤ V.card := by
  have left : ((S ×ˢ V).filter (fun e : Fin N × Fin N => I e.1 e.2)).card = S.card * d := by
    rw [cardL, Finset.sum_congr rfl (fun p hp => rows p (hS hp)), Finset.sum_const, smul_eq_mul]
  have right : ((U ×ˢ (V \ T)).filter (fun e : Fin N × Fin N => I e.1 e.2)).card = (V \ T).card * d := by
    rw [cardR, Finset.sum_congr rfl (fun l hl => cols l (Finset.mem_sdiff.mp hl).1),
      Finset.sum_const, smul_eq_mul]
  have sub : (S ×ˢ V).filter (fun e : Fin N × Fin N => I e.1 e.2) ⊆
      (U ×ˢ (V \ T)).filter (fun e : Fin N × Fin N => I e.1 e.2) := by
    rintro ⟨p, l⟩ h
    obtain ⟨hmem, hi⟩ := Finset.mem_filter.mp h
    obtain ⟨hp, hl⟩ := Finset.mem_product.mp hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hS hp, ?_⟩, hi⟩
    exact Finset.mem_sdiff.mpr ⟨hl, fun ht => none p hp l ht hi⟩
  have bound := Finset.card_le_card sub
  rw [left, right] at bound
  have cb := Nat.le_of_mul_le_mul_right bound hd
  rw [Finset.card_sdiff_of_subset hT] at cb
  have tc := Finset.card_le_card hT
  omega

lemma residual_degrees {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (outside : ¬ I p l) :
    let U := (Finset.univ.filter (fun x => ¬ I x l)).erase p
    let V := (Finset.univ.filter (fun m => ¬ I p m)).erase l
    (∀ x ∈ U, (V.filter (fun m => I x m)).card = q) ∧
    (∀ m ∈ V, (U.filter (fun x => I x m)).card = q) := by
  dsimp
  constructor
  · intro x hx
    have xp : x ≠ p := Finset.ne_of_mem_erase hx
    have xl : ¬ I x l := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
    obtain ⟨m, hm, unique⟩ := hu x p xp
    have same : (((Finset.univ.filter (fun k => ¬ I p k)).erase l).filter (fun k => I x k)) =
        (Finset.univ.filter (fun k => I x k)).erase m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨kl, pk⟩, xk⟩
        exact ⟨fun e => pk (e ▸ hm.2), xk⟩
      · rintro ⟨km, xk⟩
        exact ⟨⟨fun e => xl (e ▸ xk), fun pk => km (unique k ⟨xk, pk⟩)⟩, xk⟩
    rw [same, Finset.card_erase_of_mem (by simp [hm.1]), lines_through q N I hq hN hl hu x]
    rfl
  · intro m hm
    have ml : m ≠ l := Finset.ne_of_mem_erase hm
    have pm : ¬ I p m := (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2
    obtain ⟨x, hx, unique⟩ := lines_intersect I hq hN hl hu m l ml
    have same : (((Finset.univ.filter (fun y => ¬ I y l)).erase p).filter (fun y => I y m)) =
        (Finset.univ.filter (fun y => I y m)).erase x := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨yp, yl⟩, ym⟩
        exact ⟨fun e => yl (e ▸ hx.2), ym⟩
      · rintro ⟨yx, ym⟩
        exact ⟨⟨fun e => pm (e ▸ ym), fun yl => yx (unique y ⟨ym, yl⟩)⟩, ym⟩
    rw [same, Finset.card_erase_of_mem (by simp [hx.1]), hl m]
    rfl

lemma mixed_independent_bound {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (S T : Finset (Fin N)) (hs : S.Nonempty) (ht : T.Nonempty)
    (none : ∀ p ∈ S, ∀ l ∈ T, ¬ I p l) : S.card + T.card ≤ q ^ 2 + 1 := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨l, hlT⟩ := ht
  let U := (Finset.univ.filter (fun x => ¬ I x l)).erase p
  let V := (Finset.univ.filter (fun m => ¬ I p m)).erase l
  have outside := none p hp l hlT
  obtain ⟨rows, cols⟩ := residual_degrees I hq hN hl hu p l outside
  have hS : S.erase p ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, none x (Finset.mem_of_mem_erase hx) l hlT⟩⟩
  have hT : T.erase l ⊆ V := by
    intro m hm
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hm,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, none p hp m (Finset.mem_of_mem_erase hm)⟩⟩
  have bound := regular_independent_bound I U V (S.erase p) (T.erase l) hq hS hT rows cols
    (fun x hx m hm => none x (Finset.mem_of_mem_erase hx) m (Finset.mem_of_mem_erase hm))
  have vc : V.card = q ^ 2 - 1 := by
    have count := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun m => I p m)
    rw [lines_through q N I hq hN hl hu p, Finset.card_univ, Fintype.card_fin] at count
    rw [Finset.card_erase_of_mem (by simp [outside])]
    omega
  rw [Finset.card_erase_of_mem hp, Finset.card_erase_of_mem hlT, vc] at bound
  have qq : 0 < q ^ 2 := pow_pos hq 2
  have sc := Finset.card_pos.mpr ⟨p, hp⟩
  have tc := Finset.card_pos.mpr ⟨l, hlT⟩
  omega


lemma proper_mixed_cover_bound {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (aProper : A ≠ Finset.univ) (bProper : B ≠ Finset.univ)
    (cover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N + q ≤ A.card + B.card := by
  obtain ⟨p, hp⟩ : ∃ p : Fin N, p ∉ A := by
    by_contra! all
    exact aProper (Finset.eq_univ_of_forall all)
  obtain ⟨l, hlB⟩ : ∃ l : Fin N, l ∉ B := by
    by_contra! all
    exact bProper (Finset.eq_univ_of_forall all)
  have none : ∀ p ∈ Finset.univ \ A, ∀ l ∈ Finset.univ \ B, ¬ I p l := by
    intro x hx y hy hi
    rcases cover x y hi with h | h
    · exact (Finset.mem_sdiff.mp hx).2 h
    · exact (Finset.mem_sdiff.mp hy).2 h
  have bound := mixed_independent_bound I hq hN hl hu (Finset.univ \ A) (Finset.univ \ B)
    ⟨p, by simp [hp]⟩ ⟨l, by simp [hlB]⟩ none
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),
    Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, Fintype.card_fin] at bound
  have aCard : A.card ≤ N := by simpa using Finset.card_le_card (Finset.subset_univ A)
  have bCard : B.card ≤ N := by simpa using Finset.card_le_card (Finset.subset_univ B)
  omega

lemma proper_mixed_cover_pays_debt {q N s : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (aProper : A ≠ Finset.univ) (bProper : B ≠ Finset.univ)
    (cover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B)
    (cost : (edges I).card + A.card + B.card ≤ s + 1 + q) :
    N * (q + 2) ≤ s + 1 := by
  have gap := proper_mixed_cover_bound I hq hN hl hu A B aProper bProper cover
  rw [edges_card I hl] at cost
  have expand : N * (q + 2) = N * (q + 1) + N := by ring
  omega

end PEqualNP.Outside.L_meta_2583.PlaneGeometry
