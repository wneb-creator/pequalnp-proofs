import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.PlaneMatching

-- The finite Hall argument below is adapted from Mathlib.Combinatorics.Hall.Finite,
-- Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. Apache 2.0.

open Finset

universe u v

namespace FiniteHall

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  have := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases! he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, SetCoe.exists, exists_and_right,
        exists_eq_right]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  · subst s'
    simp

-- First case of the inductive step: assuming that
-- `∀ (s : Finset ι), s.Nonempty → s ≠ univ → #s < #(s.biUnion t)`
-- and that the statement of **Hall's Marriage Theorem** is true for all
-- `ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  have := Classical.decEq ι
  -- Choose an arbitrary element `x : ι` and `y : t x`.
  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne
  -- Restrict to everything except `x` and `y`.
  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩
  -- Extend the resulting function.
  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  have := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective, Nat.add_sub_cancel_left]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff_of_subset]
  · gcongr
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

-- Second case of the inductive step: assuming that
-- `∃ (s : Finset ι), s ≠ univ → #s = #(s.biUnion t)`
-- and that the statement of **Hall's Marriage Theorem** is true for all
-- `ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have := Classical.decEq ι
  -- Restrict to `s`
  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩
  -- Restrict to `sᶜ` in the domain and `(s.biUnion t)ᶜ` in the codomain.
  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩
  -- Put them together
  have f''_notMem_biUnion : ∀ (x'') (hx'' : x'' ∉ s), f'' ⟨x'', hx''⟩ ∉ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : x'' ∉ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    grind
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

-- Here we combine the two inductive steps into a full strong induction proof,
-- completing the proof the harder direction of **Hall's Marriage Theorem**.
theorem hall_hard_inductive (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases! h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
    · rcases h with ⟨s, sne, snu, sle⟩
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end FiniteHall


lemma plane_point_degree_le (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) (p : Fin N) :
    (Finset.univ.filter (fun l : Fin N => p ∈ S l)).card ≤ q + 1 := by
  classical
  set L := Finset.univ.filter (fun l : Fin N => p ∈ S l) with hL
  have hsub : L.biUnion (fun l => (S l).erase p) ⊆ Finset.univ.erase p := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_erase] at hx
    obtain ⟨_, _, hx, _⟩ := hx
    exact Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩
  have hdisj : (L : Set (Fin N)).PairwiseDisjoint (fun l => (S l).erase p) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hL] at hi hj
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_erase] at hxi hxj
    obtain ⟨l, _, hl⟩ := hU p x (Ne.symm hxi.1)
    exact hij ((hl i ⟨hi, hxi.2⟩).trans (hl j ⟨hj, hxj.2⟩).symm)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  have hterm : ∀ l ∈ L, ((S l).erase p).card = q := by
    intro l hl
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.card_erase_of_mem hl, hS l]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem
    (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hcard
  have h1 : N - 1 = (q + 1) * q := by
    rw [hN, Nat.add_sub_cancel]; simp [pow_two, Nat.add_mul]
  rw [h1] at hcard
  exact Nat.le_of_mul_le_mul_right hcard hq

lemma plane_hall_lines (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) :
    ∃ σ : Fin N → Fin N, Function.Injective σ ∧ ∀ l, σ l ∈ S l := by
  classical
  apply FiniteHall.hall_hard_inductive
  intro B
  set U := B.biUnion S with hUdef
  have h1 : ∑ l ∈ B, (U ∩ S l).card = B.card * (q + 1) := by
    rw [Finset.sum_congr rfl (fun l hl => by
      rw [Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem S hl), hS]),
      Finset.sum_const, smul_eq_mul]
  have h2 : ∑ l ∈ B, (U ∩ S l).card = ∑ p ∈ U, (B.filter (fun l => p ∈ S l)).card := by
    simp_rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have h3 : ∑ p ∈ U, (B.filter (fun l => p ∈ S l)).card ≤ U.card * (q + 1) := by
    have := Finset.sum_le_card_nsmul U (fun p => (B.filter (fun l => p ∈ S l)).card) (q + 1)
      (fun p _ => le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ B))) (plane_point_degree_le q N S hq hN hS hU p))
    simpa [smul_eq_mul] using this
  have h4 : B.card * (q + 1) ≤ U.card * (q + 1) := by omega
  exact Nat.le_of_mul_le_mul_right h4 (Nat.succ_pos q)

lemma plane_perfect_matching (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p, I p (σ p) := by
  classical
  let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l)
  obtain ⟨f, hf, hmem⟩ := plane_hall_lines q N S hq hN hS (by simpa [S] using hU)
  let e : Equiv.Perm (Fin N) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  refine ⟨e.symm, ?_⟩
  intro p
  have h := (Finset.mem_filter.mp (hmem (e.symm p))).2
  have he : f (e.symm p) = p := e.apply_symm_apply p
  rwa [he] at h

end PEqualNP.Outside.L_meta_2583.PlaneMatching
