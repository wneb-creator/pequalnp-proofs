import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5363

open SimpleGraph

section Girth

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

-- In a graph whose cycles all have length at least five, two distinct vertices have at most one
-- common neighbour.
theorem one_common (hg : ∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) {x y u v : V}
    (hxy : x ≠ y) (hxu : G.Adj x u) (huy : G.Adj u y) (hxv : G.Adj x v) (hvy : G.Adj v y) :
    u = v := by
  by_contra h
  let w : G.Walk x x := .cons hxu (.cons huy (.cons hvy.symm (.cons hxv.symm Walk.nil)))
  have hc : w.IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · simp [w, Walk.edges_cons, hxy, hxy.symm, hxu.ne, huy.ne, hxv.ne, hvy.ne,
        h, hxu.ne.symm, huy.ne.symm, hxv.ne.symm, hvy.ne.symm]
    · simp [w]
    · simp [w, Walk.support_cons, h, hxy, hxy.symm, hxu.ne, huy.ne, hxv.ne, hvy.ne, hxu.ne.symm,
        huy.ne.symm, hxv.ne.symm, hvy.ne.symm]
  have h5 := hg x w hc
  simp [w] at h5

-- Membership in a two-element set.
theorem mem_pair' {x u v : V} (h : x ∈ ({u, v} : Finset V)) : x = u ∨ x = v := by
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.mp h)

-- A pair that is not an edge spans an independent set of vertices.
theorem pair_indep {u v : V} (h : ¬ G.Adj u v) :
    ∀ x ∈ ({u, v} : Finset V), ∀ y ∈ ({u, v} : Finset V), ¬ G.Adj x y := by
  intro x hx y hy
  rcases mem_pair' hx with hx1 | hx1 <;> rcases mem_pair' hy with hy1 | hy1
  · subst hx1
    subst hy1
    exact fun c0 => G.loopless.irrefl _ c0
  · subst hx1
    subst hy1
    exact h
  · subst hx1
    subst hy1
    exact fun c0 => h c0.symm
  · subst hx1
    subst hy1
    exact fun c0 => G.loopless.irrefl _ c0

end Girth

section Count

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem card_pred (c : ℕ) : c * (c - 1) + c = c * c := by
  cases c with
  | zero => rfl
  | succ d =>
    rw [Nat.succ_sub_one]
    ring

-- The neighbours of `u` that lie in `W`.
def nb (W : Finset V) (u : V) : Finset V :=
  W.filter fun w => G.Adj w u

-- The ordered edges of `G` with both ends in `W`.
def oe (W : Finset V) : Finset (V × V) :=
  W.biUnion fun u => ({u} : Finset V) ×ˢ nb G W u

theorem mem_nb {W : Finset V} {u w : V} : w ∈ nb G W u ↔ w ∈ W ∧ G.Adj w u := by
  simp [nb]

theorem card_oe (W : Finset V) : (oe G W).card = ∑ u ∈ W, (nb G W u).card := by
  rw [oe]
  refine (Finset.card_biUnion ?_).trans (Finset.sum_congr rfl ?_)
  · intro u hu u' hu' hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    simp only [Finset.mem_product, Finset.mem_singleton] at hz hz'
    exact hne (hz.1 ▸ hz'.1)
  · intro u _
    rw [Finset.card_product, Finset.card_singleton, one_mul]

-- Inside any vertex set `W` of size `N`, at most `N * N` pairs of vertices have a common
-- neighbour in `W`.
theorem cherries (hg : ∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) (W : Finset V) :
    ∑ u ∈ W, (nb G W u).card * ((nb G W u).card - 1) ≤ W.card * W.card := by
  classical
  let fib : V → Finset (V × V) := fun u =>
    ((nb G W u) ×ˢ (nb G W u)).filter fun z => z.1 ≠ z.2
  have hfib : ∀ u ∈ W, (fib u).card = (nb G W u).card * ((nb G W u).card - 1) := by
    intro u _
    have h2 : (((nb G W u) ×ˢ (nb G W u)).filter fun z : V × V => z.1 = z.2).card =
        (nb G W u).card := by
      have he : ((nb G W u) ×ˢ (nb G W u)).filter (fun z : V × V => z.1 = z.2) =
          (nb G W u).diag := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2 ▸ h1⟩, h2⟩
      rw [he, Finset.diag_card]
    have h3 := Finset.card_filter_add_card_filter_not
      (s := nb G W u ×ˢ nb G W u) (fun z : V × V => z.1 ≠ z.2)
    simp only [not_not] at h3
    rw [Finset.card_product, h2] at h3
    have h4 := card_pred (nb G W u).card
    rw [← h4] at h3
    change (fib u).card = _
    unfold fib
    exact Nat.add_right_cancel h3
  have hdisj : ((W : Set V).PairwiseDisjoint fib) := by
    intro u hu u' hu' hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    simp only [fib, Finset.mem_filter, Finset.mem_product] at hz hz'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    obtain ⟨⟨h1', h2'⟩, h3'⟩ := hz'
    have a1 := (mem_nb G).mp h1
    have a2 := (mem_nb G).mp h2
    have a1' := (mem_nb G).mp h1'
    have a2' := (mem_nb G).mp h2'
    exact hne (one_common hg h3 a1.2 a2.2.symm a1'.2 a2'.2.symm)
  have hsub : W.biUnion fib ⊆ W ×ˢ W := by
    intro z hz
    obtain ⟨u, _, hz⟩ := Finset.mem_biUnion.mp hz
    simp only [fib, Finset.mem_filter, Finset.mem_product] at hz
    have b1 := (mem_nb G).mp hz.1.1
    have b2 := (mem_nb G).mp hz.1.2
    exact Finset.mem_product.mpr ⟨b1.1, b2.1⟩
  calc ∑ u ∈ W, (nb G W u).card * ((nb G W u).card - 1)
      = ∑ u ∈ W, (fib u).card := (Finset.sum_congr rfl hfib).symm
    _ = (W.biUnion fib).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (W ×ˢ W).card := Finset.card_le_card hsub
    _ = W.card * W.card := Finset.card_product _ _

-- Inside any vertex set `W` of size `N`, the number `S` of ordered edges satisfies
-- `S ^ 2 ≤ 2 * N ^ 3`.
theorem edges_bound (hg : ∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) (W : Finset V) :
    (∑ u ∈ W, (nb G W u).card) ^ 2 ≤ 2 * W.card ^ 3 := by
  let d : V → ℕ := fun u => (nb G W u).card
  have hcs : (∑ u ∈ W, d u * 1) ^ 2 ≤ (∑ u ∈ W, d u ^ 2) * ∑ u ∈ W, (1 : ℕ) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq W d (fun _ => 1)
  have h1 : (∑ u ∈ W, d u) ^ 2 ≤ (∑ u ∈ W, d u ^ 2) * W.card := by
    simpa using hcs
  have h2 : ∑ u ∈ W, d u ^ 2 = (∑ u ∈ W, d u * (d u - 1)) + ∑ u ∈ W, d u := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h4 := card_pred (d u)
    rw [pow_two, ← h4]
  have h3 : ∑ u ∈ W, d u ≤ W.card * W.card := by
    calc ∑ u ∈ W, d u ≤ ∑ _u ∈ W, W.card := by
          apply Finset.sum_le_sum
          intro u _
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = W.card * W.card := by simp [Finset.sum_const]
  have hch := cherries G hg W
  change (∑ u ∈ W, d u) ^ 2 ≤ 2 * W.card ^ 3
  calc (∑ u ∈ W, d u) ^ 2
      ≤ ((∑ u ∈ W, d u * (d u - 1)) + ∑ u ∈ W, d u) * W.card :=
        h1.trans (Nat.mul_le_mul_right _ (by rw [h2]))
    _ = (∑ u ∈ W, d u * (d u - 1)) * W.card + (∑ u ∈ W, d u) * W.card := add_mul _ _ _
    _ ≤ (W.card * W.card) * W.card + (W.card * W.card) * W.card :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hch) (Nat.mul_le_mul_right _ h3)
    _ = 2 * W.card ^ 3 := by rw [pow_succ, pow_two]; ring

end Count

section Conflicts

variable {ι : Type*} [DecidableEq ι] {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

-- In a family whose members carry pairwise disjoint signatures, the number of conflicts inside
-- a subfamily is at most the number of ordered edges between the signatures.
theorem conflicts_le (P : Finset ι) (sig : ι → Finset V) (r : ι → ι → Bool)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (sig p) (sig q))
    (hwit : ∀ p ∈ P, ∀ q ∈ P, r p q = true → ∃ x, x ∈ sig p ∧ ∃ y, y ∈ sig q ∧ G.Adj x y)
    {Q : Finset ι} (hQ : Q ⊆ P) {W : Finset V} (hW : Q.biUnion sig ⊆ W) :
    ∑ p ∈ Q, (Q.filter fun q => r p q).card ≤ (oe G W).card := by
  classical
  set Dm := (Q ×ˢ Q).filter fun z => r z.1 z.2 = true with hDm
  set Triples := (Dm ×ˢ (W ×ˢ W)).filter
    fun w => w.2.1 ∈ sig w.1.1 ∧ w.2.2 ∈ sig w.1.2 ∧ G.Adj w.2.1 w.2.2 with hTriples
  have hfib : ∀ p ∈ Q, (Dm.filter fun z => z.1 = p).card = (Q.filter fun q => r p q).card := by
    intro p hpQ
    have he : (Dm.filter fun z => z.1 = p) = (Q.filter fun q => r p q).image (fun q => (p, q)) := by
      ext z
      constructor
      · intro h
        have h' := h
        rw [hDm] at h'
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h'
        obtain ⟨h3, h4⟩ := Finset.mem_filter.mp h1
        obtain ⟨h5, h6⟩ := Finset.mem_product.mp h3
        refine Finset.mem_image.mpr ⟨z.2, Finset.mem_filter.mpr ⟨h6, by rw [← h2]; exact h4⟩,
          Prod.ext h2.symm rfl⟩
      · intro h
        obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
        rw [Prod.mk.injEq] at hq'
        obtain ⟨rfl, rfl⟩ := hq'
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpQ, h1⟩, h2⟩,
          rfl⟩
    rw [he, Finset.card_image_of_injOn (fun a _ b _ h => congrArg Prod.snd h)]
  have hmaps : ∀ z ∈ Dm, z.1 ∈ Q := by
    intro z hz
    have hz' := hz
    rw [hDm] at hz'
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hz').1).1
  have hA : Dm ⊆ Triples.image Prod.fst := by
    intro z hz
    have hz' := hz
    rw [hDm] at hz'
    rcases Finset.mem_filter.mp hz' with ⟨h1, h2⟩
    rcases Finset.mem_product.mp h1 with ⟨h3, h4⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hwit z.1 (hQ h3) z.2 (hQ h4) h2
    refine Finset.mem_image.mpr ⟨(z, (x, y)), ?_, rfl⟩
    rw [hTriples]
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, Finset.mem_product.mpr ⟨
      hW (Finset.mem_biUnion.mpr ⟨z.1, h3, hx⟩),
      hW (Finset.mem_biUnion.mpr ⟨z.2, h4, hy⟩)⟩⟩, ?_⟩
    exact ⟨hx, hy, hxy⟩
  have hB : Triples.image (fun w => w.2) ⊆ oe G W := by
    intro xy hxy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxy
    rw [hTriples] at hw
    rcases Finset.mem_filter.mp hw with ⟨hw1, hw2⟩
    rcases Finset.mem_product.mp hw1 with ⟨_, hwW⟩
    rcases Finset.mem_product.mp hwW with ⟨hx, hy⟩
    rw [oe]
    exact Finset.mem_biUnion.mpr ⟨w.2.1, hx, Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr rfl,
      (mem_nb G).mpr ⟨hy, hw2.2.2.symm⟩⟩⟩
  have hC : ∀ w ∈ Triples, ∀ w' ∈ Triples, w.2 = w'.2 → w = w' := by
    intro w hw w' hw' he
    rw [hTriples] at hw hw'
    rcases Finset.mem_filter.mp hw with ⟨hw1, hw2⟩
    rcases Finset.mem_filter.mp hw' with ⟨hw1', hw2'⟩
    rcases Finset.mem_product.mp hw1 with ⟨hwD, _⟩
    rcases Finset.mem_product.mp hw1' with ⟨hwD', _⟩
    rcases Finset.mem_filter.mp hwD with ⟨hQ2, _⟩
    rcases Finset.mem_filter.mp hwD' with ⟨hQ2', _⟩
    rcases Finset.mem_product.mp hQ2 with ⟨hp, hq⟩
    rcases Finset.mem_product.mp hQ2' with ⟨hp', hq'⟩
    have e1 : w.2.1 ∈ sig w'.1.1 := by rw [he]; exact hw2'.1
    have e2 : w.2.2 ∈ sig w'.1.2 := by rw [he]; exact hw2'.2.1
    have hpq : w.1.1 = w'.1.1 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj _ (hQ hp) _ (hQ hp') hne) hw2.1 e1
    have hqq : w.1.2 = w'.1.2 := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj _ (hQ hq) _ (hQ hq') hne) hw2.2.1 e2
    exact Prod.ext (Prod.ext hpq hqq) he
  calc ∑ p ∈ Q, (Q.filter fun q => r p q).card
      = Dm.card := by
        refine (Finset.sum_congr rfl hfib).symm.trans ?_
        exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Q) hmaps).symm
    _ ≤ (Triples.image Prod.fst).card := Finset.card_le_card hA
    _ ≤ Triples.card := Finset.card_image_le
    _ = (Triples.image fun w => w.2).card := (Finset.card_image_of_injOn hC).symm
    _ ≤ (oe G W).card := Finset.card_le_card hB

-- A nonempty subfamily of `s` members with pairwise disjoint signatures, each of at most two
-- vertices, has a member conflicting with fewer than `t` others whenever `16 * s < t ^ 2`.
theorem exists_low (hg : ∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length)
    (P : Finset ι) (sig : ι → Finset V) (r : ι → ι → Bool)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (sig p) (sig q))
    (hsig : ∀ p ∈ P, (sig p).card ≤ 2)
    (hwit : ∀ p ∈ P, ∀ q ∈ P, r p q = true → ∃ x, x ∈ sig p ∧ ∃ y, y ∈ sig q ∧ G.Adj x y)
    {Q : Finset ι} (hQ : Q ⊆ P) (hNE : Q.Nonempty) {t : ℕ} (ht : 16 * Q.card < t ^ 2) :
    ∃ p ∈ Q, (Q.filter fun q => r p q).card < t := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Q.card := Finset.card_pos.mpr hNE
  have hcardW : (Q.biUnion sig).card ≤ 2 * Q.card := by
    calc (Q.biUnion sig).card ≤ ∑ p ∈ Q, (sig p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ Q, 2 := Finset.sum_le_sum fun p hp => hsig p (hQ hp)
      _ = 2 * Q.card := by simp [Finset.sum_const, Nat.mul_comm]
  have hS2 : (oe G (Q.biUnion sig)).card ^ 2 ≤ 16 * Q.card ^ 3 := by
    rw [card_oe]
    calc (∑ u ∈ Q.biUnion sig, (nb G (Q.biUnion sig) u).card) ^ 2
        ≤ 2 * (Q.biUnion sig).card ^ 3 := edges_bound G hg _
      _ ≤ 2 * (2 * Q.card) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcardW 3)
      _ = 16 * Q.card ^ 3 := by ring
  have hsum : Q.card * t ≤ ∑ p ∈ Q, (Q.filter fun q => r p q).card := by
    calc Q.card * t = ∑ _p ∈ Q, t := by simp [Finset.sum_const]
      _ ≤ ∑ p ∈ Q, (Q.filter fun q => r p q).card := Finset.sum_le_sum fun p hp => hcon p hp
  have hle := conflicts_le P sig r hdisj hwit hQ (le_refl _)
  have h1 : (Q.card * t) ^ 2 ≤ 16 * Q.card ^ 3 := by
    calc (Q.card * t) ^ 2
        ≤ (∑ p ∈ Q, (Q.filter fun q => r p q).card) ^ 2 := Nat.pow_le_pow_left hsum 2
      _ ≤ (oe G (Q.biUnion sig)).card ^ 2 := Nat.pow_le_pow_left hle 2
      _ ≤ 16 * Q.card ^ 3 := hS2
  rw [Nat.mul_pow] at h1
  have h2 : Q.card ^ 2 * t ^ 2 ≤ Q.card ^ 2 * (16 * Q.card) := by
    calc Q.card ^ 2 * t ^ 2 ≤ 16 * Q.card ^ 3 := h1
      _ = Q.card ^ 2 * (16 * Q.card) := by ring
  have h3 : t ^ 2 ≤ 16 * Q.card := le_of_mul_le_mul_left h2 (pow_pos hpos 2)
  omega

end Conflicts

section Greedy

variable {ι : Type*} [DecidableEq ι]

-- Greedy extraction of a conflict-free subfamily from a family in which every nonempty
-- subfamily has a member conflicting with at most `D` of its members.
theorem greedy (r : ι → ι → Bool) (D : ℕ) :
    ∀ (s : ℕ) (Q : Finset ι), Q.card = s → (∀ p ∈ Q, r p p = false) → (∀ p q, r p q = r q p) →
      (∀ Q' ⊆ Q, Q'.Nonempty → ∃ p ∈ Q', (Q'.filter fun q => r p q).card ≤ D) →
      ∃ J : Finset ι, J ⊆ Q ∧ (∀ p ∈ J, ∀ q ∈ J, r p q = false) ∧ Q.card ≤ J.card * (D + 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro Q hcard hirr hsymm hlow
    rcases Finset.eq_empty_or_nonempty Q with hE | hN
    · exact ⟨∅, by simp [hE], by simp, by simp [hE]⟩
    · obtain ⟨p, hp, hdeg⟩ := hlow Q (fun _ hz => hz) hN
      set Nbr := Q.filter (fun q => r p q) with hNbr
      have hpN : p ∉ Nbr := by
        rw [hNbr]
        simp [hirr p hp]
      have hsubN : insert p Nbr ⊆ Q := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | h
        · exact hp
        · exact (Finset.mem_filter.mp h).1
      set Q' := Q \ insert p Nbr with hQ'def
      have hQ'Q : Q' ⊆ Q := by
        rw [hQ'def]
        exact Finset.sdiff_subset
      have hcardQ' : Q'.card + (Nbr.card + 1) = Q.card := by
        have h1 := Finset.card_sdiff_add_card_eq_card hsubN
        rw [Finset.card_insert_of_notMem hpN] at h1
        rwa [hQ'def]
      obtain ⟨J, hJQ', hJind, hJle⟩ :=
        ih Q'.card (by omega) Q' rfl (fun q hq => hirr q (hQ'Q hq)) hsymm
          (fun Q'' hQ''Q' hNE => hlow Q'' (hQ''Q'.trans hQ'Q) hNE)
      have hpJ : p ∉ J := fun h => (Finset.mem_sdiff.mp (hJQ' h)).2 (Finset.mem_insert_self _ _)
      have key : ∀ q' ∈ J, r p q' = false := by
        intro q' hq'
        have hnot : q' ∉ Nbr := fun hqN =>
          (Finset.mem_sdiff.mp (hJQ' hq')).2 (Finset.mem_insert_of_mem hqN)
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact hnot (Finset.mem_filter.mpr ⟨hQ'Q (hJQ' hq'), hc⟩)
      refine ⟨insert p J, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | h
        · exact hp
        · exact hQ'Q (hJQ' h)
      · intro p' hp' q' hq'
        rcases Finset.mem_insert.mp hp' with rfl | hp'J
        · rcases Finset.mem_insert.mp hq' with rfl | hq'J
          · exact hirr _ hp
          · exact key q' hq'J
        · rcases Finset.mem_insert.mp hq' with rfl | hq'J
          · rw [hsymm]
            exact key p' hp'J
          · exact hJind p' hp'J q' hq'J
      · rw [Finset.card_insert_of_notMem hpJ, add_mul, one_mul, ← hcardQ']
        have h1 : Q'.card + (Nbr.card + 1) ≤ J.card * (D + 1) + (D + 1) :=
          Nat.add_le_add hJle (by omega)
        omega

end Greedy

section Classes

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

-- A non-edge pair containing `c` whose part outside `T` is nonempty, where `c` lies in `T`,
-- consists of `c` and one vertex `u` outside `T`.
theorem thru {p : V × V} {c : V} {T : Finset V} (hedge : ¬ G.Adj p.1 p.2)
    (hc : c ∈ ({p.1, p.2} : Finset V)) (hcT : c ∈ T)
    (hne : (({p.1, p.2} : Finset V) \ T).Nonempty) :
    ∃ u : V, u ∉ T ∧ ({p.1, p.2} : Finset V) = {c, u} ∧
      ({p.1, p.2} : Finset V) \ T = {u} ∧ ¬ G.Adj c u := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨hu1, hu2⟩ := Finset.mem_sdiff.mp hu
  have huc : u ≠ c := fun h => hu2 (by rw [h]; exact hcT)
  have hpairs : ({p.1, p.2} : Finset V) = {c, u} := by
    rcases mem_pair' hc with h2 | h2 <;> rcases mem_pair' hu1 with h1 | h1
    · exact absurd (h2.trans h1.symm) (Ne.symm huc)
    · rw [h2, h1]
    · rw [h2, h1, Finset.pair_comm]
    · exact absurd (h2.trans h1.symm) (Ne.symm huc)
  refine ⟨u, hu2, hpairs, ?_, ?_⟩
  · rw [hpairs]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, hT⟩
      rcases h with hx | hx
      · exact absurd hcT (hx ▸ hT)
      · exact hx
    · intro h
      exact ⟨Or.inr h, by rw [h]; exact hu2⟩
  · exact pair_indep hedge c (by rw [hpairs]; exact Finset.mem_insert_self _ _)
      u (by rw [hpairs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

-- An edge between two non-edge pairs that both contain `c` and have a part outside `T` joins
-- their parts outside `T`.
theorem wit_c {p q : V × V} {c : V} {T : Finset V} (hp : ¬ G.Adj p.1 p.2)
    (hcp : c ∈ ({p.1, p.2} : Finset V)) (hcpT : c ∈ T)
    (hnp : (({p.1, p.2} : Finset V) \ T).Nonempty) (hq : ¬ G.Adj q.1 q.2)
    (hcq : c ∈ ({q.1, q.2} : Finset V)) (hcqT : c ∈ T)
    (hnq : (({q.1, q.2} : Finset V) \ T).Nonempty)
    (h : ∃ x ∈ ({p.1, p.2} : Finset V), ∃ y ∈ ({q.1, q.2} : Finset V), G.Adj x y) :
    ∃ x, x ∈ ({p.1, p.2} : Finset V) \ T ∧
      ∃ y, y ∈ ({q.1, q.2} : Finset V) \ T ∧ G.Adj x y := by
  obtain ⟨u, hu, hpu, hps, hcu⟩ := thru hp hcp hcpT hnp
  obtain ⟨v, hv, hqv, hqs, hcv⟩ := thru hq hcq hcqT hnq
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  rw [hpu] at hx
  rw [hqv] at hy
  rcases mem_pair' hx with hx1 | hx1 <;> rcases mem_pair' hy with hy1 | hy1
  · subst hx1
    subst hy1
    exact absurd hxy (G.loopless.irrefl _)
  · subst hx1
    subst hy1
    exact absurd hxy hcv
  · subst hx1
    subst hy1
    exact absurd hxy (fun c0 => hcu c0.symm)
  · subst hx1
    subst hy1
    refine ⟨x, ?_, y, ?_, hxy⟩
    · rw [hps]
      exact Finset.mem_singleton_self _
    · rw [hqs]
      exact Finset.mem_singleton_self _

-- An edge between two non-edge pairs that both avoid `a` and `b` joins their parts outside
-- `{a, b}`.
theorem wit_r {p q : V × V} {a b : V} (ha1 : a ∉ ({p.1, p.2} : Finset V))
    (hb1 : b ∉ ({p.1, p.2} : Finset V)) (ha2 : a ∉ ({q.1, q.2} : Finset V))
    (hb2 : b ∉ ({q.1, q.2} : Finset V))
    (h : ∃ x ∈ ({p.1, p.2} : Finset V), ∃ y ∈ ({q.1, q.2} : Finset V), G.Adj x y) :
    ∃ x, x ∈ ({p.1, p.2} : Finset V) \ {a, b} ∧
      ∃ y, y ∈ ({q.1, q.2} : Finset V) \ {a, b} ∧ G.Adj x y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨x, Finset.mem_sdiff.mpr ⟨hx, ?_⟩, y, Finset.mem_sdiff.mpr ⟨hy, ?_⟩, hxy⟩
  · intro c
    rcases mem_pair' c with c | c
    · exact ha1 (c ▸ hx)
    · exact hb1 (c ▸ hx)
  · intro c
    rcases mem_pair' c with c | c
    · exact ha2 (c ▸ hy)
    · exact hb2 (c ▸ hy)

end Classes

end PEqualNP.Outside.L_meta_5363

open PEqualNP.Outside.L_meta_5363 in
theorem PEqualNP.Outside.L_meta_5363 : ∀ (x1 : ℕ),   ∃ (x2 : ℕ),     ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)),       (∀ (x5 : Fin x3) (x6 : x4.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →         ∀ (x6 x7 : Fin x3) (x8 : Finset (Fin x3 × Fin x3)),           x2 ≤ x8.card →             (∀ x10 ∈ x8, ¬x4.Adj x10.1 x10.2) →               (have x11 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x11 : Fin x3 × Fin x3) => {x11.1, x11.2} \ {x6, x7};                 ∀ x12 ∈ x8, ∀ x14 ∈ x8, x12 ≠ x14 → Disjoint (x11 x12) (x11 x14)) →                 ∃ (x12 : Finset (Fin x3)), (∀ x13 ∈ x12, ∀ x15 ∈ x12, ¬x4.Adj x13 x15) ∧ ∀ (x13 : Finset (Fin x3)), x13.card ≤ x1 → x6 ∉ x13 → x7 ∉ x13 → ∃ x17 ∈ x8, x17.1 ∈ x12 \ x13 ∧ x17.2 ∈ x12 \ x13 := by
  classical
  intro k
  refine ⟨256 * (k + 1) ^ 2, ?_⟩
  intro n G hg a b P hP hedge hdisj
  set K : ℕ := (k + 1) ^ 2 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact pow_pos (Nat.succ_pos k) 2
  set M : ℕ := 64 * K with hM
  set t : ℕ := 33 * (k + 1) + 1 with htdef
  have htpos : 0 < t := by
    rw [htdef]
    omega
  have ht2 : 16 * M < t ^ 2 := by
    rw [hM, htdef]
    nlinarith [hKpos]
  have hMt : (k + 1) * t ≤ M := by
    rw [hM, htdef]
    nlinarith [hKpos]
  set sig : Fin n × Fin n → Finset (Fin n) :=
    fun p => ({p.1, p.2} : Finset (Fin n)) \ {a, b} with hsigdef
  set r : Fin n × Fin n → Fin n × Fin n → Bool := fun p q =>
    decide (∃ x ∈ ({p.1, p.2} : Finset (Fin n)),
      ∃ y ∈ ({q.1, q.2} : Finset (Fin n)), G.Adj x y) with hrdef
  have hd : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (sig p) (sig q) := hdisj
  have hsig : ∀ p ∈ P, (sig p).card ≤ 2 := by
    intro p _
    have h1 : (sig p).card ≤ ({p.1, p.2} : Finset (Fin n)).card :=
      Finset.card_le_card (by rw [hsigdef]; exact Finset.sdiff_subset)
    exact h1.trans (le_trans (Finset.card_insert_le _ _) (by simp))
  have hpair : ∀ p ∈ P, ∀ x ∈ ({p.1, p.2} : Finset (Fin n)),
      ∀ y ∈ ({p.1, p.2} : Finset (Fin n)), ¬ G.Adj x y := fun p hp => pair_indep (hedge p hp)
  have hirr : ∀ p ∈ P, r p p = false := by
    intro p hp
    rw [hrdef]
    simp only [decide_eq_false_iff_not]
    rintro ⟨x, hx, y, hy, hxy⟩
    exact hpair p hp x hx y hy hxy
  have hsymm : ∀ p q, r p q = r q p := by
    intro p q
    rw [hrdef]
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨y, hy, x, hx, hxy.symm⟩
    · rintro ⟨y, hy, x, hx, hxy⟩
      exact ⟨x, hx, y, hy, hxy.symm⟩
  have main : ∀ Q : Finset (Fin n × Fin n), Q ⊆ P →
      (∀ p ∈ Q, ∀ q ∈ Q, r p q = true → ∃ x, x ∈ sig p ∧ ∃ y, y ∈ sig q ∧ G.Adj x y) →
      M ≤ Q.card →
      ∃ J : Finset (Fin n × Fin n), J ⊆ P ∧ (∀ p ∈ J, ∀ q ∈ J, r p q = false) ∧ k + 1 ≤ J.card := by
    intro Q hQ hwit hcard
    obtain ⟨Q', hQ'Q, hQ'card⟩ := Finset.exists_subset_card_eq hcard
    have hQ'P : Q' ⊆ P := fun z hz => hQ (hQ'Q hz)
    have hlow : ∀ Q'' ⊆ Q', Q''.Nonempty → ∃ p ∈ Q'', (Q''.filter fun q => r p q).card ≤ t - 1 := by
      intro Q'' hQ''Q' hNE
      have ht' : 16 * Q''.card < t ^ 2 := by
        have h1 := Finset.card_le_card hQ''Q'
        rw [hQ'card] at h1
        omega
      obtain ⟨p, hpQ, hlt⟩ := exists_low hg Q sig r
        (fun p hp q hq hne => hd p (hQ hp) q (hQ hq) hne)
        (fun p hp => hsig p (hQ hp)) hwit
        (hQ''Q'.trans hQ'Q) hNE ht'
      exact ⟨p, hpQ, Nat.le_sub_one_of_lt hlt⟩
    obtain ⟨J, hJQ', hJind, hJle⟩ :=
      greedy r (t - 1) Q'.card Q' rfl (fun p hp => hirr p (hQ'P hp)) hsymm hlow
    refine ⟨J, hJQ'.trans hQ'P, hJind, ?_⟩
    rw [Nat.sub_add_cancel htpos] at hJle
    have h1 : (k + 1) * t ≤ J.card * t := hMt.trans (hQ'card.ge.trans hJle)
    refine le_of_mul_le_mul_left ?_ htpos
    rw [Nat.mul_comm t (k + 1), Nat.mul_comm t J.card]
    exact h1
  set PA := P.filter fun p => a ∈ ({p.1, p.2} : Finset (Fin n)) ∧ sig p ≠ ∅ with hPA
  set PB := P.filter fun p =>
    a ∉ ({p.1, p.2} : Finset (Fin n)) ∧ b ∈ ({p.1, p.2} : Finset (Fin n)) ∧ sig p ≠ ∅ with hPB
  set PR := P.filter fun p =>
    a ∉ ({p.1, p.2} : Finset (Fin n)) ∧ b ∉ ({p.1, p.2} : Finset (Fin n)) ∧ sig p ≠ ∅ with hPR
  set P0 := P.filter fun p => sig p = ∅ with hP0
  have hcover : P ⊆ P0 ∪ (PA ∪ (PB ∪ PR)) := by
    intro p hp
    by_cases h0 : sig p = ∅
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h0⟩)
    · by_cases h1 : a ∈ ({p.1, p.2} : Finset (Fin n))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h1, h0⟩))
      · by_cases h2 : b ∈ ({p.1, p.2} : Finset (Fin n))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hp, h1, h2, h0⟩)))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hp, h1, h2, h0⟩)))
  have hab2 : ({a, b} : Finset (Fin n)).card ≤ 2 := by
    simpa using Finset.card_insert_le a ({b} : Finset (Fin n))
  have hP0le : P0.card ≤ 4 := by
    have hsub : P0 ⊆ ({a, b} : Finset (Fin n)) ×ˢ {a, b} := by
      intro p hp
      rw [hP0] at hp
      rcases Finset.mem_filter.mp hp with ⟨_, h0⟩
      have h2 : ({p.1, p.2} : Finset (Fin n)) ⊆ {a, b} := by
        rw [hsigdef] at h0
        exact Finset.sdiff_eq_empty_iff_subset.mp h0
      exact Finset.mem_product.mpr ⟨h2 (Finset.mem_insert_self _ _),
        h2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
    calc P0.card ≤ (({a, b} : Finset (Fin n)) ×ˢ {a, b}).card := Finset.card_le_card hsub
      _ = ({a, b} : Finset (Fin n)).card * ({a, b} : Finset (Fin n)).card := Finset.card_product _ _
      _ ≤ 2 * 2 := Nat.mul_le_mul hab2 hab2
      _ = 4 := by norm_num
  have hbig : M ≤ PA.card ∨ M ≤ PB.card ∨ M ≤ PR.card := by
    have h1 : P.card ≤ P0.card + PA.card + PB.card + PR.card := by
      calc P.card ≤ (P0 ∪ (PA ∪ (PB ∪ PR))).card := Finset.card_le_card hcover
        _ ≤ P0.card + (PA ∪ (PB ∪ PR)).card := Finset.card_union_le _ _
        _ ≤ P0.card + (PA.card + (PB ∪ PR).card) :=
          Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ ≤ P0.card + (PA.card + (PB.card + PR.card)) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Finset.card_union_le _ _) _) _
        _ = P0.card + PA.card + PB.card + PR.card := by ring
    by_contra hc
    push Not at hc
    omega
  have hJ : ∃ J : Finset (Fin n × Fin n), J ⊆ P ∧ (∀ p ∈ J, ∀ q ∈ J, r p q = false) ∧
      k + 1 ≤ J.card := by
    rcases hbig with h | h | h
    · refine main PA (Finset.filter_subset _ _) ?_ h
      intro p hp q hq hr
      rw [hPA] at hp hq
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpa, hnp⟩
      rcases Finset.mem_filter.mp hq with ⟨hqP, hqa, hnq⟩
      rw [hrdef] at hr
      simp only [decide_eq_true_iff] at hr
      simp only [hsigdef]
      exact wit_c (hedge p hpP) hpa (Finset.mem_insert_self a {b})
        (Finset.nonempty_of_ne_empty hnp) (hedge q hqP) hqa (Finset.mem_insert_self a {b})
        (Finset.nonempty_of_ne_empty hnq) hr
    · refine main PB (Finset.filter_subset _ _) ?_ h
      intro p hp q hq hr
      rw [hPB] at hp hq
      rcases Finset.mem_filter.mp hp with ⟨hpP, _, hpb, hnp⟩
      rcases Finset.mem_filter.mp hq with ⟨hqP, _, hqb, hnq⟩
      rw [hrdef] at hr
      simp only [decide_eq_true_iff] at hr
      simp only [hsigdef]
      exact wit_c (hedge p hpP) hpb (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
        (Finset.nonempty_of_ne_empty hnp) (hedge q hqP) hqb
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)) (Finset.nonempty_of_ne_empty hnq) hr
    · refine main PR (Finset.filter_subset _ _) ?_ h
      intro p hp q hq hr
      rw [hPR] at hp hq
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpa, hpb, _⟩
      rcases Finset.mem_filter.mp hq with ⟨hqP, hqa, hqb, _⟩
      rw [hrdef] at hr
      simp only [decide_eq_true_iff] at hr
      simp only [hsigdef]
      exact wit_r hpa hpb hqa hqb hr
  obtain ⟨J, hJP, hJind, hJcard⟩ := hJ
  set I : Finset (Fin n) := J.biUnion fun p => ({p.1, p.2} : Finset (Fin n)) with hI
  refine ⟨I, ?_, ?_⟩
  · intro x hx y hy
    rw [hI] at hx hy
    obtain ⟨p, hpJ, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨q, hqJ, hy⟩ := Finset.mem_biUnion.mp hy
    by_cases hpq : p = q
    · subst hpq
      exact hpair p (hJP hpJ) x hx y hy
    · have h := hJind p hpJ q hqJ
      rw [hrdef] at h
      simp only [decide_eq_false_iff_not] at h
      intro hxy
      exact h ⟨x, hx, y, hy, hxy⟩
  · intro S hS haS hbS
    by_contra hcon
    push Not at hcon
    have hin : ∀ p ∈ J, p.1 ∈ I ∧ p.2 ∈ I := by
      intro p hpJ
      rw [hI]
      exact ⟨Finset.mem_biUnion.mpr ⟨p, hpJ, Finset.mem_insert_self _ _⟩,
        Finset.mem_biUnion.mpr ⟨p, hpJ, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩⟩
    have hmap : ∀ p ∈ J, (if p.1 ∈ S then p.1 else p.2) ∈ S ∧
        (if p.1 ∈ S then p.1 else p.2) ∈ sig p := by
      intro p hpJ
      by_cases h1 : p.1 ∈ S
      · have hf : (if p.1 ∈ S then p.1 else p.2) ∈ S := by simp [h1]
        have hm : (if p.1 ∈ S then p.1 else p.2) ∈ sig p := by
          simp only [h1, ite_true, hsigdef]
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, ?_⟩
          intro c
          rcases mem_pair' c with c | c
          · exact haS (c ▸ h1)
          · exact hbS (c ▸ h1)
        exact ⟨hf, hm⟩
      · have h2 : p.2 ∈ S := by
          by_contra h2c
          obtain ⟨hm1, hm2⟩ := hin p hpJ
          exact hcon p (hJP hpJ) (Finset.mem_sdiff.mpr ⟨hm1, h1⟩) (Finset.mem_sdiff.mpr ⟨hm2, h2c⟩)
        have hf : (if p.1 ∈ S then p.1 else p.2) ∈ S := by simp [h1, h2]
        have hm : (if p.1 ∈ S then p.1 else p.2) ∈ sig p := by
          simp only [h1, ite_false, hsigdef]
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          intro c
          rcases mem_pair' c with c | c
          · exact haS (c ▸ h2)
          · exact hbS (c ▸ h2)
        exact ⟨hf, hm⟩
    have hinj : ∀ p ∈ J, ∀ q ∈ J,
        (if p.1 ∈ S then p.1 else p.2) = (if q.1 ∈ S then q.1 else q.2) → p = q := by
      intro p hpJ q hqJ he
      by_contra hne
      exact Finset.disjoint_left.mp (hd p (hJP hpJ) q (hJP hqJ) hne) (he ▸ (hmap p hpJ).2)
        (hmap q hqJ).2
    have hle := Finset.card_le_card_of_injOn (fun p => if p.1 ∈ S then p.1 else p.2)
      (fun p hp => (hmap p (Finset.mem_coe.mp hp)).1)
      (fun p hp q hq he => hinj p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) he)
    omega
