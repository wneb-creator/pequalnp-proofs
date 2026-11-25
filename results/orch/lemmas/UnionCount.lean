import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace PEqualNP.Outside.L_meta_2585_aux.UnionCount

def Good {m n : ℕ} (R : Fin m → Fin n → Prop) (g : ℕ) (T : ℕ → Finset (Fin n)) (c : Fin m) (u : Fin n) (j : ℕ) : Prop :=
  j < g ∧ (∀ t ∈ (T (n + j) : Finset (Fin n)), R c t) ∧
    u ∈ (T (n + j) : Finset (Fin n)) ∧ ∃ u0 ∈ (T (n + j) : Finset (Fin n)), u0 < u

lemma no_below {m n : ℕ} (R : Fin m → Fin n → Prop) (g : ℕ) (T : ℕ → Finset (Fin n))
    (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩}) (c : Fin m) (u : Fin n) (j a : ℕ)
    (hj : j < g) (ha : a < n + j)
    (hadj : ∀ t ∈ (T a : Finset (Fin n)), R c t) (hu : u ∈ (T a : Finset (Fin n)))
    (hmin : ∀ j', j' < j → ¬ Good R g T c u j') : ∀ t ∈ (T a : Finset (Fin n)), ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [hinput a han, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j', rfl⟩ : ∃ j', a = n + j' := ⟨a - n, by omega⟩
    exact hmin j' (by omega) ⟨by omega, hadj, hu, t, ht, hlt⟩

lemma no_lt_aux {m n : ℕ} (R : Fin m → Fin n → Prop) (g : ℕ) (T : ℕ → Finset (Fin n))
    (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩}) (c : Fin m) (u u' : Fin n) (j a b : ℕ)
    (hj : j < g) (ha : a < n + j) (hb : b < n + j)
    (hT : (T (n + j) : Finset (Fin n)) = T a ∪ T b)
    (hg : Good R g T c u j)
    (hmin : ∀ j', j' < j → ¬ Good R g T c u j') (hmin' : ∀ j', j' < j → ¬ Good R g T c u' j')
    (hlt : u < u') (hu'a : u' ∈ (T a : Finset (Fin n))) : False := by
  obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
  have hadja : ∀ t ∈ (T a : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_left _ ht)
  have hadjb : ∀ t ∈ (T b : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_right _ ht)
  have h1 := no_below R g T hinput c u' j a hj ha hadja hu'a hmin'
  rw [hT, Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below R g T hinput c u j b hj hb hadjb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

lemma no_lt {m n : ℕ} (R : Fin m → Fin n → Prop) (g : ℕ) (T : ℕ → Finset (Fin n)) (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩})
    (hgate : ∀ j < g, ∃ a b, a < n + j ∧ b < n + j ∧ T (n + j) = T a ∪ T b)
    (c : Fin m) (u u' : Fin n) (j : ℕ) (hg : Good R g T c u j) (hg' : Good R g T c u' j)
    (hmin : ∀ j', j' < j → ¬ Good R g T c u j') (hmin' : ∀ j', j' < j → ¬ Good R g T c u' j')
    (hlt : u < u') : False := by
  have hj := hg.1
  obtain ⟨a, b, ha, hb, hT⟩ := hgate j hj
  have hu' := hg'.2.2.1
  rw [hT, Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux R g T hinput c u u' j a b hj ha hb hT hg hmin hmin' hlt h
  · exact no_lt_aux R g T hinput c u u' j b a hj hb ha (by rw [hT, Finset.union_comm]) hg hmin hmin' hlt h

lemma inj_core {m n : ℕ} (R : Fin m → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (g : ℕ) (T : ℕ → Finset (Fin n)) (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩})
    (hgate : ∀ j < g, ∃ a b, a < n + j ∧ b < n + j ∧ T (n + j) = T a ∪ T b)
    (c : Fin m) (u : Fin n) (c' : Fin m) (u' : Fin n) (j : ℕ) (hg : Good R g T c u j) (hg' : Good R g T c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good R g T c u j') (hmin' : ∀ j', j' < j → ¬ Good R g T c' u' j') :
    c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
    exact hN u0 u (ne_of_lt hu0lt) c c' (hadj u0 hu0) (hadj u hu) (hg'.2.1 u0 hu0) (hg'.2.1 u hu)
  subst hcc
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt R g T hinput hgate c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt R g T hinput hgate c u' u j hg' hg hmin' hmin h).elim

lemma leaf_min {m n : ℕ} (R : Fin m → Fin n → Prop) (g : ℕ) (T : ℕ → Finset (Fin n))
    (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩}) (L : Finset (Fin n))
    (hS : ∃ w < n + g, T w = L) (c : Fin m) (u : Fin n)
    (hadj : ∀ t ∈ L, R c t) (hu : u ∈ L)
    (hng : ¬ ∃ j, Good R g T c u j) : ∀ t ∈ L, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w, hw, hcomp⟩ := hS
  have hT := hcomp
  by_cases hwn : w < n
  · rw [← hT, hinput w hwn, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    exact hng ⟨j, by omega, by rw [hT]; exact hadj, by rw [hT]; exact hu, t,
      by rw [hT]; exact ht, hlt⟩

lemma card_le_of_unique_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, Set.Subsingleton {a | a ∈ s ∧ r a b}) : s.card ≤ t.card := by
  classical
  let f : s → β := fun a => Classical.choose (hs a.1 a.2)
  have hf (a : s) : f a ∈ t ∧ r a.1 (f a) := Classical.choose_spec (hs a.1 a.2)
  let g : s → t := fun a => ⟨f a, (hf a).1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro a a' heq
  have heq' : f a = f a' := congrArg Subtype.val heq
  apply Subtype.ext
  exact ht (f a) (hf a).1 ⟨a.2, (hf a).2⟩ ⟨a'.2, heq'.symm ▸ (hf a').2⟩

lemma count_gen {m n : ℕ} (R : Fin m → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (g : ℕ) (T : ℕ → Finset (Fin n)) (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩})
    (hgate : ∀ j < g, ∃ a b, a < n + j ∧ b < n + j ∧ T (n + j) = T a ∪ T b)
    (K : Finset (Fin m × Finset (Fin n)))
    (hK : ∀ k ∈ K, (∃ w < n + g, T w = k.2) ∧ ∀ t ∈ k.2, R k.1 t)
    (P : Finset (Σ _ : Fin m, Fin n))
    (hP : ∀ q ∈ P, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2) :
    P.card ≤ g + K.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good R g T q.1 q.2 j).card ≤ g := by
    conv_rhs => rw [← Finset.card_range g]
    refine card_le_of_unique_fibers
      (fun q j => Good R g T q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good R g T q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      exact Finset.mem_range.2 (Nat.find_spec hex).1
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core R hN g T hinput hgate c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good R g T q.1 q.2 j).card ≤ K.card := by
    refine card_le_of_unique_fibers
      (fun q k => k.1 = q.1 ∧ q.2 ∈ k.2) ?_ ?_
    · intro q hq
      exact hP q (Finset.mem_filter.1 hq).1
    · intro k hk q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨hq1, hqc, hqu⟩ := hq
      obtain ⟨hq1', hqc', hqu'⟩ := hq'
      have hcc : c = c' := hqc.symm.trans hqc'
      subst hcc
      obtain ⟨hcomp, hadj⟩ := hK k hk
      rw [hqc] at hadj
      have h1 := leaf_min R g T hinput k.2 hcomp c u hadj hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min R g T hinput k.2 hcomp c u' hadj hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good R g T q.1 q.2 j)
  omega

lemma linear_family_bound {m n g : ℕ} (T : ℕ → Finset (Fin n))
    (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩})
    (hgate : ∀ j < g, ∃ a b, a < n + j ∧ b < n + j ∧ T (n + j) = T a ∪ T b)
    (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hserve : ∀ p, (S p).Nonempty → ∃ w < n + g, T w = S p) :
    (∑ p : Fin m, (S p).card) ≤ g + (Finset.univ.filter fun p => (S p).Nonempty).card := by
  classical
  let R : Fin m → Fin n → Prop := fun p u => u ∈ S p
  have hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ p q : Fin m,
      R p u0 → R p u → R q u0 → R q u → p = q := by
    intro u0 u hne p q hp0 hpu hq0 hqu
    by_contra hpq
    have hs : ({u0, u} : Finset (Fin n)) ⊆ S p ∩ S q := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hp0, hq0⟩
      · exact Finset.mem_inter.mpr ⟨hpu, hqu⟩
    have hc : ({u0, u} : Finset (Fin n)).card = 2 := by simp [hne]
    have hle := Finset.card_le_card hs
    have hsmall := hlin p q hpq
    omega
  let A : Finset (Fin m) := Finset.univ.filter fun p => (S p).Nonempty
  let K : Finset (Fin m × Finset (Fin n)) := A.image fun p => (p, S p)
  let I : Finset (Σ _ : Fin m, Fin n) := Finset.univ.sigma S
  have hK : ∀ k ∈ K,
      (∃ w < n + g, T w = k.2) ∧ ∀ t ∈ k.2, R k.1 t := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨hserve p (Finset.mem_filter.mp hp).2, fun _ ht => ht⟩
  have hP : ∀ q ∈ I, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2 := by
    intro q hq
    refine ⟨(q.1, S q.1), ?_, rfl, (Finset.mem_sigma.mp hq).2⟩
    exact Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨q.2, (Finset.mem_sigma.mp hq).2⟩⟩, rfl⟩
  have hbound := count_gen R hN g T hinput hgate K hK I hP
  have hKcard : K.card ≤ A.card := Finset.card_image_le
  dsimp [A] at hKcard
  have hIcard : I.card = ∑ p : Fin m, (S p).card := Finset.card_sigma _ _
  omega

lemma linear_family_cost {m n g : ℕ} (T : ℕ → Finset (Fin n))
    (hinput : ∀ w (hw : w < n), T w = {⟨w, hw⟩})
    (hgate : ∀ j < g, ∃ a b, a < n + j ∧ b < n + j ∧ T (n + j) = T a ∪ T b)
    (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hserve : ∀ p, (S p).Nonempty → ∃ w < n + g, T w = S p) :
    (∑ p : Fin m, ((S p).card - 1)) ≤ g := by
  classical
  have hcard (p : Fin m) :
      (S p).card = ((S p).card - 1) + if (S p).Nonempty then 1 else 0 := by
    by_cases hp : (S p).Nonempty
    · have hpos := Finset.card_pos.mpr hp
      simp only [ite_eq_left hp]
      omega
    · have hempty : S p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      simp [hempty]
  have hsum : (∑ p : Fin m, (S p).card) =
      (∑ p : Fin m, ((S p).card - 1)) +
        (Finset.univ.filter fun p => (S p).Nonempty).card := by
    calc
      (∑ p : Fin m, (S p).card) =
          ∑ p : Fin m, (((S p).card - 1) + if (S p).Nonempty then 1 else 0) :=
        Finset.sum_congr rfl (fun p _ => hcard p)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  have hb := linear_family_bound T hinput hgate S hlin hserve
  omega

end PEqualNP.Outside.L_meta_2585_aux.UnionCount
