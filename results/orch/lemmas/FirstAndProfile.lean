import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.SingletonProfile

def HasEdge {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

def SignalMono {V : Type*} (s : Set V → Prop) : Prop :=
  ∀ ⦃X Y : Set V⦄, X ⊆ Y → s X → s Y

def ContextMono {V : Type*} (K : Set V → Prop → Prop) : Prop :=
  ∀ ⦃X Y : Set V⦄ ⦃p q : Prop⦄, X ⊆ Y → (p → q) → K X p → K Y q

def Exact {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (s : Set V → Prop) : Prop :=
  ∀ X, K X (s X) ↔ HasEdge G X

def Pivotal {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (u v : V) : Prop :=
  G.Adj u v ∧ ¬ K {u, v} False

def Required {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (X : Set V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, Pivotal G K u v

def Permitted {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (X : Set V) : Prop :=
  ∀ I, X ⊆ I → ¬ HasEdge G I → ¬ K I True

lemma hasEdge_mono {V : Type*} (G : SimpleGraph V) : SignalMono (HasEdge G) := by
  rintro X Y hXY ⟨u, hu, v, hv, he⟩
  exact ⟨u, hXY hu, v, hXY hv, he⟩

lemma hasEdge_pair {V : Type*} (G : SimpleGraph V) {u v : V} (he : G.Adj u v) :
    HasEdge G {u, v} :=
  ⟨u, by simp, v, by simp, he⟩

lemma required_mono {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop) :
    SignalMono (Required G K) := by
  rintro X Y hXY ⟨u, hu, v, hv, he⟩
  exact ⟨u, hXY hu, v, hXY hv, he⟩

lemma permitted_mono {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop) :
    SignalMono (Permitted G K) := by
  intro X Y hXY hX I hYI
  exact hX I (hXY.trans hYI)

lemma pivotal_requires {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s : Set V → Prop} (hK : ContextMono K) (hs : Exact G K s)
    {u v : V} (he : Pivotal G K u v) : s {u, v} := by
  by_contra hn
  exact he.2 (hK (Set.Subset.rfl) hn ((hs _).2 (hasEdge_pair G he.1)))

lemma exact_iff_interval {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s h : Set V → Prop} (hK : ContextMono K) (hs : Exact G K s)
    (hm : SignalMono h) :
    Exact G K h ↔ (∀ X, Required G K X → h X) ∧
      (∀ X, h X → Permitted G K X) := by
  classical
  constructor
  · intro hh
    constructor
    · rintro X ⟨u, hu, v, hv, he⟩
      exact hm (Set.pair_subset hu hv) (pivotal_requires hK hh he)
    · intro X hx I hXI hi hk
      exact hi ((hh I).1 (hK Set.Subset.rfl (fun _ => hm hXI hx) hk))
  · rintro ⟨hreq, hperm⟩ X
    constructor
    · intro hval
      by_contra hi
      by_cases hx : h X
      · exact hperm X hx X Set.Subset.rfl hi (hK Set.Subset.rfl (fun _ => trivial) hval)
      · exact hi ((hs X).1 (hK Set.Subset.rfl (fun h' => (hx h').elim) hval))
    · rintro ⟨u, hu, v, hv, he⟩
      have hsub : {u, v} ⊆ X := Set.pair_subset hu hv
      by_cases h0 : K {u, v} False
      · exact hK hsub False.elim h0
      · have h1 : h X := hreq X ⟨u, hu, v, hv, he, h0⟩
        exact hK hsub (fun _ => h1) ((hs _).2 (hasEdge_pair G he))

lemma required_sound {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    {X : Set V} (hX : Required G K X) : HasEdge G X := by
  obtain ⟨u, hu, v, hv, he⟩ := hX
  exact ⟨u, hu, v, hv, he.1⟩

lemma sound_pivotal_substitution {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {s h : Set V → Prop}
    (hK : ContextMono K) (hs : Exact G K s) (hm : SignalMono h)
    (hsound : ∀ X, h X → HasEdge G X)
    (hp : ∀ u v, Pivotal G K u v → h {u, v}) : Exact G K h := by
  apply (exact_iff_interval hK hs hm).2
  constructor
  · rintro X ⟨u, hu, v, hv, he⟩
    exact hm (Set.pair_subset hu hv) (hp u v he)
  · intro X hx I hXI hi
    exact (hi (hsound I (hm hXI hx))).elim

lemma least_signal_exact {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s : Set V → Prop} (hK : ContextMono K) (hs : Exact G K s) :
    Exact G K (Required G K) := by
  apply sound_pivotal_substitution hK hs (required_mono G K) (fun _ => required_sound G K)
  intro u v he
  exact ⟨u, by simp, v, by simp, he⟩

lemma greatest_signal_exact {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s : Set V → Prop} (hK : ContextMono K) (hs : Exact G K s) :
    Exact G K (Permitted G K) := by
  exact (exact_iff_interval hK hs (permitted_mono G K)).2
    ⟨((exact_iff_interval hK hs (required_mono G K)).1 (least_signal_exact hK hs)).2,
     fun _ h => h⟩

lemma narrow_on_pivotal {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s h : Set V → Prop} (hK : ContextMono K) (hs : Exact G K s) (hm : SignalMono h)
    (hbelow : ∀ X, h X → s X) (hp : ∀ u v, Pivotal G K u v → h {u, v}) :
    Exact G K h := by
  apply (exact_iff_interval hK hs hm).2
  constructor
  · rintro X ⟨u, hu, v, hv, he⟩
    exact hm (Set.pair_subset hu hv) (hp u v he)
  · intro X hx I hXI hi hK1
    exact hi ((hs I).1 (hK Set.Subset.rfl (fun _ => hbelow I (hm hXI hx)) hK1))

lemma singleton_forces_center {V : Type*} (G : SimpleGraph V) (s : Set V → Prop)
    (hm : SignalMono s) {c v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hsv : s {v})
    (hstar : ∀ u w, G.Adj u w → s {u, w} → u = c ∨ w = c) : c = v := by
  by_cases hvc : v = c
  · exact hvc.symm
  have hsa : s {v, a} := hm (Set.singleton_subset_iff.mpr (by simp)) hsv
  have hsb : s {v, b} := hm (Set.singleton_subset_iff.mpr (by simp)) hsv
  have hac : a = c := (hstar v a hva hsa).resolve_left hvc
  have hbc : b = c := (hstar v b hvb hsb).resolve_left hvc
  exact (hab (hac.trans hbc.symm)).elim

lemma singleton_literal_repair {V : Type*} (G : SimpleGraph V)
    (K : Set V → Prop → Prop) (s : Set V → Prop)
    (hK : ContextMono K) (hm : SignalMono s) (hex : Exact G K s)
    {c v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (hsv : s {v}) (hstar : ∀ u w, G.Adj u w → s {u, w} → u = c ∨ w = c) :
    Exact G K (fun X => v ∈ X) := by
  have hcv := singleton_forces_center G s hm hva hvb hab hsv hstar
  subst c
  apply narrow_on_pivotal hK hex
  · intro X Y hXY hv
    exact hXY hv
  · intro X hv
    exact hm (Set.singleton_subset_iff.mpr hv) hsv
  · intro u w he
    have hu := hstar u w he.1 (pivotal_requires hK hex he)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using hu

lemma min_degree_two_singleton_repair {V : Type*} (G : SimpleGraph V)
    (K : Set V → Prop → Prop) (s : Set V → Prop)
    (hK : ContextMono K) (hm : SignalMono s) (hex : Exact G K s)
    (hdeg : ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b)
    (hstar : ∃ c, ∀ u w, G.Adj u w → s {u, w} → u = c ∨ w = c)
    (hsingle : ∃ v, s {v}) : ∃ v, Exact G K (fun X => v ∈ X) := by
  obtain ⟨v, hv⟩ := hsingle
  obtain ⟨a, b, hva, hvb, hab⟩ := hdeg v
  obtain ⟨c, hc⟩ := hstar
  exact ⟨v, singleton_literal_repair G K s hK hm hex hva hvb hab hv hc⟩

end PEqualNP.Outside.L_meta_1031.SingletonProfile

namespace PEqualNP.Outside.L_meta_1031.FirstAndProfile

open PEqualNP.Outside.L_meta_1031.SingletonProfile

def Hits {V : Type*} (A X : Set V) : Prop := ∃ a ∈ A, a ∈ X

lemma hits_pair {V : Type*} (A : Set V) (u v : V) : Hits A {u, v} ↔ u ∈ A ∨ v ∈ A := by
  simp only [Hits, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl | rfl⟩
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma singleton_clean_disjoint {V : Type*} (A B : Set V)
    (hclean : ∀ v, ¬ (Hits A {v} ∧ Hits B {v})) : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro v ha hb
  exact hclean v ⟨⟨v, ha, by simp⟩, ⟨v, hb, by simp⟩⟩

lemma center_in_operands {V : Type*} (G : SimpleGraph V) (A B : Set V) (c : V)
    (hdisj : Disjoint A B)
    (hne : ∃ u v, G.Adj u v ∧ Hits A {u, v} ∧ Hits B {u, v})
    (hstar : ∀ u v, G.Adj u v → Hits A {u, v} ∧ Hits B {u, v} → u = c ∨ v = c) :
    c ∈ A ∨ c ∈ B := by
  classical
  by_contra! hn
  obtain ⟨u, v, huv, hA, hB⟩ := hne
  rcases hstar u v huv ⟨hA, hB⟩ with rfl | rfl
  · have hvA := ((hits_pair A _ _).mp hA).resolve_left hn.1
    have hvB := ((hits_pair B _ _).mp hB).resolve_left hn.2
    exact Set.disjoint_left.mp hdisj hvA hvB
  · have huA := ((hits_pair A _ _).mp hA).resolve_right hn.1
    have huB := ((hits_pair B _ _).mp hB).resolve_right hn.2
    exact Set.disjoint_left.mp hdisj huA huB

lemma literal_guard_normalization {V : Type*} (G : SimpleGraph V)
    (K : Set V → Prop → Prop) (A B : Set V) (c : V)
    (hK : ContextMono K) (hex : Exact G K (fun X => Hits A X ∧ Hits B X))
    (hc : c ∈ A)
    (hstar : ∀ u v, G.Adj u v → Hits A {u, v} ∧ Hits B {u, v} → u = c ∨ v = c) :
    Exact G K (fun X => c ∈ X ∧ Hits B X) ∧
      (∀ X, c ∈ X ∧ Hits B X → Hits A X ∧ Hits B X) ∧
      ∀ u v, G.Adj u v →
        (Hits A {u, v} ∧ Hits B {u, v} ↔ c ∈ ({u, v} : Set V) ∧ Hits B {u, v}) := by
  have hbelow (X : Set V) (h : c ∈ X ∧ Hits B X) : Hits A X ∧ Hits B X :=
    ⟨⟨c, hc, h.1⟩, h.2⟩
  have hpairs (u v) (huv : G.Adj u v) :
      Hits A {u, v} ∧ Hits B {u, v} ↔ c ∈ ({u, v} : Set V) ∧ Hits B {u, v} := by
    constructor
    · intro h
      have hcpair : c ∈ ({u, v} : Set V) := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using hstar u v huv h
      exact ⟨hcpair, h.2⟩
    · exact hbelow _
  refine ⟨?_, hbelow, hpairs⟩
  apply narrow_on_pivotal hK hex
  · rintro X Y hXY ⟨hcX, b, hb, hbX⟩
    exact ⟨hXY hcX, b, hb, hXY hbX⟩
  · exact hbelow
  · intro u v he
    exact (hpairs u v he.1).mp (pivotal_requires hK hex he)

lemma first_star_literal_normal_form {V : Type*} (G : SimpleGraph V)
    (K : Set V → Prop → Prop) (A B : Set V) (c : V)
    (hK : ContextMono K) (hex : Exact G K (fun X => Hits A X ∧ Hits B X))
    (hclean : ∀ v, ¬ (Hits A {v} ∧ Hits B {v}))
    (hne : ∃ u v, G.Adj u v ∧ Hits A {u, v} ∧ Hits B {u, v})
    (hstar : ∀ u v, G.Adj u v → Hits A {u, v} ∧ Hits B {u, v} → u = c ∨ v = c) :
    (c ∈ A ∧ Exact G K (fun X => c ∈ X ∧ Hits B X)) ∨
      (c ∈ B ∧ Exact G K (fun X => c ∈ X ∧ Hits A X)) := by
  rcases center_in_operands G A B c (singleton_clean_disjoint A B hclean) hne hstar with ha | hb
  · exact Or.inl ⟨ha, (literal_guard_normalization G K A B c hK hex ha hstar).1⟩
  · have hex' : Exact G K (fun X => Hits B X ∧ Hits A X) := by
      simpa only [and_comm] using hex
    have hstar' : ∀ u v, G.Adj u v → Hits B {u, v} ∧ Hits A {u, v} → u = c ∨ v = c :=
      fun u v huv h => hstar u v huv h.symm
    exact Or.inr ⟨hb, (literal_guard_normalization G K B A c hK hex' hb hstar').1⟩

end PEqualNP.Outside.L_meta_1031.FirstAndProfile
