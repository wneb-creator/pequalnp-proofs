import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshCore

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

def Hits {V : Type*} (A X : Set V) : Prop := ∃ a ∈ A, a ∈ X

lemma hits_mono {V : Type*} (A : Set V) : SignalMono (Hits A) := by
  rintro X Y hXY ⟨a, ha, hx⟩
  exact ⟨a, ha, hXY hx⟩

lemma hits_pair {V : Type*} (A : Set V) (u v : V) : Hits A {u, v} ↔ u ∈ A ∨ v ∈ A := by
  constructor
  · rintro ⟨a, ha, h⟩
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr ((Set.mem_singleton_iff.mp h) ▸ ha)
  · rintro (hu | hv)
    · exact ⟨u, hu, by simp⟩
    · exact ⟨v, hv, by simp⟩

lemma center_rewire {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {A B : Set V → Prop} {c : V} (hK : ContextMono K)
    (hold : Exact G K (fun X => A X ∧ B X)) (hB : SignalMono B)
    (hdom : ∀ X, c ∈ X → A X)
    (hstar : ∀ u v, Pivotal G K u v → u = c ∨ v = c) :
    Exact G K (fun X => c ∈ X ∧ B X) := by
  apply narrow_on_pivotal hK hold
  · intro X Y hXY h
    exact ⟨hXY h.1, hB hXY h.2⟩
  · intro X h
    exact ⟨hdom X h.1, h.2⟩
  · intro u v he
    refine ⟨?_, (pivotal_requires hK hold he).2⟩
    rcases hstar u v he with rfl | rfl <;> simp

lemma external_pivotal_center {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {A B : Set V} {c : V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X)) (ha : c ∉ A) (hb : c ∉ B)
    (hstar : ∀ u v, Pivotal G K u v → u = c ∨ v = c) :
    Exact G K (Hits (A ∩ B)) := by
  apply narrow_on_pivotal hK hold (hits_mono _)
  · rintro X ⟨a, hAB, hX⟩
    exact ⟨⟨a, hAB.1, hX⟩, ⟨a, hAB.2, hX⟩⟩
  · intro u v he
    have h := pivotal_requires hK hold he
    have hA := (hits_pair A u v).1 h.1
    have hB := (hits_pair B u v).1 h.2
    apply (hits_pair _ u v).2
    rcases hstar u v he with rfl | rfl
    · exact Or.inr ⟨hA.resolve_left ha, hB.resolve_left hb⟩
    · exact Or.inl ⟨hA.resolve_right ha, hB.resolve_right hb⟩

lemma cofactor_decomposition {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s : Set V → Prop} (hK : ContextMono K) (hold : Exact G K s) (X : Set V) :
    HasEdge G X ↔ K X False ∨ Required G K X := by
  classical
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    by_cases hp : K {u, v} False
    · exact Or.inl (hK (Set.pair_subset hu hv) id hp)
    · exact Or.inr ⟨u, hu, v, hv, he, hp⟩
  · rintro (h | h)
    · exact (hold X).1 (hK Set.Subset.rfl False.elim h)
    · exact required_sound G K h

def Undominated {V : Type*} (G : SimpleGraph V) (I : Set V) (v : V) : Prop :=
  ∀ w ∈ I, ¬ G.Adj v w

lemma edge_extension {V : Type*} {G : SimpleGraph V} {I : Set V} {a b : V}
    (hi : ¬ HasEdge G I) (ha : Undominated G I a) (hb : Undominated G I b)
    (h : HasEdge G (insert a (insert b I))) : G.Adj a b := by
  obtain ⟨x, hx, y, hy, he⟩ := h
  simp only [Set.mem_insert_iff] at hx hy
  rcases hx with rfl | rfl | hx
  · rcases hy with rfl | rfl | hy
    · exact (he.ne rfl).elim
    · exact he
    · exact (ha _ hy he).elim
  · rcases hy with rfl | rfl | hy
    · exact he.symm
    · exact (he.ne rfl).elim
    · exact (hb _ hy he).elim
  · rcases hy with rfl | rfl | hy
    · exact (ha _ hx he.symm).elim
    · exact (hb _ hx he.symm).elim
    · exact (hi ⟨_, hx, _, hy, he⟩).elim

lemma critical_independent_biclique {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {A B I : Set V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X))
    (hi : ¬ HasEdge G I) (hk : K I True)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hua : Undominated G I a) (hub : Undominated G I b) : G.Adj a b := by
  apply edge_extension hi hua hub
  apply (hold _).1
  apply hK (Y := insert a (insert b I)) (Set.Subset.trans (Set.subset_insert _ _)
      (Set.subset_insert _ _)) _ hk
  exact fun _ => ⟨⟨a, ha, by simp⟩, ⟨b, hb, by simp⟩⟩

lemma residual_side_subsingleton {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {A B I : Set V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hi : ¬ HasEdge G I) (hk : K I True) :
    (A ∩ {a | Undominated G I a}).Subsingleton ∨
      (B ∩ {b | Undominated G I b}).Subsingleton := by
  classical
  by_cases hA : (A ∩ {a | Undominated G I a}).Subsingleton
  · exact Or.inl hA
  · right
    unfold Set.Subsingleton at hA
    push Not at hA
    obtain ⟨a, ha, c, hc, hac⟩ := hA
    intro b hb d hd
    have cross (x) (hx : x ∈ A ∩ {v | Undominated G I v})
        (y) (hy : y ∈ B ∩ {v | Undominated G I v}) : G.Adj x y :=
      critical_independent_biclique hK hold hi hk hx.1 hy.1 hx.2 hy.2
    exact (hfour a b c d (cross a ha b hb) (cross c hc b hb).symm
      (cross c hc d hd) (cross a ha d hd).symm).resolve_left hac

lemma independent_pivot_dominates {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {A B I : Set V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X))
    (hi : ¬ HasEdge G I) (hk : K I True) (hit : Hits A I) :
    ∀ b ∈ B, ∃ i ∈ I, G.Adj b i := by
  classical
  obtain ⟨a, ha, haI⟩ := hit
  intro b hb
  by_contra hn
  push Not at hn
  have hUA : Undominated G I a := fun i hiI hai => hi ⟨a, haI, i, hiI, hai⟩
  have h := critical_independent_biclique hK hold hi hk ha hb hUA hn
  exact hn a haI h.symm

lemma failed_bypass_certificate {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {A B : Set V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X))
    (hbad : ¬ Exact G K (Hits A)) :
    ∃ I, ¬ HasEdge G I ∧ K I True ∧ Hits A I ∧ ¬ Hits B I ∧
      ∀ b ∈ B, ∃ i ∈ I, G.Adj b i := by
  classical
  by_contra! hn
  apply hbad
  intro X
  constructor
  · intro h
    by_contra he
    have ha : Hits A X := by
      by_contra hna
      exact he ((hold X).1 (hK Set.Subset.rfl (fun a => (hna a).elim) h))
    have hk : K X True := hK Set.Subset.rfl (fun _ => trivial) h
    have hb : ¬ Hits B X := by
      intro hb
      exact he ((hold X).1 (hK Set.Subset.rfl (fun _ => ⟨ha, hb⟩) h))
    obtain ⟨b, hbB, hbi⟩ := hn X he hk ha hb
    obtain ⟨i, hi, hAdj⟩ := independent_pivot_dominates hK hold he hk ha b hbB
    exact hbi i hi hAdj
  · intro he
    exact hK Set.Subset.rfl And.left ((hold X).2 he)

lemma intersecting_edges_star {α : Type*} (G : SimpleGraph α) (r : α → α → Prop)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hedge : ∀ u v, r u v → G.Adj u v)
    (hne : ∃ a b, r a b)
    (hmeet : ∀ u v p q, r u v → r p q → u = p ∨ u = q ∨ v = p ∨ v = q) :
    ∃ c, ∀ u v, r u v → u = c ∨ v = c := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  by_cases ha : ∀ u v, r u v → u = a ∨ v = a
  · exact ⟨a, ha⟩
  · push Not at ha
    obtain ⟨p, q, hpq, hpa, hqa⟩ := ha
    have hbpq : p = b ∨ q = b := by
      have h := hmeet p q a b hpq hab
      tauto
    have hext : ∃ w, w ≠ a ∧ G.Adj b w ∧
        ∀ u v, r u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
      rcases hbpq with rfl | rfl
      · refine ⟨q, hqa, hedge p q hpq, ?_⟩
        intro u v huv
        have h := hmeet u v p q huv hpq
        tauto
      · refine ⟨p, hpa, (hedge p q hpq).symm, ?_⟩
        intro u v huv
        have h := hmeet u v p q huv hpq
        tauto
    obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
    refine ⟨b, ?_⟩
    intro u v huv
    by_contra hn
    push Not at hn
    have huva : u = a ∨ v = a := by
      have h := hmeet u v a b huv hab
      tauto
    have huvw : u = w ∨ v = w := by
      have h := hmeetw u v huv
      tauto
    have hwaAdj : G.Adj w a := by
      rcases huva with h | h
      · subst u
        have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
        simpa [hvw] using (hedge a v huv).symm
      · subst v
        have huw : u = w := huvw.resolve_right (Ne.symm hwa)
        simpa [huw] using hedge u a huv
    exact htri a b w (hedge a b hab) hbw hwaAdj

lemma nonstar_has_disjoint_edges {α : Type*} (G : SimpleGraph α) (r : α → α → Prop)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hedge : ∀ u v, r u v → G.Adj u v)
    (hne : ∃ a b, r a b)
    (hnostar : ¬ ∃ c, ∀ u v, r u v → u = c ∨ v = c) :
    ∃ u v p q, r u v ∧ r p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q := by
  classical
  by_contra h
  apply hnostar
  apply intersecting_edges_star G r htri hedge hne
  intro u v p q huv hpq
  by_contra hd
  push Not at hd
  exact h ⟨u, v, p, q, huv, hpq, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩

lemma pivotal_repair_cases {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {A B : Set V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hne : ∃ u v, Pivotal G K u v) :
    (∃ u v p q, Pivotal G K u v ∧ Pivotal G K p q ∧
      u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q) ∨
    ∃ c, (∀ u v, Pivotal G K u v → u = c ∨ v = c) ∧
      ((c ∈ A ∧ Exact G K (fun X => c ∈ X ∧ Hits B X)) ∨
       (c ∈ B ∧ Exact G K (fun X => c ∈ X ∧ Hits A X)) ∨
       (c ∉ A ∧ c ∉ B ∧ Exact G K (Hits (A ∩ B)))) := by
  classical
  by_cases h : ∃ c, ∀ u v, Pivotal G K u v → u = c ∨ v = c
  · obtain ⟨c, hc⟩ := h
    refine Or.inr ⟨c, hc, ?_⟩
    by_cases ha : c ∈ A
    · exact Or.inl ⟨ha, center_rewire hK hold (hits_mono B) (fun X hx => ⟨c, ha, hx⟩) hc⟩
    by_cases hb : c ∈ B
    · have hr : Exact G K (fun X => Hits B X ∧ Hits A X) := by
        simpa only [and_comm] using hold
      exact Or.inr (Or.inl ⟨hb, center_rewire hK hr (hits_mono A) (fun X hx => ⟨c, hb, hx⟩) hc⟩)
    · exact Or.inr (Or.inr ⟨ha, hb, external_pivotal_center hK hold ha hb hc⟩)
  · exact Or.inl (nonstar_has_disjoint_edges G (Pivotal G K) htri (fun _ _ hp => hp.1) hne h)

lemma disjoint_support_repair {V : Type*} {G : SimpleGraph V}
    {K : Set V → Prop → Prop} {A B : Set V} (hK : ContextMono K)
    (hold : Exact G K (fun X => Hits A X ∧ Hits B X))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hAB : Disjoint A B) (hne : ∃ u v, Pivotal G K u v) :
    (∃ u v p q, Pivotal G K u v ∧ Pivotal G K p q ∧
      u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q) ∨
    ∃ c, (∀ u v, Pivotal G K u v → u = c ∨ v = c) ∧
      ((c ∈ A ∧ Exact G K (fun X => c ∈ X ∧ Hits B X)) ∨
       (c ∈ B ∧ Exact G K (fun X => c ∈ X ∧ Hits A X))) := by
  rcases pivotal_repair_cases hK hold htri hne with hd | ⟨c, hc, ha | hb | ⟨_, _, hnone⟩⟩
  · exact Or.inl hd
  · exact Or.inr ⟨c, hc, Or.inl ha⟩
  · exact Or.inr ⟨c, hc, Or.inr hb⟩
  · obtain ⟨u, v, huv⟩ := hne
    obtain ⟨w, hw, _⟩ := pivotal_requires hK hnone huv
    exact (Set.disjoint_left.mp hAB hw.1 hw.2).elim

def OtherEdges {V : Type*} (G H : SimpleGraph V) (X : Set V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v ∧ ¬ H.Adj u v

def Realize {V : Type*} (G H : SimpleGraph V) (N : Set V → Prop)
    (X : Set V) (p : Prop) : Prop :=
  OtherEdges G H X ∨ (p ∧ (HasEdge H X ∨ N X))

lemma realize_mono {V : Type*} (G H : SimpleGraph V) {N : Set V → Prop}
    (hm : SignalMono N) : ContextMono (Realize G H N) := by
  rintro X Y p q hXY hPQ (⟨u, hu, v, hv, he⟩ | ⟨hp, hH | hN⟩)
  · exact Or.inl ⟨u, hXY hu, v, hXY hv, he⟩
  · exact Or.inr ⟨hPQ hp, Or.inl (hasEdge_mono H hXY hH)⟩
  · exact Or.inr ⟨hPQ hp, Or.inr (hm hXY hN)⟩

lemma realize_exact {V : Type*} {G H : SimpleGraph V} {N s : Set V → Prop}
    (hHG : H ≤ G) (hm : SignalMono s) (hpos : ∀ u v, H.Adj u v → s {u, v})
    (hneg : ∀ X, N X → s X → HasEdge G X) : Exact G (Realize G H N) s := by
  classical
  intro X
  constructor
  · rintro (⟨u, hu, v, hv, hG, _⟩ | ⟨hs, ⟨u, hu, v, hv, hH⟩ | hN⟩)
    · exact ⟨u, hu, v, hv, hG⟩
    · exact ⟨u, hu, v, hv, hHG hH⟩
    · exact hneg X hN hs
  · rintro ⟨u, hu, v, hv, hG⟩
    by_cases hH : H.Adj u v
    · exact Or.inr ⟨hm (Set.pair_subset hu hv) (hpos u v hH), Or.inl ⟨u, hu, v, hv, hH⟩⟩
    · exact Or.inl ⟨u, hu, v, hv, hG, hH⟩

lemma otherEdges_pair {V : Type*} {G H : SimpleGraph V} {u v : V} :
    OtherEdges G H {u, v} ↔ G.Adj u v ∧ ¬ H.Adj u v := by
  constructor
  · rintro ⟨a, ha, b, hb, hg, hh⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hg.ne rfl).elim
    · exact ⟨hg, hh⟩
    · exact ⟨hg.symm, fun h => hh h.symm⟩
    · exact (hg.ne rfl).elim
  · rintro ⟨hg, hh⟩
    exact ⟨u, by simp, v, by simp, hg, hh⟩

lemma realize_pivotal {V : Type*} {G H : SimpleGraph V} (hHG : H ≤ G)
    (N : Set V → Prop) (u v : V) :
    Pivotal G (Realize G H N) u v ↔ H.Adj u v := by
  classical
  simp only [Pivotal, Realize, false_and, or_false, otherEdges_pair]
  exact ⟨fun ⟨hg, h⟩ => by_contra fun hn => h ⟨hg, hn⟩,
    fun hh => ⟨hHG hh, fun h => h.2 hh⟩⟩

lemma realize_negative {V : Type*} {G H : SimpleGraph V} (hHG : H ≤ G)
    (N : Set V → Prop) (I : Set V) (hi : ¬ HasEdge G I) :
    Realize G H N I True ↔ N I := by
  constructor
  · rintro (⟨u, hu, v, hv, hg, _⟩ | ⟨_, ⟨u, hu, v, hv, hh⟩ | hn⟩)
    · exact (hi ⟨u, hu, v, hv, hg⟩).elim
    · exact (hi ⟨u, hu, v, hv, hHG hh⟩).elim
    · exact hn
  · exact fun hn => Or.inr ⟨trivial, Or.inr hn⟩

open PEqualNP.CircuitLowerBounds

def selectedLe (x y : List Bool) : Prop :=
  List.Forall₂ (fun a b => a = true → b = true) x y

lemma selectedLe_get {x y : List Bool} (h : selectedLe x y) (i : ℕ) :
    x.getD i false = true → y.getD i false = true := by
  induction h generalizing i with
  | nil => cases i <;> simp
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ j => exact ih j

def selectedValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def selectedStep (w : List Bool) (g : Gate) : List Bool := w ++ [selectedValue g w]

lemma selectedValue_mono {g : Gate} (hgate : g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (h : selectedLe x y) :
    selectedValue g x = true → selectedValue g y = true := by
  rcases hgate with hop | hop
  · simp only [selectedValue, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq]
    intro hx i hi
    exact selectedLe_get h i (hx i hi)
  · simp only [selectedValue, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, selectedLe_get h i hx⟩

lemma selectedFold_mono (s : List Gate)
    (hgate : ∀ g ∈ s, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (h : selectedLe x y) :
    selectedLe (s.foldl selectedStep x) (s.foldl selectedStep y) := by
  induction s generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun i hi => hgate i (List.mem_cons_of_mem _ hi))
      (List.rel_append h (.cons (selectedValue_mono (hgate g (by simp)) h) .nil))

noncomputable def selectedInput {n : ℕ} (X : Set (Fin n)) : List Bool := by
  classical
  exact List.ofFn (fun i : Fin n => decide (i ∈ X))

lemma selectedInput_mono {n : ℕ} {X Y : Set (Fin n)} (h : X ⊆ Y) :
    selectedLe (selectedInput X) (selectedInput Y) := by
  classical
  apply List.forall₂_of_length_eq_of_get
  · simp [selectedInput]
  · intro i hi hj
    simp only [selectedInput, List.get_eq_getElem, List.getElem_ofFn,
      decide_eq_true_eq]
    exact fun hx => h hx

def selectedCircuit (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ) :
    Circuit := ⟨pre ++ g :: post, out⟩

noncomputable def selectedSignal {n : ℕ} (pre : List Gate) (g : Gate)
    (X : Set (Fin n)) : Prop :=
  selectedValue g (pre.foldl selectedStep (selectedInput X)) = true

noncomputable def selectedContext {n : ℕ} (pre post : List Gate) (out : ℕ)
    (X : Set (Fin n)) (p : Prop) : Prop := by
  classical
  exact (post.foldl selectedStep
    (pre.foldl selectedStep (selectedInput X) ++ [decide p])).getD out false = true

lemma selectedSignal_mono {n : ℕ} (pre : List Gate) (g : Gate)
    (hp : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) : SignalMono (selectedSignal (n := n) pre g) := by
  intro X Y h
  exact selectedValue_mono hg (selectedFold_mono pre hp (selectedInput_mono h))

lemma selectedContext_mono {n : ℕ} (pre post : List Gate) (out : ℕ)
    (hp : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or)
    (hs : ∀ a ∈ post, a.op = GateOp.and ∨ a.op = GateOp.or) :
    ContextMono (selectedContext (n := n) pre post out) := by
  classical
  intro X Y p q hXY hpq
  apply selectedLe_get (i := out)
  apply selectedFold_mono post hs
  apply List.rel_append (selectedFold_mono pre hp (selectedInput_mono hXY))
  apply List.Forall₂.cons _ .nil
  simpa using hpq

lemma selected_eval {n : ℕ} (pre post : List Gate) (out : ℕ) (g : Gate)
    (X : Set (Fin n)) :
    (selectedCircuit pre g post out).eval (selectedInput X) = true ↔
      selectedContext pre post out X (selectedSignal pre g X) := by
  classical
  let w := pre.foldl selectedStep (selectedInput X)
  let b := selectedValue g w
  change ((pre ++ g :: post).foldl selectedStep (selectedInput X)).getD out false = true ↔ _
  rw [List.foldl_append, List.foldl_cons]
  change (post.foldl selectedStep (w ++ [b])).getD out false = true ↔
    (post.foldl selectedStep (w ++ [@decide (b = true) (Classical.propDecidable _)] )).getD
      out false = true
  have hdec : @decide (b = true) (Classical.propDecidable _) = b := by
    cases b <;> simp
  rw [hdec]

lemma selected_size (pre post : List Gate) (out : ℕ) (g h : Gate) :
    (selectedCircuit pre g post out).size = (selectedCircuit pre h post out).size := by
  simp [selectedCircuit, Circuit.size]

lemma selected_ao2 (pre post : List Gate) (out : ℕ) (g h : Gate)
    (hC : ∀ i ∈ (selectedCircuit pre g post out).gates,
      (i.op = GateOp.and ∨ i.op = GateOp.or) ∧ i.inputs.length ≤ 2)
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ∀ i ∈ (selectedCircuit pre h post out).gates,
      (i.op = GateOp.and ∨ i.op = GateOp.or) ∧ i.inputs.length ≤ 2 := by
  intro i hi
  change i ∈ pre ++ h :: post at hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hC i (List.mem_append_left _ hi)
  · rcases List.mem_cons.mp hi with rfl | hi
    · exact hh
    · exact hC i (List.mem_append_right _ (List.mem_cons_of_mem _ hi))

lemma selected_split {C : Circuit} {t : ℕ} {g : Gate} (ht : C.gates[t]? = some g) :
    selectedCircuit (C.gates.take t) g (C.gates.drop (t + 1)) C.output = C := by
  obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp ht
  have hlist : C.gates.take t ++ g :: C.gates.drop (t + 1) = C.gates := by
    rw [← hg, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  cases C
  simp only [selectedCircuit, hlist]

lemma selectedFold_append (pre : List Gate) (w : List Bool) :
    ∃ tail, pre.foldl selectedStep w = w ++ tail := by
  induction pre generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (selectedStep w g)
    refine ⟨[selectedValue g w] ++ tail, ?_⟩
    simpa only [List.foldl_cons, selectedStep, List.append_assoc] using ht

noncomputable def selectedWire {n : ℕ} (pre : List Gate) (i : ℕ)
    (X : Set (Fin n)) : Prop :=
  (pre.foldl selectedStep (selectedInput X)).getD i false = true

lemma selectedWire_literal {n : ℕ} (pre : List Gate) (c : Fin n) (X : Set (Fin n)) :
    selectedWire pre c X ↔ c ∈ X := by
  classical
  obtain ⟨tail, ht⟩ := selectedFold_append pre (selectedInput X)
  have hc : c.val < (selectedInput X).length := by simp [selectedInput]
  unfold selectedWire
  rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hc,
    List.getElem?_eq_getElem hc, Option.getD_some]
  simp [selectedInput]

lemma selectedSignal_binaryAnd {n : ℕ} (pre : List Gate) (i j : ℕ) (X : Set (Fin n)) :
    selectedSignal pre ⟨GateOp.and, [i, j]⟩ X ↔ selectedWire pre i X ∧ selectedWire pre j X := by
  simp [selectedSignal, selectedValue, GateOp.eval, selectedWire]

lemma selectedSignal_literalAnd {n : ℕ} (pre : List Gate) (c : Fin n) (j : ℕ)
    (X : Set (Fin n)) :
    selectedSignal pre ⟨GateOp.and, [c, j]⟩ X ↔ c ∈ X ∧ selectedWire pre j X := by
  rw [selectedSignal_binaryAnd, selectedWire_literal]

lemma selectedInput_support {n : ℕ} (x : Fin n → Bool) :
    selectedInput {i | x i = true} = List.ofFn x := by
  classical
  unfold selectedInput
  congr 1
  funext i
  change @decide (x i = true) (Classical.propDecidable _) = x i
  cases x i <;> simp

lemma selectedWire_mono {n : ℕ} (pre : List Gate) (i : ℕ)
    (hp : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or) :
    SignalMono (selectedWire (n := n) pre i) := by
  intro X Y h
  exact selectedLe_get (selectedFold_mono pre hp (selectedInput_mono h)) i

lemma selected_computes_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (out : ℕ) (g : Gate) :
    (∀ x : Fin n → Bool, (selectedCircuit pre g post out).eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ↔
    ∀ X : Set (Fin n), selectedContext pre post out X (selectedSignal pre g X) ↔
      ∃ u ∈ X, ∃ v ∈ X, G.Adj u v := by
  classical
  constructor
  · intro h X
    rw [← selected_eval]
    unfold selectedInput
    rw [h]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      exact ⟨u, hu, v, hv, he⟩
    · rintro ⟨u, hu, v, hv, he⟩
      exact ⟨u, v, he, hu, hv⟩
  · intro h x
    specialize h {i | x i = true}
    rw [← selected_eval, selectedInput_support] at h
    rw [Bool.eq_iff_iff, h, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, v, hv, he⟩
      exact ⟨u, v, he, hu, hv⟩
    · rintro ⟨u, v, he, hu, hv⟩
      exact ⟨u, hu, v, hv, he⟩

lemma selectedFold_length (pre : List Gate) (w : List Bool) :
    (pre.foldl selectedStep w).length = w.length + pre.length := by
  induction pre generalizing w with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons, ih]
    simp [selectedStep, Nat.add_comm, Nat.add_left_comm]

lemma selectedSignal_at {n : ℕ} (pre post : List Gate) (out : ℕ) (g : Gate)
    (X : Set (Fin n)) : selectedSignal pre g X ↔
    ((selectedCircuit pre g post out).wires (selectedInput X)).getD (n + pre.length) false = true := by
  change _ ↔ (((pre ++ g :: post).foldl selectedStep (selectedInput X)).getD _ false = true)
  rw [List.foldl_append, List.foldl_cons]
  obtain ⟨tail, ht⟩ := selectedFold_append post (selectedStep (pre.foldl selectedStep (selectedInput X)) g)
  rw [ht]
  have hw : (pre.foldl selectedStep (selectedInput X)).length = n + pre.length := by
    simp [selectedFold_length, selectedInput]
  have hw' : n + pre.length < (selectedStep (pre.foldl selectedStep (selectedInput X)) g).length := by
    simp [selectedStep, hw]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw']
  simp [selectedSignal, selectedStep, hw]

lemma selectedInput_pair {n : ℕ} (u v : Fin n) :
    selectedInput {u, v} = List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)) := by
  classical
  unfold selectedInput
  congr 1
  funext k
  simp

def SelectedRead (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ k h, b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs

lemma selectedRead_lt {n : ℕ} {C : Circuit} {a b : ℕ}
    (hp : Relation.TransGen (SelectedRead n C) a b) : a < b := by
  induction hp with
  | single h => exact h.1
  | tail _ h ih => exact ih.trans h.1

def SelectedOwn {n : ℕ} (C : Circuit) (t : ℕ) (u v : Fin n) : Prop :=
  ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true) ∧
  ∀ t' (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
    Relation.TransGen (SelectedRead n C) (n + t') (n + t) →
    (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false

lemma selected_first_owns_iff {n : ℕ} (pre post : List Gate) (out : ℕ)
    (g : Gate) (hp : ∀ a ∈ pre, a.op = GateOp.or) (u v : Fin n) :
    SelectedOwn (selectedCircuit pre g post out) pre.length u v ↔ selectedSignal pre g {u, v} := by
  constructor
  · intro h
    apply (selectedSignal_at pre post out g {u,v}).2
    rw [selectedInput_pair]
    exact h.1
  · intro h
    constructor
    · rw [← selectedInput_pair]
      exact (selectedSignal_at pre post out g {u,v}).1 h
    · intro t' g' ht' ha hpath
      have hlt : t' < pre.length := by
        have h' := selectedRead_lt hpath
        omega
      change (pre ++ g :: post)[t']? = some g' at ht'
      rw [List.getElem?_append_left hlt] at ht'
      have hmem : g' ∈ pre := List.mem_of_getElem? ht'
      have hh := hp g' hmem
      simp_all

lemma selected_first_center_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (out i j : ℕ) (c : Fin n)
    (hC : ∀ a ∈ (selectedCircuit pre ⟨GateOp.and, [i, j]⟩ post out).gates,
      (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2)
    (hp : ∀ a ∈ pre, a.op = GateOp.or)
    (hold : ∀ x : Fin n → Bool, (selectedCircuit pre ⟨GateOp.and, [i,j]⟩ post out).eval
      (List.ofFn x) = decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hdom : selectedWire pre i {c})
    (hne : ∃ u v, Pivotal G (selectedContext pre post out) u v)
    (hstar : ∀ u v, Pivotal G (selectedContext pre post out) u v → u = c ∨ v = c) :
    let D := selectedCircuit pre ⟨GateOp.and, [c,j]⟩ post out
    D.size = (selectedCircuit pre ⟨GateOp.and, [i,j]⟩ post out).size ∧
    (∀ a ∈ D.gates, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
    (∃ u v, G.Adj u v ∧ SelectedOwn D pre.length u v) ∧
    (∀ u v, G.Adj u v → SelectedOwn D pre.length u v → u = c ∨ v = c) := by
  dsimp only
  have hp' : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or := fun a ha => Or.inr (hp a ha)
  have hpost : ∀ a ∈ post, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    exact (hC a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  have hm : ContextMono (selectedContext (n := n) pre post out) :=
    selectedContext_mono _ _ _ hp' hpost
  have hA := (selected_computes_iff G pre post out ⟨GateOp.and,[i,j]⟩).1 hold
  have hE : Exact G (selectedContext pre post out) (fun X => selectedWire pre i X ∧ selectedWire pre j X) := by
    simpa only [Exact, HasEdge, selectedSignal_binaryAnd] using hA
  have hnew := center_rewire hm hE (selectedWire_mono pre j hp')
    (fun X hc => selectedWire_mono pre i hp' (Set.singleton_subset_iff.mpr hc) hdom) hstar
  have hD : Exact G (selectedContext pre post out) (selectedSignal pre ⟨GateOp.and,[c,j]⟩) := by
    simpa only [Exact, selectedSignal_literalAnd] using hnew
  refine ⟨selected_size _ _ _ _ _, selected_ao2 _ _ _ _ _ hC (by simp),
    (selected_computes_iff G pre post out _).2 hD, ?_, ?_⟩
  · obtain ⟨u,v,he⟩ := hne
    exact ⟨u, v, he.1, (selected_first_owns_iff _ _ _ _ hp _ _).2 (pivotal_requires hm hD he)⟩
  · intro u v _ h
    have hc := ((selectedSignal_literalAnd pre c j {u,v}).1
      ((selected_first_owns_iff _ _ _ _ hp _ _).1 h)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    exact hc.imp Eq.symm Eq.symm

lemma selected_lookup_ne (pre post : List Gate) (out : ℕ) (g h : Gate) {k : ℕ}
    (hk : k ≠ pre.length) :
    (selectedCircuit pre g post out).gates[k]? = (selectedCircuit pre h post out).gates[k]? := by
  change (pre ++ g :: post)[k]? = (pre ++ h :: post)[k]?
  by_cases hlt : k < pre.length
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · obtain ⟨r, hr⟩ : ∃ r, k - pre.length = r+1 := ⟨k - pre.length - 1, by omega⟩
    rw [List.getElem?_append_right (Nat.le_of_not_gt hlt),
      List.getElem?_append_right (Nat.le_of_not_gt hlt), hr]
    rfl

lemma selected_rewire_step {n : ℕ} (pre post : List Gate) (out i j : ℕ) (c : Fin n)
    {a b : ℕ} (ha : n ≤ a)
    (he : SelectedRead n (selectedCircuit pre ⟨GateOp.and,[c,j]⟩ post out) a b) :
    SelectedRead n (selectedCircuit pre ⟨GateOp.and,[i,j]⟩ post out) a b := by
  obtain ⟨hab,k,h,hb,hk,hh⟩ := he
  by_cases ht : k = pre.length
  · subst k
    simp [selectedCircuit] at hk
    subst h
    refine ⟨hab,pre.length,⟨GateOp.and,[i,j]⟩,hb,by simp [selectedCircuit],?_⟩
    have haj : a = j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      exact hh.resolve_left (fun h => by have h' := c.isLt; omega)
    simp [haj]
  · exact ⟨hab,k,h,hb,(selected_lookup_ne pre post out _ _ ht).trans hk,hh⟩

lemma selected_rewire_path {n : ℕ} (pre post : List Gate) (out i j : ℕ) (c : Fin n)
    {a b : ℕ} (ha : n ≤ a)
    (hp : Relation.TransGen (SelectedRead n (selectedCircuit pre ⟨GateOp.and,[c,j]⟩ post out)) a b) :
    Relation.TransGen (SelectedRead n (selectedCircuit pre ⟨GateOp.and,[i,j]⟩ post out)) a b := by
  induction hp with
  | single h => exact .single (selected_rewire_step pre post out i j c ha h)
  | tail h e ih => exact ih.tail (selected_rewire_step pre post out i j c
      (ha.trans (selectedRead_lt h).le) e)

lemma selected_prefix_at {n : ℕ} (pre post : List Gate) (out : ℕ) (g : Gate)
    (X : Set (Fin n)) {r : ℕ} (hr : r < n + pre.length) :
    ((selectedCircuit pre g post out).wires (selectedInput X)).getD r false =
    (pre.foldl selectedStep (selectedInput X)).getD r false := by
  change ((pre ++ g :: post).foldl selectedStep (selectedInput X)).getD _ _ = _
  rw [List.foldl_append]
  obtain ⟨tail, ht⟩ := selectedFold_append (g :: post) (pre.foldl selectedStep (selectedInput X))
  have hw : r < (pre.foldl selectedStep (selectedInput X)).length := by
    simpa [selectedFold_length, selectedInput] using hr
  rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]

lemma selected_owned_survives {n : ℕ} (pre post : List Gate) (out i j : ℕ)
    (c u v : Fin n) (hc : u = c ∨ v = c)
    (ho : SelectedOwn (selectedCircuit pre ⟨GateOp.and,[i,j]⟩ post out) pre.length u v) :
    SelectedOwn (selectedCircuit pre ⟨GateOp.and,[c,j]⟩ post out) pre.length u v := by
  obtain ⟨hs, hp⟩ := ho
  rw [← selectedInput_pair] at hs
  have hg := (selectedSignal_at pre post out _ {u,v}).2 hs
  have hj := ((selectedSignal_binaryAnd pre i j {u,v}).1 hg).2
  constructor
  · rw [← selectedInput_pair]
    apply (selectedSignal_at pre post out _ {u,v}).1
    apply (selectedSignal_literalAnd pre c j {u,v}).2
    refine ⟨?_, hj⟩
    rcases hc with rfl | rfl <;> simp
  · intro t g ht ha hpath
    have hlt : t < pre.length := by
      have h := selectedRead_lt hpath
      omega
    have ht' := (selected_lookup_ne pre post out ⟨GateOp.and,[i,j]⟩ ⟨GateOp.and,[c,j]⟩ hlt.ne).trans ht
    have hval := hp t g ht' ha (selected_rewire_path pre post out i j c (by omega) hpath)
    have hwn : n + t < n + pre.length := by omega
    rw [← selectedInput_pair, selected_prefix_at pre post out _ _ hwn] at hval ⊢
    exact hval

lemma selected_center_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (out i j : ℕ) (c : Fin n)
    (hC : ∀ a ∈ (selectedCircuit pre ⟨GateOp.and, [i,j]⟩ post out).gates,
      (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2)
    (hold : ∀ x : Fin n → Bool, (selectedCircuit pre ⟨GateOp.and,[i,j]⟩ post out).eval
      (List.ofFn x) = decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hdom : selectedWire pre i {c})
    (hne : ∃ u v, G.Adj u v ∧ (u = c ∨ v = c) ∧
      SelectedOwn (selectedCircuit pre ⟨GateOp.and,[i,j]⟩ post out) pre.length u v)
    (hstar : ∀ u v, Pivotal G (selectedContext pre post out) u v → u = c ∨ v = c) :
    let D := selectedCircuit pre ⟨GateOp.and, [c,j]⟩ post out
    D.size = (selectedCircuit pre ⟨GateOp.and, [i,j]⟩ post out).size ∧
    (∀ a ∈ D.gates, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
    (∃ u v, G.Adj u v ∧ SelectedOwn D pre.length u v) ∧
    (∀ u v, G.Adj u v → SelectedOwn D pre.length u v → u = c ∨ v = c) := by
  dsimp only
  have hp : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    exact (hC a (List.mem_append_left _ ha)).1
  have hs : ∀ a ∈ post, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    exact (hC a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  have hm : ContextMono (selectedContext (n := n) pre post out) :=
    selectedContext_mono _ _ _ hp hs
  have hA := (selected_computes_iff G pre post out ⟨GateOp.and,[i,j]⟩).1 hold
  have hE : Exact G (selectedContext pre post out) (fun X => selectedWire pre i X ∧ selectedWire pre j X) := by
    simpa only [Exact, HasEdge, selectedSignal_binaryAnd] using hA
  have hnew := center_rewire hm hE (selectedWire_mono pre j hp)
    (fun X hc => selectedWire_mono pre i hp (Set.singleton_subset_iff.mpr hc) hdom) hstar
  have hD : Exact G (selectedContext pre post out) (selectedSignal pre ⟨GateOp.and,[c,j]⟩) := by
    simpa only [Exact, selectedSignal_literalAnd] using hnew
  refine ⟨selected_size _ _ _ _ _, selected_ao2 _ _ _ _ _ hC (by simp),
    (selected_computes_iff G pre post out _).2 hD, ?_, ?_⟩
  · obtain ⟨u,v,he,hc,ho⟩ := hne
    exact ⟨u,v,he,selected_owned_survives pre post out i j c u v hc ho⟩
  · intro u v _ h
    have hw := h.1
    rw [← selectedInput_pair] at hw
    have hc := ((selectedSignal_literalAnd pre c j {u,v}).1
      ((selectedSignal_at pre post out _ {u,v}).2 hw)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    exact hc.imp Eq.symm Eq.symm

lemma selected_prior_step {n : ℕ} (pre post : List Gate) (out : ℕ) (g h : Gate)
    {a b : ℕ} (hlt : b < n + pre.length)
    (he : SelectedRead n (selectedCircuit pre g post out) a b) :
    SelectedRead n (selectedCircuit pre h post out) a b := by
  obtain ⟨hab,k,z,hb,hk,hz⟩ := he
  exact ⟨hab,k,z,hb,(selected_lookup_ne pre post out h g (by omega : k ≠ pre.length)).trans hk,hz⟩

lemma selected_prior_path {n : ℕ} (pre post : List Gate) (out : ℕ) (g h : Gate)
    {a b : ℕ} (hp : Relation.TransGen (SelectedRead n (selectedCircuit pre g post out)) a b)
    (hlt : b < n + pre.length) :
    Relation.TransGen (SelectedRead n (selectedCircuit pre h post out)) a b := by
  induction hp with
  | single e => exact .single (selected_prior_step pre post out g h hlt e)
  | tail _ e ih =>
    exact .tail (ih (lt_trans e.1 hlt)) (selected_prior_step pre post out g h hlt e)

lemma selected_prior_owns {n : ℕ} (pre post : List Gate) (out : ℕ) (g h : Gate)
    {t : ℕ} (ht : t < pre.length) (u v : Fin n)
    (ho : SelectedOwn (selectedCircuit pre g post out) t u v) :
    SelectedOwn (selectedCircuit pre h post out) t u v := by
  obtain ⟨hw,hp⟩ := ho
  have hwlt : n + t < n + pre.length := by omega
  constructor
  · rw [← selectedInput_pair, selected_prefix_at pre post out _ _ hwlt] at hw ⊢
    exact hw
  · intro t' z hz ha hpath
    have hlt : t' < pre.length := by
      have h := selectedRead_lt hpath
      omega
    have hz' := (selected_lookup_ne pre post out g h hlt.ne).trans hz
    have hval := hp t' z hz' ha (selected_prior_path pre post out h g hpath hwlt)
    have hwn : n + t' < n + pre.length := by omega
    rw [← selectedInput_pair, selected_prefix_at pre post out _ _ hwn] at hval ⊢
    exact hval

lemma selected_prior_owns_iff {n : ℕ} (pre post : List Gate) (out : ℕ) (g h : Gate)
    {t : ℕ} (ht : t < pre.length) (u v : Fin n) :
    SelectedOwn (selectedCircuit pre g post out) t u v ↔
      SelectedOwn (selectedCircuit pre h post out) t u v :=
  ⟨selected_prior_owns pre post out g h ht u v, selected_prior_owns pre post out h g ht u v⟩

end PEqualNP.Outside.L_meta_1031.FreshCore
