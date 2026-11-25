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

end PEqualNP.Outside.L_meta_1031.FreshCore
