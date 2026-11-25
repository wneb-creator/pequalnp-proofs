import LinearCleanup

namespace PEqualNP.Outside.L_meta_2448_aux.TwoCenterRepair

open PEqualNP.Outside.L_meta_2448_aux.LinearCleanup

variable {α : Type*}

def Repair (A B : Set α) (c d : α) (x : α → Prop) : Prop :=
  (x c ∧ Hit B x) ∨ (x d ∧ Hit A x)

lemma repair_mono (A B : Set α) (c d : α) (x y : α → Prop)
    (hxy : ∀ v, x v → y v) : Repair A B c d x → Repair A B c d y := by
  rintro (⟨hc, b, hb, hbx⟩ | ⟨hd, a, ha, hax⟩)
  · exact Or.inl ⟨hxy c hc, b, hb, hxy b hbx⟩
  · exact Or.inr ⟨hxy d hd, a, ha, hxy a hax⟩

lemma disjoint_of_centers (G : SimpleGraph α) (A B : Set α) (c d : α)
    (htri : ∀ a b e, G.Adj a b → G.Adj b e → ¬G.Adj e a)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A) : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro v hvA hvB
  exact htri c d v (hc.2 d hd.1) (hd.2 v hvA) (hc.2 v hvB).symm

lemma cross_edge_centered (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hfour : ∀ a b e f, G.Adj a b → G.Adj b e → G.Adj e f →
      G.Adj f a → a = e ∨ b = f)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (a b : α) (ha : a ∈ A) (hb : b ∈ B) (hab : G.Adj a b) : a = c ∨ b = d := by
  rcases hfour c b a d (hc.2 b hb) hab.symm (hd.2 a ha).symm
    (hc.2 d hd.1).symm with hca | hbd
  · exact Or.inl hca.symm
  · exact Or.inr hbd

lemma repair_le_product (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A) (x : α → Prop) :
    Repair A B c d x → Product A B x := by
  rintro (⟨hcx, hb⟩ | ⟨hdx, ha⟩)
  · exact ⟨⟨c, hc.1, hcx⟩, hb⟩
  · exact ⟨ha, ⟨d, hd.1, hdx⟩⟩

lemma repair_sound (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A) (x : α → Prop) :
    Repair A B c d x → Edge G x := by
  rintro (⟨hcx, b, hb, hbx⟩ | ⟨hdx, a, ha, hax⟩)
  · exact ⟨c, b, hc.2 b hb, hcx, hbx⟩
  · exact ⟨d, a, hd.2 a ha, hdx, hax⟩

lemma repair_preserves_edges (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hdis : Disjoint A B)
    (hfour : ∀ a b e f, G.Adj a b → G.Adj b e → G.Adj e f →
      G.Adj f a → a = e ∨ b = f)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (s t : α) (hst : G.Adj s t) :
    Product A B (fun v => v = s ∨ v = t) ↔
      Repair A B c d (fun v => v = s ∨ v = t) := by
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    have hab : a ≠ b := by
      intro heq
      subst b
      exact Set.disjoint_left.mp hdis ha hb
    have hedge : G.Adj a b := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (hab rfl).elim
      · exact hst
      · exact hst.symm
      · exact (hab rfl).elim
    rcases cross_edge_centered G A B c d hfour hc hd a b ha hb hedge with hac | hbd
    · exact Or.inl ⟨hac ▸ hax, b, hb, hbx⟩
    · exact Or.inr ⟨hbd ▸ hbx, a, ha, hax⟩
  · exact repair_le_product G A B c d hc hd _

theorem cofactor_repair (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hdis : Disjoint A B)
    (hfour : ∀ a b e f, G.Adj a b → G.Adj b e → G.Adj e f →
      G.Adj f a → a = e ∨ b = f)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (R K : (α → Prop) → Prop)
    (hR : ∀ x y, (∀ v, x v → y v) → R x → R y)
    (hF : ∀ x, Edge G x ↔ R x ∨ (Product A B x ∧ K x)) :
    ∀ x, Edge G x ↔ R x ∨ Repair A B c d x := by
  intro x
  constructor
  · rintro ⟨s, t, hst, hsx, htx⟩
    have hxy : ∀ v, (v = s ∨ v = t) → x v := by
      intro v hv
      rcases hv with rfl | rfl
      · exact hsx
      · exact htx
    have he := (edge_pair_iff G s t).mpr hst
    rcases (hF _).mp he with hr | ⟨hp, _⟩
    · exact Or.inl (hR _ x hxy hr)
    · exact Or.inr (repair_mono A B c d _ x hxy
        ((repair_preserves_edges G A B c d hdis hfour hc hd s t hst).mp hp))
  · rintro (hr | hh)
    · exact (hF x).mpr (Or.inl hr)
    · exact repair_sound G A B c d hc hd x hh

end PEqualNP.Outside.L_meta_2448_aux.TwoCenterRepair
