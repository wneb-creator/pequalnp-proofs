import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.LinearCleanup

variable {α : Type*}

def Hit (S : Set α) (x : α → Prop) : Prop := ∃ v ∈ S, x v

def Edge (G : SimpleGraph α) (x : α → Prop) : Prop :=
  ∃ u v, G.Adj u v ∧ x u ∧ x v

def Product (A B : Set α) (x : α → Prop) : Prop := Hit A x ∧ Hit B x

def Cleanup (A B T : Set α) (x : α → Prop) : Prop := Product A B x ∧ Hit T x

def Reduced (A B T : Set α) (x : α → Prop) : Prop :=
  (Hit (A ∩ T) x ∧ Hit B x) ∨ (Hit (B ∩ T) x ∧ Hit A x)

def Centers (G : SimpleGraph α) (A B : Set α) : Set α :=
  {a | a ∈ A ∧ ∀ b ∈ B, G.Adj a b}

def PairSound (G : SimpleGraph α) (A B T : Set α) : Prop :=
  ∀ s t, Cleanup A B T (fun v => v = s ∨ v = t) → G.Adj s t

lemma edge_pair_iff (G : SimpleGraph α) (s t : α) :
    Edge G (fun v => v = s ∨ v = t) ↔ G.Adj s t := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv.ne rfl).elim
    · exact huv
    · exact huv.symm
    · exact (huv.ne rfl).elim
  · intro h
    exact ⟨s, t, h, Or.inl rfl, Or.inr rfl⟩

lemma reduced_le_cleanup (A B T : Set α) (x : α → Prop) :
    Reduced A B T x → Cleanup A B T x := by
  rintro (⟨⟨a, ha, hax⟩, hb⟩ | ⟨⟨b, hb, hbx⟩, ha⟩)
  · exact ⟨⟨⟨a, ha.1, hax⟩, hb⟩, ⟨a, ha.2, hax⟩⟩
  · exact ⟨⟨ha, ⟨b, hb.1, hbx⟩⟩, ⟨b, hb.2, hbx⟩⟩

lemma cleanup_pair_reduced (A B T : Set α) (hdis : Disjoint A B) (s t : α) :
    Cleanup A B T (fun v => v = s ∨ v = t) ↔
      Reduced A B T (fun v => v = s ∨ v = t) := by
  constructor
  · rintro ⟨⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, c, hc, hcx⟩
    have hab : a ≠ b := by
      intro heq
      subst b
      exact Set.disjoint_left.mp hdis ha hb
    have hca : c = a ∨ c = b := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (hab rfl).elim
      · exact hcx
      · exact hcx.symm
      · exact (hab rfl).elim
    rcases hca with hca | hcb
    · exact Or.inl ⟨⟨a, ⟨ha, hca ▸ hc⟩, hax⟩, ⟨b, hb, hbx⟩⟩
    · exact Or.inr ⟨⟨b, ⟨hb, hcb ▸ hc⟩, hbx⟩, ⟨a, ha, hax⟩⟩
  · exact reduced_le_cleanup A B T _

lemma sound_context_left (G : SimpleGraph α) (A B T : Set α)
    (hsound : PairSound G A B T) :
    A ∩ T ⊆ Centers G A B := by
  intro a ha
  refine ⟨ha.1, ?_⟩
  intro b hb
  apply hsound a b
  exact ⟨⟨⟨a, ha.1, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩,
    ⟨a, ha.2, Or.inl rfl⟩⟩

lemma sound_context_right (G : SimpleGraph α) (A B T : Set α)
    (hsound : PairSound G A B T) :
    B ∩ T ⊆ Centers G B A := by
  intro b hb
  refine ⟨hb.1, ?_⟩
  intro a ha
  apply hsound b a
  exact ⟨⟨⟨a, ha, Or.inr rfl⟩, ⟨b, hb.1, Or.inl rfl⟩⟩,
    ⟨b, hb.2, Or.inl rfl⟩⟩

lemma centers_subsingleton (G : SimpleGraph α) (A B : Set α)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (b d : α) (hb : b ∈ B) (hd : d ∈ B) (hbd : b ≠ d) :
    (Centers G A B).Subsingleton := by
  intro a ha c hc
  rcases hfour a b c d (ha.2 b hb) (hc.2 b hb).symm
    (hc.2 d hd) (ha.2 d hd).symm with hac | hbd'
  · exact hac
  · exact (hbd hbd').elim

theorem shared_linear_cleanup (G : SimpleGraph α) (A B : Set α)
    (hdis : Disjoint A B)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (a c b d : α) (ha : a ∈ A) (hc : c ∈ A) (hac : a ≠ c)
    (hb : b ∈ B) (hd : d ∈ B) (hbd : b ≠ d) :
    (Centers G A B).Subsingleton ∧ (Centers G B A).Subsingleton ∧
      ∀ T : Set α, PairSound G A B T →
        A ∩ T ⊆ Centers G A B ∧ B ∩ T ⊆ Centers G B A ∧
        (∀ x, Reduced A B T x → Cleanup A B T x) ∧
        ∀ s t, Cleanup A B T (fun v => v = s ∨ v = t) ↔
          Reduced A B T (fun v => v = s ∨ v = t) := by
  refine ⟨centers_subsingleton G A B hfour b d hb hd hbd,
    centers_subsingleton G B A hfour a c ha hc hac, ?_⟩
  intro T hsound
  exact ⟨sound_context_left G A B T hsound, sound_context_right G A B T hsound,
    reduced_le_cleanup A B T, cleanup_pair_reduced A B T hdis⟩

lemma reduced_sound (G : SimpleGraph α) (A B T : Set α)
    (hsound : PairSound G A B T) (x : α → Prop) :
    Reduced A B T x → Edge G x := by
  rintro (⟨⟨a, ha, hax⟩, b, hb, hbx⟩ | ⟨⟨b, hb, hbx⟩, a, ha, hax⟩)
  · exact ⟨a, b, (sound_context_left G A B T hsound ha).2 b hb, hax, hbx⟩
  · exact ⟨b, a, (sound_context_right G A B T hsound hb).2 a ha, hbx, hax⟩

end PEqualNP.Outside.L_meta_2448_aux.LinearCleanup
