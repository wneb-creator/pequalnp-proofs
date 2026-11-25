import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

variable {α : Type*} [DecidableEq α]

def ORClass (F : (α → Bool) → Bool) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ x : α → Bool,
    F (Function.update x a true) = F (Function.update x b true)

def classPair (a b : α) : α → Bool := fun x => decide (x = a) || decide (x = b)

lemma classPair_update (a b : α) :
    classPair a b = Function.update (fun x => decide (x = b)) a true := by
  funext x
  by_cases h : x = a
  · subst x
    simp [classPair]
  · simp [classPair, h]

lemma classPair_comm (a b : α) : classPair a b = classPair b a := by
  funext x
  exact Bool.or_comm _ _

lemma orClass_card_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (S : Finset α) (hclass : ORClass F S)
    (hsub : S ⊆ Finset.univ.image left ∪ Finset.univ.image right) : S.card ≤ 2 := by
  classical
  let L := Finset.univ.image left
  let R := Finset.univ.image right
  have hL : (S ∩ L).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haL⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbS, hbL⟩ := Finset.mem_inter.mp hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp haL
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbL
    apply congrArg left
    apply hrows
    funext w
    rw [← hpair u w, ← hpair v w, classPair_update, classPair_update]
    exact hclass _ haS _ hbS _
  have hR : (S ∩ R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haR⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbS, hbR⟩ := Finset.mem_inter.mp hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp haR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbR
    apply congrArg right
    apply hcols
    funext w
    change A w u = A w v
    rw [← hpair w u, ← hpair w v, classPair_comm (left w) (right u),
      classPair_comm (left w) (right v), classPair_update, classPair_update]
    exact hclass _ haS _ hbS _
  have hcover : S = (S ∩ L) ∪ (S ∩ R) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp (hsub ha) with hl | hr
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, hr⟩)
    · intro ha
      rcases Finset.mem_union.mp ha with hl | hr
      · exact (Finset.mem_inter.mp hl).1
      · exact (Finset.mem_inter.mp hr).1
  calc
    S.card = ((S ∩ L) ∪ (S ∩ R)).card := congrArg Finset.card hcover
    _ ≤ (S ∩ L).card + (S ∩ R).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

lemma orClass_valid_card_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (S : Finset α) (hclass : ORClass F S) :
    (S ∩ (Finset.univ.image left ∪ Finset.univ.image right)).card ≤ 2 := by
  apply orClass_card_le_two F A left right hpair hrows hcols
  · exact fun a ha b hb => hclass a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
  · exact fun a ha => (Finset.mem_inter.mp ha).2


lemma orClasses_valid_union_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (K : Finset (Finset α)) (hK : ∀ S ∈ K, ORClass F S) :
    ((K.biUnion id) ∩ (Finset.univ.image left ∪ Finset.univ.image right)).card ≤ 2 * K.card := by
  classical
  let V := Finset.univ.image left ∪ Finset.univ.image right
  have heq : (K.biUnion id) ∩ V = K.biUnion (fun S => S ∩ V) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨⟨S, hS, ha⟩, hv⟩
      exact ⟨S, hS, ha, hv⟩
    · rintro ⟨S, hS, ha, hv⟩
      exact ⟨⟨S, hS, ha⟩, hv⟩
  change ((K.biUnion id) ∩ V).card ≤ _
  rw [heq]
  calc
    (K.biUnion (fun S => S ∩ V)).card ≤ ∑ S ∈ K, (S ∩ V).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ K, 2 := Finset.sum_le_sum fun S hS =>
      orClass_valid_card_le_two F A left right hpair hrows hcols S (hK S hS)
    _ = 2 * K.card := by simp [Nat.mul_comm]

end PEqualNP.Outside.L_meta_9502
