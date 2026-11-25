import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.DirtyContext

variable {V : Type*} [DecidableEq V]

def HasEdge (G : V → V → Prop) (S : Finset V) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, G u v

noncomputable def Residual (G : V → V → Prop) (A Y : Finset V) : Finset V := by
  classical
  exact A.filter (fun a => ∀ y ∈ Y, ¬ G a y)

lemma independent_insert_pair
    (G : V → V → Prop)
    (hsym : ∀ a b, G a b → G b a)
    (hirr : ∀ a, ¬ G a a)
    (Y : Finset V) (hY : ¬ HasEdge G Y)
    (a b : V) (ha : ∀ y ∈ Y, ¬ G a y)
    (hb : ∀ y ∈ Y, ¬ G b y)
    (he : HasEdge G (insert a (insert b Y))) : G a b := by
  rcases he with ⟨u, hu, v, hv, huv⟩
  simp only [Finset.mem_insert] at hu hv
  rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv
  · exact False.elim (hirr _ huv)
  · exact huv
  · exact False.elim (ha _ hv huv)
  · exact hsym _ _ huv
  · exact False.elim (hirr _ huv)
  · exact False.elim (hb _ hv huv)
  · exact False.elim (ha _ hu (hsym _ _ huv))
  · exact False.elim (hb _ hu (hsym _ _ huv))
  · exact False.elim (hY ⟨_, hu, _, hv, huv⟩)

lemma residual_rectangle
    (G : V → V → Prop)
    (hsym : ∀ a b, G a b → G b a)
    (hirr : ∀ a, ¬ G a a)
    (A B Y : Finset V) (H : Finset V → Prop)
    (hmono : ∀ S T, S ⊆ T → H S → H T)
    (hguard : ∀ S, H S → (A ∩ S).Nonempty → (B ∩ S).Nonempty → HasEdge G S)
    (hY : ¬ HasEdge G Y) (hHY : H Y) :
    ∀ a ∈ Residual G A Y, ∀ b ∈ Residual G B Y, G a b := by
  classical
  intro a ha b hb
  rw [Residual, Finset.mem_filter] at ha hb
  apply independent_insert_pair G hsym hirr Y hY a b ha.2 hb.2
  apply hguard
  · apply hmono Y (insert a (insert b Y)) _ hHY
    intro y hy
    simp only [Finset.mem_insert]
    exact Or.inr (Or.inr hy)
  · exact ⟨a, Finset.mem_inter.mpr ⟨ha.1, Finset.mem_insert_self _ _⟩⟩
  · exact ⟨b, Finset.mem_inter.mpr ⟨hb.1, Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)⟩⟩

lemma rectangle_card
    (G : V → V → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      G a b → G a' b → G a b' → G a' b' → False)
    (A B : Finset V) (hAB : ∀ a ∈ A, ∀ b ∈ B, G a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp h.2
  exact hfour a a' b b' haa' hbb' (hAB a ha b hb)
    (hAB a' ha' b hb) (hAB a ha b' hb') (hAB a' ha' b' hb')

lemma residual_rectangle_card
    (G : V → V → Prop)
    (hsym : ∀ a b, G a b → G b a)
    (hirr : ∀ a, ¬ G a a)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      G a b → G a' b → G a b' → G a' b' → False)
    (A B Y : Finset V) (H : Finset V → Prop)
    (hmono : ∀ S T, S ⊆ T → H S → H T)
    (hguard : ∀ S, H S → (A ∩ S).Nonempty → (B ∩ S).Nonempty → HasEdge G S)
    (hY : ¬ HasEdge G Y) (hHY : H Y) :
    (Residual G A Y).card ≤ 1 ∨ (Residual G B Y).card ≤ 1 := by
  exact rectangle_card G hfour _ _ (residual_rectangle G hsym hirr A B Y H hmono
    hguard hY hHY)

lemma monotone_bool_shannon
    (E : Bool → Bool) (hE : E false = true → E true = true) (z : Bool) :
    E z = (E false || (z && E true)) := by
  cases z
  · simp
  · cases hf : E false <;> cases ht : E true <;> simp_all

noncomputable def Clause (A S : Finset V) : Bool := by
  classical
  exact decide (A ∩ S).Nonempty

lemma cofactor_residual_rectangle
    (G : V → V → Prop)
    (hsym : ∀ a b, G a b → G b a)
    (hirr : ∀ a, ¬ G a a)
    (A B Y : Finset V) (E : Finset V → Bool → Bool)
    (hmono : ∀ S T, S ⊆ T → E S true = true → E T true = true)
    (hcorrect : ∀ S,
      E S (Clause A S && Clause B S) = true ↔ HasEdge G S)
    (hY : ¬ HasEdge G Y) (hHY : E Y true = true) :
    ∀ a ∈ Residual G A Y, ∀ b ∈ Residual G B Y, G a b := by
  classical
  apply residual_rectangle G hsym hirr A B Y (fun S => E S true = true) hmono
  · intro S hH hA hB
    apply (hcorrect S).mp
    simpa only [Clause, decide_eq_true hA, decide_eq_true hB, Bool.and_self] using hH
  · exact hY
  · exact hHY

lemma cofactor_residual_rectangle_card
    (G : V → V → Prop)
    (hsym : ∀ a b, G a b → G b a)
    (hirr : ∀ a, ¬ G a a)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      G a b → G a' b → G a b' → G a' b' → False)
    (A B Y : Finset V) (E : Finset V → Bool → Bool)
    (hmono : ∀ S T, S ⊆ T → E S true = true → E T true = true)
    (hcorrect : ∀ S,
      E S (Clause A S && Clause B S) = true ↔ HasEdge G S)
    (hY : ¬ HasEdge G Y) (hHY : E Y true = true) :
    (Residual G A Y).card ≤ 1 ∨ (Residual G B Y).card ≤ 1 := by
  exact rectangle_card G hfour _ _
    (cofactor_residual_rectangle G hsym hirr A B Y E hmono hcorrect hY hHY)

end PEqualNP.Outside.L_meta_2583.DirtyContext
