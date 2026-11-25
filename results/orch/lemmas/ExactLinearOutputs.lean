import TwentyOne

namespace PEqualNP.Outside.L_meta_1896_aux.ExactLinearOutputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.FourRowsSensitivity

def singletonInput {n : ℕ} (v : Fin n) : Fin n → Bool :=
  fun w => decide (w = v)

def complementInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun w => decide (w ∉ S)

noncomputable def charges {n : ℕ} (gates : List Gate) (S : Finset (Fin n)) :
    Finset (Fin gates.length) :=
  Finset.univ.filter fun j => Mrg gates S (complementInput S) singletonInput j

lemma singleton_mem_of_false_complement {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) (v : Fin n)
    (hf : val gates w (complementInput S) = false)
    (ht : val gates w (singletonInput v) = true) : v ∈ S := by
  classical
  by_contra hv
  have hmono : ∀ u, singletonInput v u = true → complementInput S u = true := by
    intro u hu
    have he : u = v := by simpa [singletonInput] using hu
    subst u
    simp [complementInput, hv]
  have hh := val_mono gates legal (singletonInput v) (complementInput S) hmono w ht
  rw [hf] at hh
  exact Bool.noConfusion hh

lemma charge_two_singletons {n : ℕ} (gates : List Gate)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (S : Finset (Fin n)) (j : Fin gates.length) (hj : j ∈ charges gates S) :
    ∃ r ∈ S, ∃ s ∈ S, r ≠ s ∧
      val gates (n + j.val) (singletonInput r) = true ∧
      val gates (n + j.val) (singletonInput s) = true := by
  classical
  have hm : Mrg gates S (complementInput S) singletonInput j :=
    (Finset.mem_filter.mp hj).2
  rcases hm with ⟨hop, hf, a, b, hab, r, hr, s, hs, ha, hb, X, hrX, hsX, hX⟩
  have hia : a ∈ (gates.get j).inputs := by rw [hab]; simp
  have hib : b ∈ (gates.get j).inputs := by rw [hab]; simp
  refine ⟨r, hr, s, hs, ?_, ?_, ?_⟩
  · intro he
    exact hsX (he ▸ hrX)
  · exact (val_or gates (singletonInput r) j.val j.isLt hop).2
      ⟨a, hia, hin j a hia, ha⟩
  · exact (val_or gates (singletonInput s) j.val j.isLt hop).2
      ⟨b, hib, hin j b hib, hb⟩

lemma charges_disjoint {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (S T : Finset (Fin n)) (hst : (S ∩ T).card ≤ 1) :
    Disjoint (charges gates S) (charges gates T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hjS hjT
  obtain ⟨r, hrS, s, hsS, hrs, hr, hs⟩ := charge_two_singletons gates hin S j hjS
  have hm : Mrg gates T (complementInput T) singletonInput j :=
    (Finset.mem_filter.mp hjT).2
  have hrT := singleton_mem_of_false_complement gates legal T _ r hm.2.1 hr
  have hsT := singleton_mem_of_false_complement gates legal T _ s hm.2.1 hs
  have hsub : ({r, s} : Finset (Fin n)) ⊆ S ∩ T := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_inter.mpr ⟨hrS, hrT⟩
    · have he : v = s := Finset.mem_singleton.mp hv
      subst v
      exact Finset.mem_inter.mpr ⟨hsS, hsT⟩
  have hcard := Finset.card_le_card hsub
  have hpair : ({r, s} : Finset (Fin n)).card = 2 := by simp [hrs]
  omega

lemma charges_card {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (S : Finset (Fin n)) (hne : 1 ≤ S.card) (output : ℕ)
    (hf : val gates output (complementInput S) = false)
    (ht : ∀ v ∈ S, val gates output (singletonInput v) = true) :
    (charges gates S).card = S.card - 1 := by
  classical
  have hone : ∀ p ∈ S, ∀ v, complementInput S v = false →
      singletonInput p v = true → v = p := by
    intro p hp v hv hsingle
    simpa [singletonInput] using hsingle
  simpa [charges, Finset.card_filter] using
    mcount gates S (complementInput S) singletonInput hone legal hin hne output hf ht

theorem exact_linear_output_bound {n : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (gates : List Gate) (targets : P → Finset (Fin n)) (outputs : P → ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (hne : ∀ p, 1 ≤ (targets p).card)
    (hlinear : ∀ p q, p ≠ q → ((targets p) ∩ (targets q)).card ≤ 1)
    (hcomplement : ∀ p, val gates (outputs p) (complementInput (targets p)) = false)
    (hsingleton : ∀ p, ∀ v ∈ targets p,
      val gates (outputs p) (singletonInput v) = true) :
    (∑ p, ((targets p).card - 1)) ≤
      {j : Fin gates.length | (gates.get j).op = GateOp.or}.ncard := by
  classical
  have hdis : (Finset.univ : Set P).PairwiseDisjoint (fun p => charges gates (targets p)) := by
    intro p hp q hq hpq
    exact charges_disjoint gates legal hin _ _ (hlinear p q hpq)
  have hsum : (∑ p, ((targets p).card - 1)) =
      (Finset.univ.biUnion fun p => charges gates (targets p)).card := by
    rw [Finset.card_biUnion hdis]
    exact Finset.sum_congr rfl fun p hp =>
      (charges_card gates legal hin (targets p) (hne p) (outputs p)
        (hcomplement p) (hsingleton p)).symm
  rw [hsum]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨p, hp, hjp⟩ := Finset.mem_biUnion.mp hj
  have hm : Mrg gates (targets p) (complementInput (targets p)) singletonInput j :=
    (Finset.mem_filter.mp hjp).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.1⟩

end PEqualNP.Outside.L_meta_1896_aux.ExactLinearOutputs
