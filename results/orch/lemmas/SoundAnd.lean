import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma graph_pair_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) : graphFun G ∅ (pairInput a b) = true ↔ G.Adj a b := by
  have hit (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simp [graphFun]
  rw [hit]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u = a ∨ u = b := by simpa [pairInput] using hu
    have hv' : v = a ∨ v = b := by simpa [pairInput] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact (huv.ne rfl).elim
    · exact huv
    · exact huv.symm
    · exact (huv.ne rfl).elim
  · intro h
    exact ⟨a, b, h, by simp [pairInput], by simp [pairInput]⟩

lemma literal_guard_sound_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p a b : Fin n) :
    (∀ x : Fin n → Bool, (x p && (x a || x b)) = true → graphFun G ∅ x = true) ↔
      G.Adj p a ∧ G.Adj p b := by
  constructor
  · intro h
    exact ⟨(graph_pair_true_iff G p a).mp (h _ (by simp [pairInput])),
      (graph_pair_true_iff G p b).mp (h _ (by simp [pairInput]))⟩
  · rintro ⟨hpa, hpb⟩ x hx
    have hx' : x p = true ∧ (x a = true ∨ x b = true) := by simpa using hx
    obtain ⟨hp, hab⟩ := hx'
    have hit : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      rcases hab with ha | hb
      · exact ⟨p, a, hpa, hp, ha⟩
      · exact ⟨p, b, hpb, hp, hb⟩
    simpa [graphFun] using hit

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) {a b p q : Fin n} (hab : a ≠ b)
    (hap : G.Adj a p) (hbp : G.Adj b p) (haq : G.Adj a q) (hbq : G.Adj b q) :
    p = q := by
  apply Finset.card_le_one.mp (hfour a b hab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hap, hbp⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haq, hbq⟩

lemma path_factor_guards {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : NoFourCycle G) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) :
    (∀ p : Fin n,
      (∀ x : Fin n → Bool, (x p && (x a || x b)) = true → graphFun G ∅ x = true) →
      p = c) ∧
    (∀ q : Fin n,
      (∀ x : Fin n → Bool, (x q && (x c || x d)) = true → graphFun G ∅ x = true) →
      q = a) ∧
    (∀ r : Fin n, ¬
      (∀ x : Fin n → Bool, (x r && (x a || x c)) = true → graphFun G ∅ x = true)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpa, hpb⟩ := (literal_guard_sound_iff G p a b).mp hp
    exact common_neighbor_unique G hfour hab hpa.symm hpb.symm hac hbc
  · intro q hq
    obtain ⟨hqc, hqd⟩ := (literal_guard_sound_iff G q c d).mp hq
    exact common_neighbor_unique G hfour hcd hqc.symm hqd.symm hac.symm had.symm
  · intro r hr
    obtain ⟨hra, hrc⟩ := (literal_guard_sound_iff G r a c).mp hr
    exact htri r a c hra hac hrc.symm

lemma mixed_guard_forcing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (f : (Fin n → Bool) → Bool)
    (hsound : ∀ x, (f x && (x a || x b)) = true → graphFun G ∅ x = true)
    {p : Fin n} (hforce : ∀ x, x p = true → f x = true) : G.Adj p a ∧ G.Adj p b := by
  apply (literal_guard_sound_iff G p a b).mp
  intro x hx
  have hx' : x p = true ∧ (x a || x b) = true := by simpa using hx
  apply hsound x
  simp [hforce x hx'.1, hx'.2]

lemma path_factor_forcing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : NoFourCycle G) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) :
    (∀ (f : (Fin n → Bool) → Bool),
      (∀ x, (f x && (x a || x b)) = true → graphFun G ∅ x = true) →
      ∀ p, (∀ x, x p = true → f x = true) → p = c) ∧
    (∀ (f : (Fin n → Bool) → Bool),
      (∀ x, (f x && (x c || x d)) = true → graphFun G ∅ x = true) →
      ∀ p, (∀ x, x p = true → f x = true) → p = a) ∧
    (∀ (f : (Fin n → Bool) → Bool),
      (∀ x, (f x && (x a || x c)) = true → graphFun G ∅ x = true) →
      ¬ ∃ p, ∀ x, x p = true → f x = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf p hp
    obtain ⟨hpa, hpb⟩ := mixed_guard_forcing G a b f hf hp
    exact common_neighbor_unique G hfour hab hpa.symm hpb.symm hac hbc
  · intro f hf p hp
    obtain ⟨hpc, hpd⟩ := mixed_guard_forcing G c d f hf hp
    exact common_neighbor_unique G hfour hcd hpc.symm hpd.symm hac.symm had.symm
  · rintro f hf ⟨p, hp⟩
    obtain ⟨hpa, hpc⟩ := mixed_guard_forcing G a c f hf hp
    exact htri p a c hpa hac hpc.symm

end PEqualNP.Outside.L_meta_1772_aux
