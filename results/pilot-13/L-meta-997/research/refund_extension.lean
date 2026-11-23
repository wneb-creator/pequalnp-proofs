
namespace PEqualNP.Outside.L_meta_997.Refund

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.light

lemma refund_output_count {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n))
    (hlinear : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)).card ≤
      (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i)))).card := by
  classical
  let I := Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  let R := Finset.univ.filter (fun g : Fin C.gates.length =>
    (∃ i : Fin m, ∀ p : Fin n,
      value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
    (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
      (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i)))
  have hsingle (i : Fin m) (p : Fin n) :
      value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
    rw [hcorrect]
    simp
  have hsupp (i : Fin m) : singleSupp C (o i) = S i := by
    ext p
    rw [mem_singleSupp]
    exact hsingle i p
  have hgate (i : Fin m) (hi : i ∈ I) : n ≤ o i ∧ o i < n + C.gates.length := by
    have hc := (Finset.mem_filter.mp hi).2.2
    have h := singleSupp_gate C (o i) (by rwa [hsupp])
    exact h
  have hheavy (i : Fin m) (hd : Disjoint (S i) y) (p : Fin n) :
      value C (fun v => decide (v ∈ y ∨ v = p)) (o i) = true ↔ p ∈ S i := by
    rw [hcorrect]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hqy | rfl⟩
      · exact False.elim (Finset.disjoint_left.mp hd hq hqy)
      · exact hq
    · intro hp
      exact ⟨p, hp, Or.inr rfl⟩
  let f (i : {i // i ∈ I}) : Fin C.gates.length :=
    ⟨o i.val - n, by have := hgate i.val i.property; omega⟩
  have hwire (i : {i // i ∈ I}) : n + (f i).val = o i.val := by
    have := hgate i.val i.property
    dsimp [f]
    omega
  have hf (i : {i // i ∈ I}) : f i ∈ R := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · refine ⟨i.val, ?_⟩
      intro p
      rw [hwire]
      exact hsingle i.val p
    · have hd := (Finset.mem_filter.mp i.property).2.1
      refine ⟨i.val, hd, ?_⟩
      intro p _
      rw [hwire]
      exact hheavy i.val hd p
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have ho : o i.val = o j.val := by
      rw [← hwire i, ← hwire j, hij]
    have hs : S i.val = S j.val := by
      rw [← hsupp i.val, ← hsupp j.val, ho]
    have hcross := hlinear i.val j.val hne
    rw [← hs, Finset.inter_self] at hcross
    have hc := (Finset.mem_filter.mp i.property).2.2
    omega
  have hcard := Fintype.card_le_of_injective
    (fun i : {i // i ∈ I} => (⟨f i, hf i⟩ : {g // g ∈ R}))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  simpa only [Fintype.card_coe] using hcard

end PEqualNP.Outside.L_meta_997.Refund
