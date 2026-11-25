import PEqualNP.Outside.L_meta_2089

namespace PEqualNP.Outside.L_meta_2089.LinearBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Structural

def single {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => value C (single i) w = true)

lemma single_le {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hi : x i = true) :
    single i ≤ x := by
  intro j
  by_cases h : j = i
  · subst j
    simp [single, hi]
  · simp [single, h]

lemma private_quota {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (hmono : ∀ w, Monotone (fun x : Fin n → Bool => value C x w))
    (x : Fin n → Bool) (a : ℕ) (hoff : value C x a = false) :
    ∃ I : Finset ℕ, (support (n := n) C a).card ≤ I.card + 1 ∧
      ∀ i ∈ I, n ≤ i ∧ i < n + C.size ∧ i ≤ a ∧
        (gateAt C (i - n)).op = GateOp.or ∧ value C x i = false ∧
        2 ≤ (support (n := n) C i).card := by
  classical
  let G := (Finset.Ico n (n + C.size)).filter (fun w => value C x w = false)
  let O := G.filter (fun w => (gateAt C (w - n)).op = GateOp.or ∧
    2 ≤ (support (n := n) C w).card)
  let V : Option (Fin n) → ℕ → Bool := fun z w =>
    value C (z.elim x single) w
  have ginfo (w : ℕ) (hw : w ∈ G) :
      n ≤ w ∧ w < n + C.size ∧ value C x w = false := by
    simpa only [G, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hw
  have step (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ O then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, V none r = false) ∧
      ∀ y, (∀ r ∈ P, V y r = false) → V y w = false := by
    obtain ⟨hn, hlt, hx⟩ := ginfo w hw
    by_cases hs : 2 ≤ (support (n := n) C w).card
    · obtain ⟨P, hc, hb, hp, ht⟩ := gate_false_step C hm x w hn hlt hx
      have hweight : orCharge (gateAt C (w - n)).op = (if w ∈ O then 1 else 0) := by
        cases h : (gateAt C (w - n)).op <;> simp [orCharge, O, hw, hs, h]
      refine ⟨P, by simpa only [hweight] using hc, hb, hp, ?_⟩
      intro y hy
      exact ht (y.elim x single) hy
    · let P := (support (n := n) C w).image Fin.val
      refine ⟨P, ?_, ?_, ?_, ?_⟩
      · have hc := Finset.card_image_le (f := Fin.val) (s := support (n := n) C w)
        change P.card ≤ _ at hc
        omega
      · intro r hr
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
        omega
      · intro r hr
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        change value C x i.val = false
        rw [input_value]
        have htrue : value C (single i) w = true := (Finset.mem_filter.mp hi).2
        cases hxi : x i with
        | false => rfl
        | true =>
          have hle := hmono w (single_le x i hxi)
          change value C (single i) w ≤ value C x w at hle
          rw [htrue, hx] at hle
          exact Bool.noConfusion (Bool.eq_true_of_true_le hle)
      · intro y hy
        cases y with
        | none => exact hx
        | some i =>
          change value C (single i) w = false
          cases hv : value C (single i) w with
          | false => rfl
          | true =>
            have hi : i ∈ support (n := n) C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
            have hh := hy i.val (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
            change value C (single i) i.val = false at hh
            rw [input_value] at hh
            simp [single] at hh
  obtain ⟨B, hd, hc, hBx, hp⟩ := weighted_cut V none G O step (a + 1) {a}
    (by intro w hw _; obtain rfl := Finset.mem_singleton.mp hw; omega)
    (by intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact hoff)
  let I := O.filter (· < a + 1)
  let T := Finset.univ.filter (fun i : Fin n => i.val ∈ B)
  have hsub : support (n := n) C a ⊆ T := by
    intro i hi
    by_contra hn
    have hout : value C (single i) a = false := by
      apply hp (some i) ?_ a (by simp)
      intro w hw
      by_cases hwin : w < n
      · let j : Fin n := ⟨w, hwin⟩
        change value C (single i) j.val = false
        rw [input_value]
        have hne : j ≠ i := by
          intro h
          have : i.val ∈ B := h ▸ hw
          exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩)
        simp [single, hne]
      · by_cases htot : w < n + C.size
        · have hg : w ∈ G := Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨by omega, htot⟩, hBx w hw⟩
          exact (Finset.disjoint_left.mp hd hw hg).elim
        · exact missing_value C (single i) w (by omega)
    have hin : value C (single i) a = true := (Finset.mem_filter.mp hi).2
    exact Bool.noConfusion (hin.symm.trans hout)
  have hTc : T.card ≤ B.card := by
    rw [← Finset.card_image_of_injective T Fin.val_injective]
    apply Finset.card_le_card
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hi).2
  refine ⟨I, ?_, ?_⟩
  · have hBc : B.card ≤ I.card + 1 := by
      simpa only [Finset.card_singleton, I, Nat.add_comm] using hc
    exact (Finset.card_le_card hsub).trans (hTc.trans hBc)
  · intro i hi
    obtain ⟨hO, hia⟩ := Finset.mem_filter.mp hi
    obtain ⟨hG, hop, hs⟩ := Finset.mem_filter.mp hO
    obtain ⟨hni, hlt, hx⟩ := ginfo i hG
    exact ⟨hni, hlt, by omega, hop, hx, hs⟩

end PEqualNP.Outside.L_meta_2089.LinearBound
