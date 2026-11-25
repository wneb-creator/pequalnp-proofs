import Mathlib


namespace PEqualNP.Outside.L_meta_4675.ReaderCharge

lemma nonstar_reader_shape {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 1 < Q.card) (hB : 1 < B.card)
    (hAQ : (A ∩ Q).Nonempty) (hP : P.Nonempty)
    (hbase : ∀ q ∈ Q, ∀ b ∈ P, (q, b) ∈ E)
    (hprod : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E)
    (hdirty : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∉ E) :
    ∃ (b0 b1 : Fin l) (q0 : Fin p),
      b0 ≠ b1 ∧ P = {b0} ∧ B = {b0, b1} ∧ A ∩ Q = {q0} ∧
      (∀ a ∈ A, (a, b1) ∈ E) ∧ (∀ q ∈ Q, (q, b0) ∈ E) ∧
      (∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ↔ b = b1 ∨ a = q0 ∧ b = b0) := by
  obtain ⟨a0, ha0, b0, hb0, hbad⟩ := hdirty
  obtain ⟨q0, hq0⟩ := hAQ
  obtain ⟨hq0A, hq0Q⟩ := Finset.mem_inter.mp hq0
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp hQ
  have hQ0 : ∀ z ∈ Q, (z, b0) ∈ E := by
    intro z hz
    exact (hprod a0 ha0 b0 hb0 z hz).resolve_left hbad
  have hP0 : P = {b0} := by
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    refine ⟨hP, ?_⟩
    intro b hb
    by_contra hbb
    exact hC4 q r b b0 hqr hbb
      ⟨hbase q hq b hb, hQ0 q hq, hbase r hr b hb, hQ0 r hr⟩
  have hother : ∀ b ∈ B, b ≠ b0 → ∀ a ∈ A, (a, b) ∈ E := by
    intro b hb hbb a ha
    by_contra hab
    have hqb := (hprod a ha b hb q hq).resolve_left hab
    have hrb := (hprod a ha b hb r hr).resolve_left hab
    exact hC4 q r b b0 hqr hbb ⟨hqb, hQ0 q hq, hrb, hQ0 r hr⟩
  have ha0q : a0 ≠ q0 := by
    intro he
    subst a0
    exact hbad (hQ0 q0 hq0Q)
  obtain ⟨b1, hb1, hb10⟩ : ∃ b1 ∈ B, b1 ≠ b0 := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB
    by_cases hu0 : u = b0
    · exact ⟨v, hv, fun hv0 => huv (hu0.trans hv0.symm)⟩
    · exact ⟨u, hu, hu0⟩
  have hB01 : B = {b0, b1} := by
    apply Finset.Subset.antisymm
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hb00 : b = b0
      · exact Or.inl hb00
      · right
        by_contra hb11
        exact hC4 a0 q0 b b1 ha0q hb11
          ⟨hother b hb hb00 a0 ha0, hother b1 hb1 hb10 a0 ha0,
            hother b hb hb00 q0 hq0A, hother b1 hb1 hb10 q0 hq0A⟩
    · exact Finset.insert_subset hb0 (Finset.singleton_subset_iff.mpr hb1)
  have hAQ0 : A ∩ Q = {q0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨hq0A, hq0Q⟩, ?_⟩
    intro a ha
    obtain ⟨haA, haQ⟩ := Finset.mem_inter.mp ha
    by_contra haq
    exact hC4 a q0 b0 b1 haq hb10.symm
      ⟨hQ0 a haQ, hother b1 hb1 hb10 a haA,
        hQ0 q0 hq0Q, hother b1 hb1 hb10 q0 hq0A⟩
  refine ⟨b0, b1, q0, hb10.symm, hP0, hB01, hAQ0,
    hother b1 hb1 hb10, hQ0, ?_⟩
  intro a ha b hb
  constructor
  · intro hab
    have hbb : b = b0 ∨ b = b1 := by simpa [hB01] using hb
    rcases hbb with hb0eq | hb1eq
    · right
      refine ⟨?_, hb0eq⟩
      rw [hb0eq] at hab
      by_contra haq
      exact hC4 a q0 b0 b1 haq hb10.symm
        ⟨hab, hother b1 hb1 hb10 a ha,
          hQ0 q0 hq0Q, hother b1 hb1 hb10 q0 hq0A⟩
    · exact Or.inl hb1eq
  · rintro (hb1eq | ⟨haq, hb0eq⟩)
    · rw [hb1eq]
      exact hother b1 hb1 hb10 a ha
    · rw [haq, hb0eq]
      exact hQ0 q0 hq0Q

end PEqualNP.Outside.L_meta_4675.ReaderCharge


namespace PEqualNP.Outside.L_meta_4675.RestoreStar

def pairVal {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (v : α ⊕ β) : Bool :=
  decide (v = Sum.inl a ∨ v = Sum.inr b)

def graphValue {α β : Type*} (E : Finset (α × β)) (x : α ⊕ β → Bool) : Prop :=
  ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true

lemma pairVal_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (x : α ⊕ β → Bool) (a : α) (b : β)
    (ha : x (Sum.inl a) = true) (hb : x (Sum.inr b) = true) :
    ∀ v, pairVal a b v = true → x v = true := by
  intro v hv
  simp only [pairVal, decide_eq_true_eq] at hv
  rcases hv with hv | hv
  · simpa [hv] using ha
  · simpa [hv] using hb

lemma false_prune_restore_star {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A : Finset α) (B : Finset β)
    (b0 b1 : β) (q0 : α) (F0 : (α ⊕ β → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) →
      F0 x = true → F0 y = true)
    (hbelow : ∀ x, F0 x = true → graphValue E x)
    (houtside : ∀ a b, (a, b) ∈ E → (a ∉ A ∨ b ∉ B) →
      F0 (pairVal a b) = true)
    (hexception : F0 (pairVal q0 b0) = true)
    (hshape : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E →
      b = b1 ∨ a = q0 ∧ b = b0)
    (hcolumn : ∀ a ∈ A, (a, b1) ∈ E) :
    ∀ x, graphValue E x ↔
      F0 x = true ∨ (∃ a ∈ A, x (Sum.inl a) = true) ∧ x (Sum.inr b1) = true := by
  intro x
  constructor
  · rintro ⟨a, b, hab, hxa, hxb⟩
    by_cases ha : a ∈ A
    · by_cases hb : b ∈ B
      · rcases hshape a ha b hb hab with hb1 | ⟨ha0, hb0⟩
        · exact Or.inr ⟨⟨a, ha, hxa⟩, hb1 ▸ hxb⟩
        · apply Or.inl
          apply hmono (pairVal q0 b0) x
          · apply pairVal_le
            · simpa [ha0] using hxa
            · simpa [hb0] using hxb
          · exact hexception
      · exact Or.inl (hmono (pairVal a b) x (pairVal_le x a b hxa hxb)
          (houtside a b hab (Or.inr hb)))
    · exact Or.inl (hmono (pairVal a b) x (pairVal_le x a b hxa hxb)
        (houtside a b hab (Or.inl ha)))
  · rintro (hx | ⟨⟨a, ha, hxa⟩, hxb⟩)
    · exact hbelow x hx
    · exact ⟨a, b1, hcolumn a ha, hxa, hxb⟩

end PEqualNP.Outside.L_meta_4675.RestoreStar

namespace PEqualNP.Outside.L_meta_4675.NonstarRepair

open PEqualNP.Outside.L_meta_4675.RestoreStar

lemma nonstar_rectangle_repair {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 1 < Q.card) (hB : 1 < B.card)
    (hAQ : (A ∩ Q).Nonempty) (hP : P.Nonempty)
    (hbase : ∀ q ∈ Q, ∀ b ∈ P, (q,b) ∈ E)
    (hprod : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a,b) ∈ E ∨ (q,b) ∈ E)
    (hdirty : ∃ a ∈ A, ∃ b ∈ B, (a,b) ∉ E)
    (F0 : (Fin p ⊕ Fin l → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) → F0 x = true → F0 y = true)
    (hbelow : ∀ x, F0 x = true → graphValue E x)
    (houtside : ∀ a b, (a,b) ∈ E → (a ∉ A ∨ b ∉ B) → F0 (pairVal a b) = true)
    (hbasePreserved : ∀ q ∈ Q, ∀ b ∈ P, F0 (pairVal q b) = true) :
    ∃ b1 : Fin l, (∀ a ∈ A, (a,b1) ∈ E) ∧
      ∀ x, graphValue E x ↔
        F0 x = true ∨ (∃ a ∈ A, x (Sum.inl a) = true) ∧ x (Sum.inr b1) = true := by
  obtain ⟨b0,b1,q0,_,hP0,_,hAQ0,hcol,_,hshape⟩ :=
    PEqualNP.Outside.L_meta_4675.ReaderCharge.nonstar_reader_shape
      E hC4 A Q B P hQ hB hAQ hP hbase hprod hdirty
  have hq0 : q0 ∈ Q := by
    have hm : q0 ∈ A ∩ Q := by rw [hAQ0]; simp
    exact (Finset.mem_inter.mp hm).2
  have hb0 : b0 ∈ P := by rw [hP0]; simp
  exact ⟨b1,hcol,false_prune_restore_star E A B b0 b1 q0 F0 hmono hbelow houtside
    (hbasePreserved q0 hq0 b0 hb0) (fun a ha b hb hab => (hshape a ha b hb).mp hab) hcol⟩

end PEqualNP.Outside.L_meta_4675.NonstarRepair
