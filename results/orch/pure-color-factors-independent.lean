import PEqualNP.Outside.L_meta_2584
namespace PEqualNP.Outside.L_meta_2584.PureFactorReview
namespace PureColorFactor
open PEqualNP.TopForm

lemma choose_shared_factor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hfour : NoFourCycle G)
    (hAB : 2 ≤ (A ∩ B).card)
    (hsound : ∀ d ∈ D, ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C,
      G.Adj a d ∨ G.Adj b d ∨ G.Adj c d)
    (hdirty : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d) :
    ∃ E : Finset (Fin n), (E = A ∨ E = B) ∧
      (∀ d ∈ D, (∀ e ∈ E, G.Adj e d) ∨ (∀ c ∈ C, G.Adj c d)) ∧
      ∀ v : Fin n, (∀ p ∈ A ∩ B, G.Adj p v) → ∀ e ∈ E, G.Adj e v := by
  classical
  obtain ⟨c, hc, m, hm, hcm⟩ := hdirty
  have hmcover := TwoJunkStructure.point_factors_cover_line G.Adj A B C m (hsound m hm)
  have hmAB : (∀ a ∈ A, G.Adj a m) ∨ (∀ b ∈ B, G.Adj b m) := by
    rcases hmcover with hA | hB | hC
    · exact Or.inl hA
    · exact Or.inr hB
    · exact False.elim (hcm (hC c hc))
  obtain ⟨E, hE, hEm⟩ : ∃ E : Finset (Fin n),
      (E = A ∨ E = B) ∧ ∀ e ∈ E, G.Adj e m := by
    rcases hmAB with hA | hB
    · exact ⟨A, Or.inl rfl, hA⟩
    · exact ⟨B, Or.inr rfl, hB⟩
  have hTm : ∀ p ∈ A ∩ B, G.Adj p m := by
    intro p hp
    rcases hE with rfl | rfl
    · exact hEm p (Finset.mem_inter.mp hp).1
    · exact hEm p (Finset.mem_inter.mp hp).2
  have hunique : ∀ v : Fin n, (∀ p ∈ A ∩ B, G.Adj p v) → v = m := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ B).card)
    by_contra hvm
    have hsmall := hfour a b hab
    have hlarge : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card := by
      apply Finset.one_lt_card.mpr
      exact ⟨v, by simp [hv a ha, hv b hb], m, by simp [hTm a ha, hTm b hb], hvm⟩
    omega
  refine ⟨E, hE, ?_, ?_⟩
  · intro d hd
    rcases TwoJunkStructure.point_factors_cover_line G.Adj A B C d (hsound d hd)
      with hA | hB | hC
    · left
      have he := hunique d (fun p hp => hA p (Finset.mem_inter.mp hp).1)
      simpa only [he] using hEm
    · left
      have he := hunique d (fun p hp => hB p (Finset.mem_inter.mp hp).2)
      simpa only [he] using hEm
    · exact Or.inr hC
  · intro v hv
    simpa only [hunique v hv] using hEm

end PureColorFactor

namespace PureColorFactor
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership Sharing

lemma pair_gate_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j p q : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [p, q]) (x : Fin n → Bool) :
    gateVal n C j x = true ↔
      val C (List.ofFn x) p = true ∧ val C (List.ofFn x) q = true := by
  have hp : p < n + j := hAO.2.1 j hj p (by rw [hin]; simp)
  have hq : q < n + j := hAO.2.1 j hj q (by rw [hin]; simp)
  rw [gateVal_eq_val, val_and (by simp) hj hand]
  simp [hin, hp, hq]

lemma graph_of_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) {u v : Fin n} (huv : G.Adj u v)
    (hu : x u = true) (hv : x v = true) : graphFun G ∅ x = true := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, v, huv, hu, hv⟩

lemma choose_wire_factor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    (g h p q c d : ℕ) (hg : g < C.gates.length) (hh : h < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hhand : (gateAt C h).op = GateOp.and)
    (hgin : (gateAt C g).inputs = [p, q]) (hhin : (gateAt C h).inputs = [c, d])
    (ppure : ∀ j, OrReaches n C p j → (gateAt C j).op = GateOp.or)
    (qpure : ∀ j, OrReaches n C q j → (gateAt C j).op = GateOp.or)
    (cpure : ∀ j, OrReaches n C c j → (gateAt C j).op = GateOp.or)
    (dpure : ∀ j, OrReaches n C d j → (gateAt C j).op = GateOp.or)
    (S : Fin n → Prop) (pS : ∀ u ∈ orIn n C p, S u)
    (qS : ∀ u ∈ orIn n C q, S u) (cS : ∀ u ∈ orIn n C c, S u)
    (dS : ∀ u ∈ orIn n C d, ¬ S u)
    (hSS : ∀ u v, S u → S v → ¬ G.Adj u v)
    (hLL : ∀ u v, ¬ S u → ¬ S v → ¬ G.Adj u v)
    (hlarge : 2 ≤ (orIn n C p ∩ orIn n C q).card)
    (hdirty : ¬ BelowF G C h)
    (hblock : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true) :
    ∃ e : ℕ, (e = p ∨ e = q) ∧
      (∀ x : Fin n → Bool, val C (List.ofFn x) e = true →
        gateVal n C h x = true → graphFun G ∅ x = true) ∧
      ∀ v : Fin n, (∀ u ∈ orIn n C p ∩ orIn n C q, G.Adj u v) →
        ∀ u ∈ orIn n C e, G.Adj u v := by
  classical
  have hcover : ∀ l ∈ orIn n C d, ∀ a ∈ orIn n C p,
      ∀ b ∈ orIn n C q, ∀ f ∈ orIn n C c,
      G.Adj a l ∨ G.Adj b l ∨ G.Adj f l := by
    intro l hl a ha b hb f hf
    let x : Fin n → Bool := fun u => decide (u = a ∨ u = b ∨ u = f ∨ u = l)
    have hxa : x a = true := by simp [x]
    have hxb : x b = true := by simp [x]
    have hxf : x f = true := by simp [x]
    have hxl : x l = true := by simp [x]
    have hv := hblock x
      ((pair_gate_true hAO hg hgand hgin x).mpr ⟨orIn_value ha x hxa, orIn_value hb x hxb⟩)
      ((pair_gate_true hAO hh hhand hhin x).mpr ⟨orIn_value hf x hxf, orIn_value hl x hxl⟩)
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hv
    obtain ⟨u, v, huv, hu, hv⟩ := hv
    have hu' : u = a ∨ u = b ∨ u = f ∨ u = l := by simpa [x] using hu
    have hv' : v = a ∨ v = b ∨ v = f ∨ v = l := by simpa [x] using hv
    have haS := pS a ha
    have hbS := qS b hb
    have hfS := cS f hf
    have hlS := dS l hl
    rcases hu' with rfl | rfl | rfl | rfl <;>
      rcases hv' with rfl | rfl | rfl | rfl
    all_goals first | exact False.elim (hSS _ _ (by assumption) (by assumption) huv)
                    | exact False.elim (hLL _ _ (by assumption) (by assumption) huv)
                    | exact Or.inl huv
                    | exact Or.inr (Or.inl huv)
                    | exact Or.inr (Or.inr huv)
                    | exact Or.inl huv.symm
                    | exact Or.inr (Or.inl huv.symm)
                    | exact Or.inr (Or.inr huv.symm)
  have hbad : ∃ f ∈ orIn n C c, ∃ l ∈ orIn n C d, ¬ G.Adj f l := by
    by_contra hbad
    push Not at hbad
    apply hdirty
    intro x hx
    obtain ⟨hc, hd⟩ := (pair_gate_true hAO hh hhand hhin x).mp hx
    obtain ⟨f, hf, hxf⟩ := (pure_or_value_iff cpure x).mp hc
    obtain ⟨l, hl, hxl⟩ := (pure_or_value_iff dpure x).mp hd
    exact graph_of_pair G x (hbad f hf l hl) hxf hxl
  obtain ⟨E, hE, hED, hguard⟩ := choose_shared_factor G (orIn n C p) (orIn n C q)
    (orIn n C c) (orIn n C d) hfour hlarge hcover hbad
  obtain ⟨e, he, heE, hepure⟩ : ∃ e : ℕ, (e = p ∨ e = q) ∧ orIn n C e = E ∧
      (∀ j, OrReaches n C e j → (gateAt C j).op = GateOp.or) := by
    rcases hE with rfl | rfl
    · exact ⟨p, Or.inl rfl, rfl, ppure⟩
    · exact ⟨q, Or.inr rfl, rfl, qpure⟩
  refine ⟨e, he, ?_, ?_⟩
  · intro x hex hhx
    obtain ⟨u, hu, hxu⟩ := (pure_or_value_iff hepure x).mp hex
    obtain ⟨hc, hd⟩ := (pair_gate_true hAO hh hhand hhin x).mp hhx
    obtain ⟨f, hf, hxf⟩ := (pure_or_value_iff cpure x).mp hc
    obtain ⟨l, hl, hxl⟩ := (pure_or_value_iff dpure x).mp hd
    rcases hED l hl with hE | hC
    · exact graph_of_pair G x (hE u (heE ▸ hu)) hxu hxl
    · exact graph_of_pair G x (hC f hf) hxf hxl
  · intro v hv u hu
    exact hguard v hv u (heE ▸ hu)

end PureColorFactor

end PEqualNP.Outside.L_meta_2584.PureFactorReview
