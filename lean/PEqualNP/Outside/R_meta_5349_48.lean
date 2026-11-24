import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_5349_48
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (raw : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsAO2 n C →
      (G.edgeFinset.filter fun e => ∃ u v : Fin n, e = s(u,v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
          (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
          (u ∈ side C g 1 ∨ v ∈ side C g 1)).card ≤ 27*C.size)
    (obstruction : ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → TopForm G C →
      ∀ (T : Finset (Sym2 (Fin n))) (u v : Sym2 (Fin n) → Fin n)
        (a g : Sym2 (Fin n) → ℕ) (b : Sym2 (Fin n) → Fin 2),
      (∀ e ∈ T, e ∈ Ustar G C ∧ e = s(u e,v e) ∧ a e ∈ tops G C ∧ g e ∈ junk G C ∧
        u e ∈ side C (a e) (b e) ∧ OrReaches n C (opnd C (a e) (1-b e)) (g e) ∧
        gateVal n C (g e) (pairInput (u e) (v e)) = true) →
      (∀ (w : Fin n), ∀ e ∈ T, ∀ d ∈ T, v e = v d →
        w ∈ side C (a e) (1-b e) → w ∈ side C (a d) (1-b d) → e = d) →
      T.Nonempty → (∃ e ∈ T, ∃ u' v' : Fin n, e = s(u',v') ∧
        ∃ a' ∈ tops G C, ∃ b' : Fin 2, ∃ g' ∈ junk G C,
          u' ∈ side C a' b' ∧ OrReaches n C (opnd C a' (1-b')) g' ∧
          (u' ∈ side C g' 0 ∨ v' ∈ side C g' 0) ∧
          (u' ∈ side C g' 1 ∨ v' ∈ side C g' 1)) ∨
        ∃ e ∈ T, ∃ f ∈ [fun z => (u z).val,fun z => (v z).val,fun z => 2*a z+(b z).val,g],
          (T.filter fun z => f z = f e).card ≤ d) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ (x9 : Finset (Sym2 (Fin x2))) (x10 x11 : Sym2 (Fin x2) → Fin x2) (x12 x13 : Sym2 (Fin x2) → ℕ) (x14 : Sym2 (Fin x2) → Fin (2 : ℕ)), (∀ x15 ∈ x9, x15 ∈ PEqualNP.TopForm.Ustar x3 x5 ∧ x15 = s(x10 x15, x11 x15) ∧ x12 x15 ∈ PEqualNP.TopForm.tops x3 x5 ∧ x13 x15 ∈ PEqualNP.TopForm.junk x3 x5 ∧ x10 x15 ∈ PEqualNP.TopForm.side x5 (x12 x15) (x14 x15) ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 (x12 x15) ((1 : Fin (2 : ℕ)) - x14 x15)) (x13 x15) ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 (x13 x15) (PEqualNP.EdgeOwnership.pairInput (x10 x15) (x11 x15)) = Bool.true) → (∀ x16 ∈ x9, ∀ x18 ∈ [fun (x19 : Sym2 (Fin x2)) => ↑(x10 x19), fun (x19 : Sym2 (Fin x2)) => ↑(x11 x19), fun (x19 : Sym2 (Fin x2)) => (2 : ℕ) * x12 x19 + ↑(x14 x19), x13], (3 : ℕ) ≤ {x20 ∈ x9 | x18 x20 = x18 x16}.card) → (∀ (x17 : Fin x2), ∀ x18 ∈ x9, ∀ x20 ∈ x9, x11 x18 = x11 x20 → x17 ∈ PEqualNP.TopForm.side x5 (x12 x18) ((1 : Fin (2 : ℕ)) - x14 x18) → x17 ∈ PEqualNP.TopForm.side x5 (x12 x20) ((1 : Fin (2 : ℕ)) - x14 x20) → x18 = x20) → x9.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  obtain ⟨d,hob⟩ := obstruction
  refine ⟨27+5*d,?_⟩
  intro n G inst C hcy hleast htop S u v a g b hw _ hDisj
  let E := G.edgeFinset.filter fun e => ∃ u v : Fin n, e = s(u,v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1-b)) g ∧
      (u ∈ side C g 0 ∨ v ∈ side C g 0) ∧
      (u ∈ side C g 1 ∨ v ∈ side C g 1)
  have hE : E.card ≤ 27*C.size := raw n G C hcy hleast.1
  let label : Fin 4 → Sym2 (Fin n) → ℕ :=
    ![fun e => (u e).val,fun e => (v e).val,fun e => 2*a e+(b e).val,g]
  let V := G.support.toFinset.image Fin.val
  let ranges : Fin 4 → Finset ℕ := ![V,V,Finset.range (2*C.size),Finset.range C.size]
  let R := (Finset.univ : Finset (Fin 4)).sigma ranges
  have cap : R.card ≤ 5*(C.size+1) := by
    have hV : V.card ≤ C.size+1 := by
      apply Finset.card_image_le.trans
      have he := (Set.ncard_eq_toFinset_card' G.support).symm
      rw [he]
      exact support n G C hleast
    change ((Finset.univ : Finset (Fin 4)).sigma ranges).card ≤ _
    rw [Finset.card_sigma,Fin.sum_univ_four]
    change V.card + V.card + (Finset.range (2*C.size)).card + (Finset.range C.size).card ≤ _
    simp only [Finset.card_range]
    omega
  have allowed (e) (he : e ∈ S) (j : Fin 4) : (⟨j,label j e⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ R := by
    obtain ⟨hu,heq,ht,hj,_,_,_⟩ := hw e he
    have hAdj : G.Adj (u e) (v e) := by
      have hm := (Finset.mem_sdiff.mp hu).1
      rw [heq] at hm
      exact G.mem_edgeFinset.mp hm
    have hU : (u e).val ∈ V := Finset.mem_image.mpr ⟨u e,by simpa using (show u e ∈ G.support from ⟨_,hAdj⟩),rfl⟩
    have hV : (v e).val ∈ V := Finset.mem_image.mpr ⟨v e,by simpa using (show v e ∈ G.support from ⟨_,hAdj.symm⟩),rfl⟩
    have index {P : ℕ → Prop} {dec : DecidablePred P} {i : ℕ}
        (h : i ∈ @gatesWhere C P dec) : i < C.size := by
      exact Finset.mem_range.mp (Finset.mem_filter.mp (show i ∈ (Finset.range C.size).filter P from h)).1
    have hA : a e < C.size := index ht
    have hG : g e < C.size := index hj
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    fin_cases j
    · exact hU
    · exact hV
    · apply Finset.mem_range.mpr
      change 2*a e + (b e).val < 2*C.size
      have := (b e).isLt
      omega
    · exact Finset.mem_range.mpr hG
  have peel (m : ℕ) : ∀ (P : Finset (Sigma (fun _ : Fin 4 => ℕ))) (A : Finset (Sym2 (Fin n))),
      P.card = m → A ⊆ S \ E →
      (∀ e ∈ A, ∀ j, (⟨j,label j e⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ P) →
      A.card ≤ d*P.card := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro P A hm hAS hp
      by_cases hne : A.Nonempty
      swap
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
      have low : ∃ e ∈ A, ∃ j : Fin 4, (A.filter fun z => label j z = label j e).card ≤ d := by
        have hA : A ⊆ S := hAS.trans Finset.sdiff_subset
        rcases hob n G C hcy hleast htop A u v a g b
          (fun e he => hw e (hA he))
          (fun w e he t ht => hDisj w e (hA he) t (hA ht)) hne with hraw | hfew
        · obtain ⟨e,he,u',v',heq,a',ha',b',g',hg',hu',hr',h0,h1⟩ := hraw
          have hedge : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp (hw e (hA he)).1).1
          have hraw : e ∈ E := Finset.mem_filter.mpr
            ⟨hedge,u',v',heq,a',ha',b',g',hg',hu',hr',h0,h1⟩
          exact ((Finset.mem_sdiff.mp (hAS he)).2 hraw).elim
        · obtain ⟨e,he,f,hf,hfew⟩ := hfew
          refine ⟨e,he,?_⟩
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
          rcases hf with rfl|rfl|rfl|rfl
          · exact ⟨0,hfew⟩
          · exact ⟨1,hfew⟩
          · exact ⟨2,hfew⟩
          · exact ⟨3,hfew⟩
      obtain ⟨e,he,j,hfew⟩ := low
      let B := A.filter fun z => label j z = label j e
      let r : Sigma (fun _ : Fin 4 => ℕ) := ⟨j,label j e⟩
      have hr : r ∈ P := hp e he j
      have hlt : (P.erase r).card < m := hm ▸ Finset.card_erase_lt_of_mem hr
      have rem (z) (hz : z ∈ A \ B) (i) : (⟨i,label i z⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ P.erase r := by
        obtain ⟨hza,hzb⟩ := Finset.mem_sdiff.mp hz
        apply Finset.mem_erase.mpr
        refine ⟨?_,hp z hza i⟩
        intro eq
        have ij : i = j := congrArg Sigma.fst eq
        subst i
        have same : label j z = label j e := congrArg (fun p : Sigma (fun _ : Fin 4 => ℕ) => p.2) eq
        exact hzb (Finset.mem_filter.mpr ⟨hza,same⟩)
      have hsize := ih _ hlt (P.erase r) (A \ B) rfl (Finset.sdiff_subset.trans hAS) rem
      have hsum := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun z => label j z = label j e) A)
      change (A \ B).card + B.card = A.card at hsum
      change B.card ≤ d at hfew
      have hcount : P.card = (P.erase r).card+1 := by
        have := Finset.card_erase_add_one hr
        omega
      rw [hcount,Nat.mul_add,Nat.mul_one]
      omega
  have hPaid := peel R.card R (S \ E) rfl Finset.Subset.rfl
    (fun e he => allowed e (Finset.mem_sdiff.mp he).1)
  have hPaid' : (S \ E).card ≤ 5*d*(C.size+1) := by
    calc (S \ E).card ≤ d*R.card := hPaid
      _ ≤ d*(5*(C.size+1)) := Nat.mul_le_mul_left _ cap
      _ = 5*d*(C.size+1) := by ring
  have hcover : S ⊆ (S \ E) ∪ E := by
    intro e he
    by_cases h : e ∈ E
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  have hsize := (Finset.card_le_card hcover).trans (Finset.card_union_le (S \ E) E)
  nlinarith
