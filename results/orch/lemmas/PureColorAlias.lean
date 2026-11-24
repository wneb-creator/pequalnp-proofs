import PEqualNP.Outside.L_meta_2584

namespace PEqualNP.Outside.L_meta_2584

namespace UpwardErase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma overwrite_val_ge {n : ℕ} {C : Circuit} (hAO : AndOrOnly C)
    (j : ℕ) (r : Gate) (x : Fin n → Bool)
    (hrep : val C (List.ofFn x) (n + j) = true → replacementVal n C j r x = true)
    (w : ℕ) : val C (List.ofFn x) w = true →
      val (overwriteCircuit C j r) (List.ofFn x) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
      exact id
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C j r).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      by_cases hjk : j = k
      · subst k
        rw [overwriteCircuit_val_self C hk r x]
        exact hrep
      have he : gateAt (overwriteCircuit C j r) k = gateAt C k :=
        overwriteCircuit_gateAt_other C j k hjk r
      rcases hAO _ (gateAt_mem hk) with hand | hor
      · rw [val_and (n := n) (by simp) hk hand,
          val_and (n := n) (by simp) hk' (by rw [he]; exact hand), he]
        intro hv i hi
        exact ⟨(hv i hi).1, ih i (hv i hi).1 (hv i hi).2⟩
      · rw [val_or (n := n) (by simp) hk hor,
          val_or (n := n) (by simp) hk' (by rw [he]; exact hor), he]
        rintro ⟨i, hi, hlt, hv⟩
        exact ⟨i, hi, hlt, ih i hlt hv⟩
    · rw [val_ge (n := n) (by simp) (by omega)]
      simp

lemma upward_or_context_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (g e : ℕ) (r : Gate)
    (hrval : ∀ x : Fin n → Bool, replacementVal n C g r x = val C (List.ofFn x) e)
    (hfront : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w g →
      ∃ v ∈ (gateAt C j).inputs, ¬ OrReaches n C v g ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) e = true →
          val C (List.ofFn x) v = true → graphFun G ∅ x = true)
    (x : Fin n → Bool) (hfalse : graphFun G ∅ x = false) (w : ℕ) :
    val (overwriteCircuit C g r) (List.ofFn x) w = true →
      val C (List.ofFn x) w = true ∨
        (OrReaches n C w g ∧ val C (List.ofFn x) e = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
      exact Or.inl
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C g r).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      by_cases hgk : g = k
      · subst k
        rw [overwriteCircuit_val_self C hk r x, hrval]
        intro hv
        exact Or.inr ⟨(orReaches_iff n C g g).mpr ⟨hk, Or.inl rfl⟩, hv⟩
      have he : gateAt (overwriteCircuit C g r) k = gateAt C k :=
        overwriteCircuit_gateAt_other C g k hgk r
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · rw [val_and (n := n) (by simp) hk' (by rw [he]; exact hand), he]
        intro hv
        left
        apply (val_and (n := n) (by simp) hk hand).mpr
        intro i hi
        have hilt := hAO.2.1 k hk i hi
        refine ⟨hilt, ?_⟩
        rcases ih i hilt (hv i hi).2 with hold | ⟨hr, hetrue⟩
        · exact hold
        · obtain ⟨v, hvin, hvnot, hsound⟩ := hfront k hk hand i hi hr
          have hvlt := hAO.2.1 k hk v hvin
          have hvold : val C (List.ofFn x) v = true := by
            rcases ih v hvlt (hv v hvin).2 with hvold | ⟨hvr, _⟩
            · exact hvold
            · exact False.elim (hvnot hvr)
          have hyes := hsound x hetrue hvold
          rw [hfalse] at hyes
          cases hyes
      · rw [val_or (n := n) (by simp) hk' (by rw [he]; exact hor), he]
        rintro ⟨i, hi, hilt, hiv⟩
        rcases ih i hilt hiv with hold | ⟨hr, hetrue⟩
        · exact Or.inl ((val_or (n := n) (by simp) hk hor).mpr ⟨i, hi, hilt, hold⟩)
        · exact Or.inr ⟨(orReaches_iff n C k g).mpr
            ⟨hk, Or.inr ⟨hor, i, hi, hilt, hr⟩⟩, hetrue⟩
    · rw [val_ge (n := n) (by simp) (by rw [overwriteCircuit_length]; omega)]
      simp

lemma erase_and_with_frontier_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅)
    (g e : ℕ) (hg : g < C.gates.length) (hgand : (gateAt C g).op = GateOp.and)
    (he : e ∈ (gateAt C g).inputs)
    (hout : ¬ OrReaches n C C.output g)
    (hfront : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w g →
      ∃ v ∈ (gateAt C j).inputs, ¬ OrReaches n C v g ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) e = true →
          val C (List.ofFn x) v = true → graphFun G ∅ x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  let r : Gate := ⟨GateOp.or, [e, e]⟩
  let E := overwriteCircuit C g r
  have helt : e < n + g := hAO.2.1 g hg e he
  have hrback : ∀ i ∈ r.inputs, i < n + g := by
    intro i hi
    simp only [r, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    simpa [hi] using helt
  have hrval (x : Fin n → Bool) : replacementVal n C g r x = val C (List.ofFn x) e := by
    rw [replacementVal_of_readsBack C g r x hrback]
    simp [r, GateOp.eval]
  have hE : IsAO2 n E := overwriteCircuit_isAO2 hAO g r (Or.inr rfl) hrback rfl
  have hge (x : Fin n → Bool) (w : ℕ) : val C (List.ofFn x) w = true →
      val E (List.ofFn x) w = true := by
    apply overwrite_val_ge hAO.1 g r x _ w
    rw [hrval]
    intro hv
    exact ((val_and (n := n) (by simp) hg hgand).mp hv e he).2
  have hEf : circuitFun n E = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      cases hF : graphFun G ∅ x with
      | true => rfl
      | false =>
        have hv := upward_or_context_bound G C hAO g e r hrval hfront x hF C.output hx
        rcases hv with hold | ⟨hr, _⟩
        · change circuitFun n C x = true at hold
          rw [hf, hF] at hold
          cases hold
        · exact False.elim (hout hr)
    · intro hx
      apply hge x C.output
      change circuitFun n C x = true
      rw [hf]
      exact hx
  have hgate (x : Fin n → Bool) : gateVal n E g x = val E (List.ofFn x) e := by
    change val (overwriteCircuit C g r) (List.ofFn x) (n + g) = _
    rw [overwriteCircuit_val_self C hg r x, hrval,
      overwriteCircuit_val_before C g r x e helt]
  obtain ⟨D, hD, hsize, hDf⟩ := MinimumPure.erase_equivalent_wire E hE
    (by simpa only [E, overwriteCircuit_length] using hg) helt hgate
  refine ⟨D, hD, ?_, hDf.trans hEf⟩
  simpa only [E, overwriteCircuit_size] using hsize

end UpwardErase

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

namespace PureColorFrontier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma selected_factor_frontier_guard {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h p q e : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hg : g < C.gates.length) (hga : (gateAt C g).op = GateOp.and)
    (hgin : (gateAt C g).inputs = [p, q]) (hgdirty : ¬ BelowF G C g)
    (hHpure : ∀ v ∈ (gateAt C h).inputs, ∀ k, OrReaches n C v k →
      (gateAt C k).op = GateOp.or)
    (epure : ∀ k, OrReaches n C e k → (gateAt C k).op = GateOp.or)
    (hEH : ∀ x, val C (List.ofFn x) e = true → gateVal n C h x = true →
      graphFun G ∅ x = true)
    (hneigh : ∀ v : Fin n, (∀ t ∈ orIn n C p ∩ orIn n C q, G.Adj t v) →
      ∀ u ∈ orIn n C e, G.Adj u v) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w g →
      ∃ v ∈ (gateAt C j).inputs, ¬ OrReaches n C v g ∧
        ∀ x, val C (List.ofFn x) e = true → val C (List.ofFn x) v = true →
          graphFun G ∅ x = true := by
  intro j hj hja w hw hr
  have hgj : g < j := by
    have := orReaches_wire_le hr
    have := hAO.2.1 j hj w hw
    omega
  have hjclean : BelowF G C j := by
    by_contra hdirty
    rcases honly j hj hja hdirty with he | he
    · omega
    · subst j
      have hgo := hHpure w hw g hr
      rw [hga] at hgo
      cases hgo
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
  obtain ⟨v, hvin, hcover⟩ : ∃ v ∈ (gateAt C j).inputs,
      ∀ t ∈ (gateAt C j).inputs, t = w ∨ t = v := by
    have hw' := hw
    rw [hin] at hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with hwa | hwb
    · refine ⟨b, by rw [hin]; simp, ?_⟩
      intro t ht
      have he : t = a ∨ t = b := by
        simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using ht
      exact he.imp (fun he => he.trans hwa.symm) id
    · refine ⟨a, by rw [hin]; simp, ?_⟩
      intro t ht
      have he : t = a ∨ t = b := by
        simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using ht
      exact he.symm.imp (fun he => he.trans hwb.symm) id
  have hvg : ¬ OrReaches n C v g := by
    intro hvr
    apply hgdirty
    intro x hx
    apply hjclean x
    apply (val_and (n := n) (by simp) hj hja).mpr
    intro t ht
    refine ⟨hAO.2.1 j hj t ht, ?_⟩
    rcases hcover t ht with he | he
    · rw [he]
      exact orStep_up (by simp) (orReaches_reach g w hr).1 hx
    · rw [he]
      exact orStep_up (by simp) (orReaches_reach g v hvr).1 hx
  refine ⟨v, hvin, hvg, ?_⟩
  intro x hex hvx
  rcases val_true_or_frontier hAO x v hvx with ⟨u, hu, hxu⟩ | ⟨k, hk, hka, hkr, hkx⟩
  · have hcommon : ∀ t ∈ orIn n C p ∩ orIn n C q, G.Adj t u := by
      intro t ht
      have hgt := common_or_input_implies_and hAO.2.1 hg hga hgin ht
        (pairInput t u) (pairInput_left t u)
      have hwt : val C (List.ofFn (pairInput t u)) w = true :=
        orStep_up (by simp) (orReaches_reach g w hr).1 hgt
      have hvt : val C (List.ofFn (pairInput t u)) v = true :=
        orIn_value hu _ (pairInput_right t u)
      apply (graphFun_pair G t u).mp
      apply hjclean (pairInput t u)
      apply (val_and (n := n) (by simp) hj hja).mpr
      intro z hz
      refine ⟨hAO.2.1 j hj z hz, ?_⟩
      rcases hcover z hz with rfl | rfl
      · exact hwt
      · exact hvt
    obtain ⟨t, ht, hxt⟩ := (pure_or_value_iff epure x).mp hex
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨t, u, hneigh u hcommon t ht, hxt, hxu⟩
  · have hkdirty : ¬ BelowF G C k := by
      intro hkclean
      apply hTop k hk j hj hka hkclean hja
      obtain ⟨l, hl, he, hcone⟩ := orReaches_gate_ancestor hkr
      have hlt := hAO.2.1 j hj v hvin
      exact (FlatRead.inCone_iff n C k j).mpr
        ⟨hj, l, by omega, by simpa only [he] using hvin, hcone⟩
    rcases honly k hk hka hkdirty with rfl | rfl
    · exact False.elim (hvg hkr)
    · exact hEH x hex hkx

lemma dirty_not_output_or_path {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hf : circuitFun n C = graphFun G ∅)
    (g : ℕ) (hgdirty : ¬ BelowF G C g) : ¬ OrReaches n C C.output g := by
  intro hr
  apply hgdirty
  intro x hx
  rw [← hf]
  exact orStep_up (by simp) (orReaches_reach g C.output hr).1 hx

end PureColorFrontier

namespace PureColorFrontier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership Sharing

lemma erase_two_dirty_pure_colors {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hf : circuitFun n C = graphFun G ∅) (hTop : TopForm G C) (hfour : NoFourCycle G)
    (g h p q c d : ℕ) (hg : g < C.gates.length) (hh : h < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hhand : (gateAt C h).op = GateOp.and)
    (hgin : (gateAt C g).inputs = [p, q]) (hhin : (gateAt C h).inputs = [c, d])
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hgdirty : ¬ BelowF G C g) (hhdirty : ¬ BelowF G C h)
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
    (hblock : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  obtain ⟨e, he, hEH, hneigh⟩ := PureColorFactor.choose_wire_factor G C hAO hfour
    g h p q c d hg hh hgand hhand hgin hhin ppure qpure cpure dpure
    S pS qS cS dS hSS hLL hlarge hhdirty hblock
  have heinput : e ∈ (gateAt C g).inputs := by
    rw [hgin]
    rcases he with rfl | rfl <;> simp
  have epure : ∀ k, OrReaches n C e k → (gateAt C k).op = GateOp.or := by
    rcases he with rfl | rfl
    · exact ppure
    · exact qpure
  have hHpure : ∀ v ∈ (gateAt C h).inputs, ∀ k, OrReaches n C v k →
      (gateAt C k).op = GateOp.or := by
    intro v hv
    rw [hhin] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact cpure
    · exact dpure
  exact UpwardErase.erase_and_with_frontier_guard G C hAO hf g e hg hgand heinput
    (dirty_not_output_or_path G C hf g hgdirty)
    (selected_factor_frontier_guard G C hAO hTop g h p q e honly hg hgand hgin
      hgdirty hHpure epure hEH hneigh)

end PureColorFrontier

end PEqualNP.Outside.L_meta_2584
