namespace PEqualNP.Outside.L_meta_3754.ExceptionalPair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma exceptional_alias_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (s : Fin n → Bool) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (g aW bW : ℕ) (v m : Fin n) (E : Strict3653.Exceptional G C s g aW bW v m)
    (j p : ℕ) (hjg : j<g)
    (hsem : PairPreserve.AliasSem n C P j p (bW-n) g v)
    (hout : C.output<n+C.gates.length)
    (hcones : ∀k<C.gates.length,InOutputCone n C k)
    (hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → i≠g → BelowF G C i)
    (hjv : gateVal n C j (Ledger.singletonInput v)=true) :
    wireVal n P C.output (pairInput v m)=true := by
  have hBg : bW-n<g := by have hb:=E.bBound;have hn:=E.bGate;omega
  have hbEq : n+(bW-n)=bW := by have hn:=E.bGate;omega
  have hBv : gateVal n C (bW-n) (Ledger.singletonInput v)=true := by
    have hb := (E.pureB (Ledger.singletonInput v)).mpr ⟨v,E.vInB,by simp [Ledger.singletonInput]⟩
    simpa only [gateVal,PEqualNP.ReadTwo.wval,hbEq] using hb
  have hgv : gateVal n C g (Ledger.singletonInput v)=true := by
    rw [E.gateProduct]
    have ha := (E.pureA (Ledger.singletonInput v)).mpr ⟨v,E.vInA,by simp [Ledger.singletonInput]⟩
    have hb := (E.pureB (Ledger.singletonInput v)).mpr ⟨v,E.vInB,by simp [Ledger.singletonInput]⟩
    rw [ha,hb]
    rfl
  have huniq : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g := by
    intro i hi hand hd
    by_contra hne
    exact hd (hunique i hi hand hne)
  obtain ⟨top,htop,hand,htg,hreader⟩ := E.mReader
  have hother : ∀b : Fin 2,m∈Strict3653.varSet n C g (opnd C top b) →
      wireVal n C (opnd C top b) (pairInput v m)=true := by
    intro b hm
    have hw := Ledger.operand_bound n C hC.1 top htop b
    have hd : ¬Strict3653.WireBelowF G C (opnd C top b) := by
      exact Bypass.least_no_and_below_operand hC htop hand
        (Strict3653.opnd_mem hC.1 htop b)
    have hh := (E.dirtyWireFormula (opnd C top b) (hw.trans (Nat.add_lt_add_left htop n)) hd
      (pairInput v m)).mpr (Or.inr ⟨m,hm,by simp [pairInput]⟩)
    exact hh
  have hreach : ∀b : Fin 2,Strict3653.usesG n C g (opnd C top b)=true →
      ∃k,opnd C top b=n+k ∧ k<C.gates.length ∧ (g=k ∨ InCone n C g k) := by
    intro b hb
    exact Strict3653.usesG_reach hC.1 g (opnd C top b)
      ((Ledger.operand_bound n C hC.1 top htop b).trans (Nat.add_lt_add_left htop n)) hb
  rcases hreader with ⟨h0,h1⟩ | ⟨h1,h0⟩
  · exact PairPreserve.alias_pair_from_reader G C P hC hfixed j p (bW-n) g v m hsem hjg hBg hout
      huniq top (hcones top htop) hand htg 0 1 (by decide) (hreach 0 h0) (hother 1 h1) hjv hBv hgv
  · exact PairPreserve.alias_pair_from_reader G C P hC hfixed j p (bW-n) g v m hsem hjg hBg hout
      huniq top (hcones top htop) hand htg 1 0 (by decide) (hreach 1 h1) (hother 0 h0) hjv hBv hgv

end PEqualNP.Outside.L_meta_3754.ExceptionalPair
