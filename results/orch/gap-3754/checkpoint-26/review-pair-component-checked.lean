namespace PEqualNP.Outside.L_meta_3754.PairPreserve
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

def AliasSem (n : ℕ) (C P : Circuit) (j p B g : ℕ) (v : Fin n) : Prop :=
  ∀(x : Fin n → Bool) k,k<C.gates.length →
    wireVal n P (n+k) x=if k=g ∨ k=B then x v else if k=j then wireVal n P p x else
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n P u x)

lemma opnd_mem (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ)
    (hk : k<C.gates.length) (b : Fin 2) : opnd C k b∈(gateAt C k).inputs := by
  obtain ⟨a,c,hac⟩ := Ledger.gate_two n C hAO k hk
  fin_cases b <;> simp [opnd,hac]

lemma noimp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (k : ℕ) (hk : k<C.gates.length)
    (hand : (gateAt C k).op=GateOp.and) (b : Fin 2) :
    ¬∀x : Fin n → Bool,wireVal n C (opnd C k b) x=true → graphFun G ∅ x=true := by
  exact Bypass.least_no_and_below_operand hC hk hand (opnd_mem n C hC.1 k hk b)

lemma least_or_after_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (top : ℕ) (hbelow : BelowF G C top) (k : ℕ) (hcone : InOutputCone n C k)
    (hanc : InCone n C top k) : (gateAt C k).op=GateOp.or := by
  have hm : gateAt C k∈C.gates := by rw [Ledger.gateAt_eq_getElem C k hcone.1];exact List.getElem_mem hcone.1
  rcases hC.1.1 _ hm with hand | hor
  · exact (Ledger.no_clean_and_ancestor G C hC.1 hfixed k hcone
      (noimp G C hC k hcone.1 hand) top hanc hbelow).elim
  · exact hor

lemma alias_unique_forward (n : ℕ) (C P : Circuit) (hAO : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hsem : AliasSem n C P j p B g v)
    (hjg : j<g) (hBg : B<g) (top : ℕ) (htop : top<C.gates.length)
    (hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → i=g)
    (x : Fin n → Bool) (hv : x v=true) :
    ∀k,InCone n C k top → (g=k ∨ InCone n C g k) → wireVal n P (n+k) x=true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hkTop hreach
    have hk : k<C.gates.length := (Ledger.inCone_lt n C k top htop hkTop).trans htop
    by_cases hkg : k=g
    · rw [hsem x k hk,if_pos (Or.inl hkg),hv]
    have hgk : g<k := by
      rcases hreach with he | he
      · exact (hkg he.symm).elim
      · exact Ledger.inCone_lt n C g k hk he
    have hor : (gateAt C k).op=GateOp.or := by
      have hm : gateAt C k∈C.gates := by rw [Ledger.gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rcases hAO.1 _ hm with hand | hor
      · exact (hkg (hall k hkTop hand)).elim
      · exact hor
    have hanc : InCone n C g k := hreach.resolve_left (Ne.symm hkg)
    obtain ⟨w,hw,hnw,hwk,hgw⟩ := (Ledger.inCone_iff n C g k hk).mp hanc
    have hwcone : InCone n C (w-n) k :=
      (Ledger.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hnw,hwk,Or.inl rfl⟩
    have hvw := ih (w-n) (by omega) (Ledger.inCone_trans n C (w-n) k top htop hwcone hkTop) hgw
    rw [hsem x k hk,if_neg (by omega),if_neg (by omega),hor]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    exact ⟨w,hw,by simpa only [show n+(w-n)=w by omega] using hvw⟩

lemma alias_clean_to_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (j p B g : ℕ) (v : Fin n) (hsem : AliasSem n C P j p B g v)
    (top : ℕ) (hcone : InOutputCone n C top) (hbelow : BelowF G C top)
    (hjtop : j<top) (hBtop : B<top) (hgtop : g<top)
    (hout : C.output<n+C.gates.length) (x : Fin n → Bool)
    (ht : wireVal n P (n+top) x=true) : wireVal n P C.output x=true := by
  have hup : ∀k,InOutputCone n C k → (k=top ∨ InCone n C top k) → wireVal n P (n+k) x=true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hkcone hreach
      rcases hreach with rfl | hreach
      · exact ht
      have htk := Ledger.inCone_lt n C top k hkcone.1 hreach
      have hor := least_or_after_clean G C hC hfixed top hbelow k hkcone hreach
      obtain ⟨w,hw,hnw,hwk,htw⟩ := (Ledger.inCone_iff n C top k hkcone.1).mp hreach
      have hwcone : InCone n C (w-n) k :=
        (Ledger.inCone_iff n C (w-n) k hkcone.1).mpr ⟨w,hw,hnw,hwk,Or.inl rfl⟩
      have hvw := ih (w-n) (by omega) (Ledger.output_cone_ancestor n C (w-n) k hkcone hwcone)
        (htw.imp_left Eq.symm)
      rw [hsem x k hkcone.1,if_neg (by omega),if_neg (by omega),hor]
      simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
      exact ⟨w,hw,by simpa only [show n+(w-n)=w by omega] using hvw⟩
  rcases hcone.2 with ho | ⟨hno,ho⟩
  · simpa only [ho] using ht
  · have hk : C.output-n<C.gates.length := by omega
    have hc : InOutputCone n C (C.output-n) := ⟨hk,Or.inl (by omega)⟩
    have hh := hup (C.output-n) hc (Or.inr ho)
    simpa only [show n+(C.output-n)=C.output by omega] using hh

lemma alias_pair_from_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (j p B g : ℕ) (v m : Fin n) (hsem : AliasSem n C P j p B g v)
    (hjg : j<g) (hBg : B<g) (hout : C.output<n+C.gates.length)
    (hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g)
    (top : ℕ) (hcone : InOutputCone n C top) (hand : (gateAt C top).op=GateOp.and)
    (htg : top≠g) (used other : Fin 2) (hne : used≠other)
    (hreach : ∃k,opnd C top used=n+k ∧ k<C.gates.length ∧ (g=k ∨ InCone n C g k))
    (hother : wireVal n C (opnd C top other) (pairInput v m)=true)
    (hjv : gateVal n C j (Ledger.singletonInput v)=true)
    (hBv : gateVal n C B (Ledger.singletonInput v)=true)
    (hgv : gateVal n C g (Ledger.singletonInput v)=true) :
    wireVal n P C.output (pairInput v m)=true := by
  have hbelow : BelowF G C top := by
    by_contra hn
    exact htg (hunique top hcone.1 hand hn)
  have hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → i=g := by
    intro i hi hiAND
    have hil := (Ledger.inCone_lt n C i top hcone.1 hi).trans hcone.1
    exact hunique i hil hiAND (Ledger.no_clean_and_ancestor G C hC.1 hfixed top hcone
      (noimp G C hC top hcone.1 hand) i hi)
  have hallTrue : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and →
      gateVal n C i (Ledger.singletonInput v)=true := by
    intro i hi hiAND
    simpa only [hall i hi hiAND] using hgv
  obtain ⟨k,hwk,hk,hgk⟩ := hreach
  have hkw := Ledger.operand_bound n C hC.1 top hcone.1 used
  have hkTop : InCone n C k top :=
    (Ledger.inCone_iff n C k top hcone.1).mpr
      ⟨opnd C top used,opnd_mem n C hC.1 top hcone.1 used,by omega,hkw,Or.inl (by omega)⟩
  have hgtop : g<top := by
    have hkt := Ledger.inCone_lt n C k top hcone.1 hkTop
    rcases hgk with he | he
    · omega
    · have := Ledger.inCone_lt n C g k hk he
      omega
  have hused : wireVal n C (opnd C top used) (Ledger.singletonInput v)=true := by
    have hh := Ledger.ancestor_truth_if_and_true n C hC.1 top hcone.1
      (Ledger.singletonInput v) hallTrue k hkTop g hgv hgk
    simpa only [hwk,gateVal,wireVal] using hh
  have hcases : ∀b : Fin 2,b=used ∨ b=other := by
    intro b
    fin_cases b <;> fin_cases used <;> fin_cases other <;> simp_all
  have hfalse : wireVal n C (opnd C top other) (Ledger.singletonInput v)=false := by
    cases hh : wireVal n C (opnd C top other) (Ledger.singletonInput v)
    · rfl
    · have hb : ∀b : Fin 2,wireVal n C (opnd C top b) (Ledger.singletonInput v)=true := by
        intro b
        rcases hcases b with rfl | rfl <;> assumption
      have ht : gateVal n C top (Ledger.singletonInput v)=true := by
        rw [Ledger.gate_and_value n C hC.1 top hcone.1 hand,hb 0,hb 1]
        rfl
      have hf := hbelow _ ht
      have hz : graphFun G ∅ (Ledger.singletonInput v)=false := by simp [graphFun,Ledger.singletonInput]
      rw [hz] at hf
      cases hf
  have hagree := Ledger.alias_agree_on_false_operand n C P hC.1 j p B g v hsem
    top hcone.1 (Ledger.singletonInput v) hallTrue other hfalse hjv hBv hgv
  have hotherP : wireVal n P (opnd C top other) (pairInput v m)=true := by
    rw [hagree];exact hother
  have husedP : wireVal n P (opnd C top used) (pairInput v m)=true := by
    rw [hwk]
    exact alias_unique_forward n C P hC.1 j p B g v hsem hjg hBg top hcone.1 hall
      (pairInput v m) (by simp [pairInput]) k hkTop hgk
  have hbP : ∀b : Fin 2,wireVal n P (opnd C top b) (pairInput v m)=true := by
    intro b
    rcases hcases b with rfl | rfl <;> assumption
  have htP : wireVal n P (n+top) (pairInput v m)=true := by
    rw [hsem _ top hcone.1,if_neg (by omega),if_neg (by omega),hand]
    obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hC.1 top hcone.1
    have ha : wireVal n P a (pairInput v m)=true := by simpa [opnd,hab] using hbP 0
    have hb : wireVal n P b (pairInput v m)=true := by simpa [opnd,hab] using hbP 1
    simp [hab,GateOp.eval,ha,hb]
  exact alias_clean_to_output G C P hC hfixed j p B g v hsem top hcone hbelow
    (by omega) (by omega) hgtop hout (pairInput v m) htP

end PEqualNP.Outside.L_meta_3754.PairPreserve
