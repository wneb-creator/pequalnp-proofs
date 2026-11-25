import PEqualNP.Outside.L_meta_3754

namespace PEqualNP.Outside.L_meta_3754.CriticalBypass
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.SplitCount PEqualNP.EdgeOwnership Bypass

lemma eval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀i,x i=true → y i=true) :
    C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true := by
  exact Semantic.val_monotone C.gates hAO.1 x y hxy C.output

lemma bypass_diff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {r i : ℕ}
    (hr : r<C.gates.length) (hi : i<n+r) :
    ∃x : Fin n → Bool,(bypass n C r i).eval (List.ofFn x)≠graphFun G ∅ x := by
  by_contra h
  push Not at h
  have heq : circuitFun n (bypass n C r i)=graphFun G ∅ := funext h
  have hc := hL.2.2 _ (isAO2_bypass hL.1 hi) heq
  change C.gates.length≤(bypass n C r i).gates.length at hc
  rw [bypass_length] at hc
  omega

lemma opMono_rev : OpMono (fun a b => b=true → a=true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma or_bypass_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {r i : ℕ}
    (hr : r<C.gates.length) (hop : (gateAt C r).op=GateOp.or)
    (him : i∈(gateAt C r).inputs) (x : Fin n → Bool) :
    (bypass n C r i).eval (List.ofFn x)=true → C.eval (List.ofFn x)=true := by
  have hi := hAO.2.1 r hr i him
  apply bypass_eval_rel (R:=fun a b=>b=true → a=true) (fun _ h=>h) opMono_rev
    (by simp) (fun k hk=>hAO.1 _ (gateAt_mem hk)) hr (Or.inl hi)
  intro hv
  exact (val_or (by simp) hr hop).mpr ⟨i,him,hi,hv⟩

lemma and_bypass_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {r i : ℕ}
    (hr : r<C.gates.length) (hop : (gateAt C r).op=GateOp.and)
    (him : i∈(gateAt C r).inputs) (x : Fin n → Bool) :
    C.eval (List.ofFn x)=true → (bypass n C r i).eval (List.ofFn x)=true := by
  have hi := hAO.2.1 r hr i him
  apply bypass_eval_rel (R:=fun a b=>a=true → b=true) (fun _ h=>h) opMono_imp
    (by simp) (fun k hk=>hAO.1 _ (gateAt_mem hk)) hr (Or.inl hi)
  intro hv
  exact ((val_and (by simp) hr hop).mp hv i him).2

lemma least_or_operand_loses_edge {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C) {r i : ℕ}
    (hr : r<C.gates.length) (hop : (gateAt C r).op=GateOp.or)
    (him : i∈(gateAt C r).inputs) :
    ∃u v : Fin n,G.Adj u v ∧
      (bypass n C r i).eval (List.ofFn (pairInput u v))=false := by
  have hi := hL.1.2.1 r hr i him
  obtain ⟨x,hx⟩ := bypass_diff hL hr hi
  have hle := or_bypass_le hL.1 hr hop him x
  have hc := congrFun hL.2.1 x
  change C.eval (List.ofFn x)=graphFun G ∅ x at hc
  have hF : graphFun G ∅ x=true := by
    cases hf : graphFun G ∅ x <;> cases hd : (bypass n C r i).eval (List.ofFn x) <;> simp_all
  have hD : (bypass n C r i).eval (List.ofFn x)=false := by
    cases hd : (bypass n C r i).eval (List.ofFn x) <;> simp_all
  have hedge : ∃u v : Fin n,G.Adj u v ∧ x u=true ∧ x v=true := by
    simpa [graphFun] using hF
  obtain ⟨u,v,huv,hu,hv⟩ := hedge
  refine ⟨u,v,huv,?_⟩
  by_contra he
  have ht : (bypass n C r i).eval (List.ofFn (pairInput u v))=true := by simpa using he
  have hm := eval_mono (isAO2_bypass hL.1 hi) (pairInput u v) x (by
    intro z hz
    simp only [pairInput,decide_eq_true_eq] at hz
    rcases hz with rfl | rfl <;> assumption) ht
  rw [hD] at hm
  cases hm

lemma extend_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (hx : graphFun G ∅ x=false) :
    ∃y : Fin n → Bool,(∀i,x i=true → y i=true) ∧ graphFun G ∅ y=false ∧
      ∀i,y i=false → graphFun G ∅ (Function.update y i true)=true := by
  classical
  let S : Finset (Fin n → Bool) := Finset.univ.filter fun y=>
    graphFun G ∅ y=false ∧ ∀i,x i=true → y i=true
  let weight (y : Fin n → Bool) := (Finset.univ.filter fun i=>y i=true).card
  have hS : S.Nonempty := ⟨x,by simp [S,hx]⟩
  obtain ⟨y,hy,hmax⟩ := Finset.exists_max_image S weight hS
  have hys := (Finset.mem_filter.mp hy).2
  refine ⟨y,hys.2,hys.1,?_⟩
  intro i hi
  by_contra hbad
  have hbad' : graphFun G ∅ (Function.update y i true)=false := by simpa using hbad
  have hup : Function.update y i true∈S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hbad',?_⟩
    intro j hj
    by_cases hji : j=i
    · subst j;simp
    · simpa [Function.update_of_ne hji] using hys.2 j hj
  have hcard := hmax _ hup
  have heq : (Finset.univ.filter fun j=>Function.update y i true j=true)=
      insert i (Finset.univ.filter fun j=>y j=true) := by
    ext j
    by_cases hji : j=i
    · subst j;simp
    · simp [hji]
  have hnot : i∉Finset.univ.filter (fun j=>y j=true) := by simp [hi]
  dsimp [weight] at hcard
  rw [heq,Finset.card_insert_of_notMem hnot] at hcard
  omega

lemma least_and_operand_accepts_max_false {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C) {r i : ℕ}
    (hr : r<C.gates.length) (hop : (gateAt C r).op=GateOp.and)
    (him : i∈(gateAt C r).inputs) :
    ∃x : Fin n → Bool,graphFun G ∅ x=false ∧
      (bypass n C r i).eval (List.ofFn x)=true ∧
      ∀j,x j=false → graphFun G ∅ (Function.update x j true)=true := by
  have hi := hL.1.2.1 r hr i him
  obtain ⟨x,hx⟩ := bypass_diff hL hr hi
  have hge := and_bypass_ge hL.1 hr hop him x
  have hc := congrFun hL.2.1 x
  change C.eval (List.ofFn x)=graphFun G ∅ x at hc
  have hF : graphFun G ∅ x=false := by
    cases hf : graphFun G ∅ x <;> cases hd : (bypass n C r i).eval (List.ofFn x) <;> simp_all
  have hD : (bypass n C r i).eval (List.ofFn x)=true := by
    cases hd : (bypass n C r i).eval (List.ofFn x) <;> simp_all
  obtain ⟨y,hxy,hy,hymax⟩ := extend_false G x hF
  exact ⟨y,hy,eval_mono (isAO2_bypass hL.1 hi) x y hxy hD,hymax⟩

end PEqualNP.Outside.L_meta_3754.CriticalBypass
