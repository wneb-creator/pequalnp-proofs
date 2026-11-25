import PNPAccepted6659

namespace PEqualNP.Outside.L_meta_6659_aux

lemma single_reader_path_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : Relation.ReflTransGen (sem_step n D) a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))

lemma single_reader_chain_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : sem_Chain n D a b) : a ≤ b :=
  single_reader_path_le hS (sem_rtg_mono (fun _ _ h => h.1) path)

lemma single_reader_other_unreachable {n : ℕ} {D : Dag} (hS : Strict n D)
    {v a b c : ℕ} (chain : sem_Chain n D v a)
    (last : sem_step n D a b) (one : fanout D a = 1)
    (other : sem_step n D c b) (different : c ≠ a) :
    ¬ Relation.ReflTransGen (sem_step n D) v c := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,first,rest⟩
    · exact different equal.symm
    · have same : b = z := sem_step_unique last first one
      have le := single_reader_path_le hS rest
      have lt := sem_step_lt hS other
      omega
  | @head start next first rest ih =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,initial,remaining⟩
    · have direct : sem_step n D start b := by simpa [equal] using other
      have same : next = b := sem_step_unique first.1 direct first.2
      have le := single_reader_chain_le hS rest
      have lt := sem_step_lt hS last
      omega
    · have same : next = z := sem_step_unique first.1 initial first.2
      subst z
      exact ih remaining

lemma single_reader_chain_hits {n : ℕ} {D : Dag} (hS : Strict n D)
    {a b : ℕ} (chain : sem_Chain n D a b) (P : ℕ → Prop) :
    ∀ w, Relation.ReflTransGen (fun u v => sem_step n D u v ∧ P v) a w →
      P a → b ≤ w → P b := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl => intro w path start bound; exact start
  | @head a next step rest ih =>
    intro w path start bound
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨z,first,remaining⟩
    · have increasing := sem_step_lt hS step.1
      have restLe := single_reader_chain_le hS rest
      omega
    · have same : next = z := sem_step_unique step.1 first.1 step.2
      subst z
      exact ih w remaining first.2 bound

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma consuming_changed_path {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k) (target : Nat)
    (changed : val D x target ≠ val D y target) (absent : i ∉ supp n D target) :
    ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
        (n+e.1) target := by
  have first : ∀ {a b : Nat},
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) a b →
      i ∈ supp n D a → i ∉ supp n D b →
      ∃ e ∈ sem_W n D i, val D x (n+e.1) ≠ val D y (n+e.1) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b)
          (n+e.1) b := by
    intro a b path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => intro present absent; exact False.elim (absent present)
    | @head a c step rest ih =>
      intro present absent
      by_cases next : i ∈ supp n D c
      · exact ih next absent
      · obtain ⟨j,s,hj,rfl,source⟩ := sem_step_iff.mp step.1
        refine ⟨(j,s),sem_mem_W.mpr ⟨hj,?_,next⟩,step.2,rest⟩
        rw [source]
        exact present
  apply first (sem_changed_path hS x y i inputs target changed) _ absent
  rw [supp_input D i]
  exact Finset.mem_singleton_self i

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma consumer_chain_cut {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g barrier : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (chain : sem_Chain n D (n+g) barrier)
    (same : val D (single u) barrier = val D (sem_ins i (single u)) barrier) :
    ∀ target, barrier ≤ target → i ∉ supp n D target →
      val D (single u) target = val D (sem_ins i (single u)) target := by
  have inputs := sem_ins_agree i (single u)
  have blocked : ∀ target, barrier ≤ target →
      val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g) →
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧
        val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+g) target → False := by
    intro target bound changed path
    exact (single_reader_chain_hits hS chain
      (fun w => val D (single u) w ≠ val D (sem_ins i (single u)) w)
      target path changed bound) same
  have hj := (sem_mem_W.mp he).1
  have childZero : val D (single u) (src D (sem_bar e)) = false := by
    cases value : val D (single u) (src D (sem_bar e)) with
    | false => rfl
    | true =>
      have member := mem_supp.mpr value
      rw [empty] at member
      exact False.elim (Finset.notMem_empty u member)
  have parentPath : val D (single u) (n+e.1) ≠ val D (sem_ins i (single u)) (n+e.1) →
      (val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g)) ∧
        Relation.ReflTransGen (fun a b => sem_step n D a b ∧
          val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+g) (n+e.1) := by
    intro parentChanged
    have childChanged : val D (single u) (src D (sem_bar e)) ≠
        val D (sem_ins i (single u)) (src D (sem_bar e)) := by
      intro childSame
      have zero : ∀ x : Fin n → Bool, val D x (src D (sem_bar e)) = false →
          val D x (n+e.1) = false := by
        intro x hx
        rw [val_gate hS x e.1 hj,sem_W_and hS he]
        obtain ⟨j,s⟩ := e
        cases s <;> simp only [sem_bar,src,Bool.not_false,Bool.not_true,ite_true,
          Bool.false_eq_true,ite_false] at hx ⊢ <;> simp [gop,hx]
      exact parentChanged ((zero _ childZero).trans
        (zero _ (childSame.symm.trans childZero)).symm)
    obtain ⟨f,hf,changed,path⟩ := consuming_changed_path hS (single u)
      (sem_ins i (single u)) i inputs (src D (sem_bar e)) childChanged
      (by rw [empty]; exact Finset.notMem_empty i)
    rcases two f hf with fromG | fromE
    · have initial : val D (single u) (n+g) ≠ val D (sem_ins i (single u)) (n+g) := by
        simpa only [fromG] using changed
      have toChild : Relation.ReflTransGen (fun a b => sem_step n D a b ∧
          val D (single u) b ≠ val D (sem_ins i (single u)) b)
          (n+g) (src D (sem_bar e)) := by simpa only [fromG] using path
      exact ⟨initial,Relation.ReflTransGen.tail toChild ⟨sem_step_src hj (!e.2),parentChanged⟩⟩
    · have backward := sem_rtg_le hS (fun _ _ step => step.1) path
      have before := sem_src_lt hS hj (!e.2)
      change src D (sem_bar e) < n+e.1 at before
      omega
  intro target bound absent
  by_contra changed
  obtain ⟨f,hf,initial,path⟩ := consuming_changed_path hS (single u)
    (sem_ins i (single u)) i inputs target changed absent
  rcases two f hf with fromG | fromE
  · apply blocked target bound
    · simpa only [fromG] using initial
    · simpa only [fromG] using path
  · have changedE : val D (single u) (n+e.1) ≠ val D (sem_ins i (single u)) (n+e.1) := by
      simpa only [fromE] using initial
    obtain ⟨changedG,toE⟩ := parentPath changedE
    have fromEPath : Relation.ReflTransGen (fun a b => sem_step n D a b ∧
        val D (single u) b ≠ val D (sem_ins i (single u)) b) (n+e.1) target := by
      simpa only [fromE] using path
    exact blocked target bound changedG (toE.trans fromEPath)

lemma consumer_barrier_true {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g barrier : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (chain : sem_Chain n D (n+g) barrier)
    (target : Nat) (after : barrier ≤ target) (absent : i ∉ supp n D target)
    (baseZero : val D (single u) target = false)
    (positive : val D (sem_ins i (single u)) target = true) :
    val D (sem_ins i (single u)) barrier = true := by
  cases value : val D (sem_ins i (single u)) barrier with
  | true => rfl
  | false =>
    have baseFalse : val D (single u) barrier = false := by
      cases base : val D (single u) barrier with
      | false => rfl
      | true =>
        have raised := val_mono hS (single u) (sem_ins i (single u))
          (sem_ins_ge i (single u)) barrier base
        rw [value] at raised
        exact False.elim (Bool.noConfusion raised)
    have same := consumer_chain_cut hS i u e he empty g barrier two chain
      (baseFalse.trans value.symm) target after absent
    rw [baseZero,positive] at same
    exact False.elim (Bool.noConfusion same)

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma consuming_ancestors_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k)
    (target : Nat)
    (consumers : ∀ e ∈ sem_W n D i,
      Relation.ReflTransGen (sem_step n D) (n + e.1) target →
      val D x (n + e.1) = val D y (n + e.1)) :
    i ∉ supp n D target → val D x target = val D y target := by
  have aux : ∀ w, Relation.ReflTransGen (sem_step n D) w target →
      i ∉ supp n D w → val D x w = val D y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro reach absent
      by_cases input : w < n
      · rw [supp_input D ⟨w,input⟩] at absent
        have ne : (⟨w,input⟩ : Fin n) ≠ i := by
          intro eq
          apply absent
          simpa only [eq] using Finset.mem_singleton_self i
        rw [val_input D x w input,val_input D y w input]
        exact inputs _ ne
      · by_cases valid : w < n + D.length
        · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha,hb,_⟩ := hS j hj
          by_cases carryA : i ∈ supp n D (opA D j)
          · apply consumers (j,false) _ reach
            apply sem_mem_W.mpr
            exact ⟨hj,by simpa only [src,Bool.false_eq_true,ite_false] using carryA,absent⟩
          · by_cases carryB : i ∈ supp n D (opB D j)
            · apply consumers (j,true) _ reach
              apply sem_mem_W.mpr
              exact ⟨hj,by simpa only [src,ite_true] using carryB,absent⟩
            · have stepA : sem_step n D (opA D j) (n+j) := by
                simpa only [src,Bool.false_eq_true,ite_false] using (sem_step_src (n := n) hj false)
              have stepB : sem_step n D (opB D j) (n+j) := by
                simpa only [src,ite_true] using (sem_step_src (n := n) hj true)
              rw [val_gate hS x j hj,val_gate hS y j hj,
                ih _ ha (Relation.ReflTransGen.head stepA reach) carryA,
                ih _ hb (Relation.ReflTransGen.head stepB reach) carryB]
        · rw [val_ge D x w (by omega),val_ge D y w (by omega)]

  exact aux target Relation.ReflTransGen.refl

lemma consuming_gates_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k)
    (consumers : ∀ e ∈ sem_W n D i,
      val D x (n + e.1) = val D y (n + e.1)) :
    ∀ w, i ∉ supp n D w → val D x w = val D y w :=
  fun w => consuming_ancestors_agreement hS x y i inputs w (fun e he _ => consumers e he)

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma two_consumers_offroute_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (i u : Fin n) (e : Nat × Bool) (he : e ∈ sem_W n D i)
    (empty : supp n D (src D (sem_bar e)) = ∅)
    (g target : Nat)
    (two : ∀ f ∈ sem_W n D i, f.1 = g ∨ f.1 = e.1)
    (offroute : ¬ Relation.ReflTransGen (sem_step n D) (n + g) target)
    (absent : i ∉ supp n D target) :
    val D (single u) target = val D (sem_ins i (single u)) target := by
  have inputs : ∀ k, k ≠ i → single u k = sem_ins i (single u) k := by
    intro k hk
    simp [sem_ins,hk]
  have pathLe : ∀ {a b : Nat}, Relation.ReflTransGen (sem_step n D) a b → a ≤ b := by
    intro a b path
    induction path with
    | refl => rfl
    | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))
  have hj := (sem_mem_W.mp he).1
  have childStep : sem_step n D (src D (sem_bar e)) (n + e.1) := by
    exact sem_step_src (n := n) hj (!e.2)
  have childLt : src D (sem_bar e) < n + e.1 :=
    sem_src_lt hS hj (!e.2)
  apply consuming_ancestors_agreement hS (single u) (sem_ins i (single u)) i inputs target _ absent
  intro f hf reach
  rcases two f hf with first | second
  · exact False.elim (offroute (by simpa only [first] using reach))
  · have parentReach : Relation.ReflTransGen (sem_step n D) (n + e.1) target := by
      simpa only [second] using reach
    have childSame : val D (single u) (src D (sem_bar e)) =
        val D (sem_ins i (single u)) (src D (sem_bar e)) := by
      apply consuming_ancestors_agreement hS (single u) (sem_ins i (single u)) i inputs _
      · intro f hf toChild
        rcases two f hf with first | second
        · apply False.elim
          apply offroute
          have fromG : Relation.ReflTransGen (sem_step n D) (n + g) (src D (sem_bar e)) := by
            simpa only [first] using toChild
          exact fromG.trans (Relation.ReflTransGen.head childStep parentReach)
        · have bound := pathLe toChild
          omega
      · rw [empty]
        exact Finset.notMem_empty i
    have childZero : val D (single u) (src D (sem_bar e)) = false := by
      cases hv : val D (single u) (src D (sem_bar e)) with
      | false => rfl
      | true =>
        have member : u ∈ supp n D (src D (sem_bar e)) := mem_supp.mpr hv
        rw [empty] at member
        exact False.elim (Finset.notMem_empty u member)
    have gateZero : ∀ x : Fin n → Bool, val D x (src D (sem_bar e)) = false →
        val D x (n + e.1) = false := by
      intro x hx
      rw [val_gate hS x e.1 hj,sem_W_and hS he]
      obtain ⟨j,s⟩ := e
      cases s <;> simp only [sem_bar,src,Bool.not_false,Bool.not_true,ite_true,
        Bool.false_eq_true,ite_false] at hx ⊢ <;> simp [gop,hx]
    rw [second,gateZero _ childZero,gateZero _ (childSame.symm.trans childZero)]

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma and_on_fullstar_chain_is_other {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (twoW : ∀ x, (sem_W 14 D x).card ≤ 2)
    (andEmpty : ∀ j, j < D.length → tag D j = true → supp 14 D (14+j) = ∅)
    (x : Fin 14) (e f : Nat × Bool) (he : e ∈ sem_W 14 D x)
    (empty : supp 14 D (src D (sem_bar e)) = ∅)
    (code : sem_W 14 D x = {e,f})
    (neighbors : ∀ u, Adj x u → sem_bar f ∈ sem_W 14 D u)
    (j : Nat) (s : Bool) (hj : j < D.length) (hand : tag D j = true)
    (chain : sem_Chain 14 D (14+f.1) (src D (j,s)))
    (one : fanout D (src D (j,s)) = 1) : j = e.1 := by
  classical
  by_contra different
  have before : f.1 < j := by
    have upper := sem_src_lt h.1 hj s
    have lower := single_reader_chain_le h.1 chain
    omega
  have two : ∀ q ∈ sem_W 14 D x, q.1 = f.1 ∨ q.1 = e.1 := by
    intro q hq
    rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have absent : x ∉ supp 14 D (src D (j,!s)) := by
    intro member
    have consumed : (j,!s) ∈ sem_W 14 D x := sem_mem_W.mpr
      ⟨hj,member,by rw [andEmpty j hj hand]; simp⟩
    rcases two (j,!s) consumed with atF | atE
    · simp only at atF
      omega
    · exact different atE
  have offroute : ¬ Relation.ReflTransGen (sem_step 14 D) (14+f.1) (src D (j,!s)) :=
    single_reader_other_unreachable h.1 chain (sem_step_src hj s) one
      (sem_step_src hj (!s)) (sem_src_ne h.1 hj s).symm
  have extended : sem_Chain 14 D (14+f.1) (14+j) :=
    Relation.ReflTransGen.tail chain ⟨sem_step_src hj s,one⟩
  have outEmpty : supp 14 D (outW 14 D) = ∅ := heawood_supp_out hD
  have full : ∀ u, Adj x u → u ∈ supp 14 D (src D (j,!s)) := by
    intro u hxu
    have baseFalse : val D (single u) (outW 14 D) = false := by
      cases value : val D (single u) (outW 14 D) with
      | false => rfl
      | true =>
        have member := mem_supp.mpr value
        rw [outEmpty] at member
        exact False.elim (Finset.notMem_empty u member)
    have positive : val D (sem_ins x (single u)) (outW 14 D) = true := by
      apply (sem_heawood_comp hD _).mpr
      refine ⟨x,u,hxu,sem_ins_self _ _,sem_ins_ge _ _ u ?_⟩
      simp [single]
    have survives := consumer_barrier_true h.1 x u e he empty f.1 (14+j) two
      extended (outW 14 D) (by unfold outW; omega)
      (by rw [outEmpty]; simp) baseFalse positive
    rw [sem_val_gate_src h.1 _ hj s,hand,gop_true,Bool.and_eq_true] at survives
    have same := two_consumers_offroute_agreement h.1 x u e he empty f.1
      (src D (j,!s)) two offroute absent
    exact mem_supp.mpr (same.trans survives.2)
  obtain ⟨u,v,huv,hxu,hxv,_,_⟩ := sem_hw_two_nbrs x x
  have edgeU := (hc_adjB_iff x u).mp hxu
  have edgeV := (hc_adjB_iff x v).mp hxv
  have oldU := neighbors u edgeU
  have oldV := neighbors v edgeV
  have newU : (j,!s) ∈ sem_W 14 D u := sem_mem_W.mpr
    ⟨hj,full u edgeU,by rw [andEmpty j hj hand]; simp⟩
  have newV : (j,!s) ∈ sem_W 14 D v := sem_mem_W.mpr
    ⟨hj,full v edgeV,by rw [andEmpty j hj hand]; simp⟩
  have positions : sem_bar f ≠ (j,!s) := by
    intro equal
    have indices := congrArg Prod.fst equal
    change f.1 = j at indices
    omega
  have ucode : sem_W 14 D u = {sem_bar f,(j,!s)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    · rw [Finset.card_pair positions]
      exact twoW u
  obtain ⟨q,hq,missing⟩ := sem_antichain sem_heawood_gr h.1 (sem_heawood_comp hD) huv
  rw [ucode,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact missing (sem_mem_W.mp oldV).2.1
  · exact missing (sem_mem_W.mp newV).2.1

end PEqualNP.Outside.L_meta_6659_aux
