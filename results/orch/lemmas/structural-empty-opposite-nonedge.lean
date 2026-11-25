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


namespace PEqualNP.Outside.L_meta_6659_aux

lemma chain_prefix_of_path {n : Nat} {D : Dag} (hS : Strict n D) {a b : Nat}
    (chain : sem_Chain n D a b) : ∀ g,
      Relation.ReflTransGen (sem_step n D) a g → g ≤ b → sem_Chain n D a g := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g path bound
    have lower := sem_rtg_le hS (fun _ _ step => step) path
    have equal := Nat.le_antisymm lower bound
    rw [← equal]
    exact Relation.ReflTransGen.refl
  | @head a c step rest ih =>
    intro g path bound
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨z,first,remaining⟩
    · rw [equal]
      exact Relation.ReflTransGen.refl
    · have same : c = z := sem_step_unique step.1 first step.2
      subst z
      exact Relation.ReflTransGen.head step (ih g remaining bound)

lemma pair_signal_no_branch {n : Nat} {D : Dag} (hS : Strict n D)
    (u v : Fin n) (g : Nat) (empty : supp n D g = ∅)
    (signal : val D (sem_ind ({u,v} : Finset (Fin n))) g = true)
    (branches : ∀ w, 2 ≤ fanout D w →
      ∃ i : Fin n, sem_Chain n D i.val w ∧ i ∈ supp n D w)
    (third : ∀ (i : Fin n) w, sem_Chain n D i.val w → i ≠ u → i ≠ v →
      val D (sem_ind ({u,v} : Finset (Fin n))) w = false) :
    ∀ w, Relation.ReflTransGen (sem_step n D) g w →
      val D (sem_ind ({u,v} : Finset (Fin n))) w = true → fanout D w ≤ 1 := by
  classical
  have singletonFalse : ∀ i : Fin n, val D (single i) g = false := by
    intro i
    cases value : val D (single i) g with
    | false => rfl
    | true =>
      have member := mem_supp.mpr value
      rw [empty] at member
      exact False.elim (Finset.notMem_empty i member)
  have pathU : Relation.ReflTransGen (sem_step n D) u.val g := by
    have agree : ∀ k, k ≠ u → single v k = sem_ind ({u,v} : Finset (Fin n)) k := by
      intro k hk
      simp [single,sem_ind,hk]
    have changed : val D (single v) g ≠ val D (sem_ind ({u,v} : Finset (Fin n))) g := by
      rw [singletonFalse v,signal]
      decide
    exact sem_rtg_mono (fun _ _ step => step.1)
      (sem_changed_path hS (single v) (sem_ind ({u,v} : Finset (Fin n))) u agree g changed)
  have pathV : Relation.ReflTransGen (sem_step n D) v.val g := by
    have agree : ∀ k, k ≠ v → single u k = sem_ind ({u,v} : Finset (Fin n)) k := by
      intro k hk
      simp [single,sem_ind,hk]
    have changed : val D (single u) g ≠ val D (sem_ind ({u,v} : Finset (Fin n))) g := by
      rw [singletonFalse u,signal]
      decide
    exact sem_rtg_mono (fun _ _ step => step.1)
      (sem_changed_path hS (single u) (sem_ind ({u,v} : Finset (Fin n))) v agree g changed)
  have endpointPath : ∀ i : Fin n, i = u ∨ i = v →
      Relation.ReflTransGen (sem_step n D) i.val g := by
    intro i hi
    rcases hi with equal | equal
    · simpa only [equal] using pathU
    · simpa only [equal] using pathV
  intro w reach trueAt
  by_contra many
  obtain ⟨i,chain,member⟩ := branches w (by omega)
  have endpoint : i = u ∨ i = v := by
    by_contra different
    have niu : i ≠ u := fun hi => different (Or.inl hi)
    have niv : i ≠ v := fun hi => different (Or.inr hi)
    have falseAt := third i w chain niu niv
    rw [trueAt] at falseAt
    exact Bool.noConfusion falseAt
  have bound : g ≤ w := sem_rtg_le hS (fun _ _ step => step) reach
  have initialChain := chain_prefix_of_path hS chain g (endpointPath i endpoint) bound
  have same : val D (fun _ : Fin n => false) w = val D (single i) w := by
    apply sem_dom_eq_at hS (fun _ : Fin n => false) (single i) i
    · intro k hk
      simp [single,hk]
    · exact sem_chain_dom_at hS initialChain bound
    · rw [val_zero hS,singletonFalse i]
  rw [val_zero hS,mem_supp.mp member] at same
  exact Bool.noConfusion same

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

theorem pilot_nonedge_extension :
    ∀ u v i : Fin 14, hc_adjB u v = false → i ≠ u → i ≠ v →
      ∃ z : Fin 14, hc_adjB i z = true ∧ hc_adjB u z = false ∧ hc_adjB v z = false := by
  decide +kernel

theorem pilot_chain_nonedge_pair_false {D : Dag} (hS : Strict 14 D) (hD : Correct D)
    {i u v : Fin 14} {w : ℕ} (chain : sem_Chain 14 D i.val w)
    (huv : ¬ Adj u v) (hiu : i ≠ u) (hiv : i ≠ v) :
    val D (sem_ind ({u,v} : Finset (Fin 14))) w = false := by
  obtain ⟨z,hiz,huz,hvz⟩ := pilot_nonedge_extension u v i
    (sem_adjB_false.2 huv) hiu hiv
  have hiz' := (hc_adjB_iff _ _).1 hiz
  have huz' := sem_adjB_false.1 huz
  have hvz' := sem_adjB_false.1 hvz
  have independent : ∀ a ∈ ({u,v,z} : Finset (Fin 14)),
      ∀ b ∈ ({u,v,z} : Finset (Fin 14)), ¬ Adj a b := by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact adj_irrefl _
    · exact huv
    · exact huz'
    · exact fun h => huv (adj_symm h)
    · exact adj_irrefl _
    · exact hvz'
    · exact fun h => huz' (adj_symm h)
    · exact fun h => hvz' (adj_symm h)
    · exact adj_irrefl _
  have negative := sem_ind_no_edge independent
  have positive : sem_Edge Adj (sem_ins i (sem_ind ({u,v,z} : Finset (Fin 14)))) := by
    refine ⟨i,z,hiz',sem_ins_self _ _,sem_ins_ge _ _ z ?_⟩
    simp [sem_ind]
  have branch_false := (sem_dom_split hS (sem_heawood_comp hD)
    (sem_ind ({u,v,z} : Finset (Fin 14))) i w (sem_chain_dom hS chain)
    negative positive).1
  have monotone : ∀ k : Fin 14, sem_ind ({u,v} : Finset (Fin 14)) k = true →
      sem_ind ({u,v,z} : Finset (Fin 14)) k = true := by
    intro k hk
    simp only [sem_ind,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl <;> simp
  cases value : val D (sem_ind ({u,v} : Finset (Fin 14))) w with
  | false => rfl
  | true =>
    have bad := val_mono hS _ _ monotone w value
    rw [branch_false] at bad
    exact Bool.noConfusion bad

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma first_false_filter_chain {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) {a b : Nat}
    (path : Relation.ReflTransGen (sem_step n D) a b)
    (start : val D x a = true) (finish : val D x b = false)
    (unbranched : ∀ w, Relation.ReflTransGen (sem_step n D) a w →
      val D x w = true → fanout D w ≤ 1) :
    ∃ j s, j < D.length ∧ sem_Chain n D a (src D (j,s)) ∧
      val D x (src D (j,s)) = true ∧ tag D j = true ∧
      val D x (src D (j,!s)) = false ∧ val D x (n+j) = false := by
  revert start unbranched
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro start _
    simp only [start,Bool.true_eq_false] at finish
  | @head a c step rest ih =>
    intro start unbranched
    by_cases nextTrue : val D x c = true
    · have remaining : ∀ w, Relation.ReflTransGen (sem_step n D) c w →
          val D x w = true → fanout D w ≤ 1 := by
        intro w reach value
        exact unbranched w (Relation.ReflTransGen.head step reach) value
      obtain ⟨j,s,hj,chain,value,tag,opposite,last⟩ := ih nextTrue remaining
      have one : fanout D a = 1 := Nat.le_antisymm
        (unbranched a Relation.ReflTransGen.refl start) (sem_step_fanout step)
      exact ⟨j,s,hj,Relation.ReflTransGen.head ⟨step,one⟩ chain,value,tag,opposite,last⟩
    · have nextFalse : val D x c = false := by
        cases value : val D x c <;> simp_all
      obtain ⟨j,s,hj,rfl,source⟩ := sem_step_iff.mp step
      have carried : val D x (src D (j,s)) = true := by rw [source]; exact start
      have operation := val_gate hS x j hj
      have andFalse : tag D j = true ∧ val D x (src D (j,!s)) = false := by
        cases ht : tag D j <;> cases s <;>
          simp only [src,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,
            Bool.not_true] at carried ⊢ <;>
          simp [ht,gop,carried,nextFalse] at operation ⊢ <;> exact operation
      refine ⟨j,s,hj,?_,carried,andFalse.1,andFalse.2,nextFalse⟩
      rw [source]
      exact Relation.ReflTransGen.refl

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma tight_surplus_branch_chain {n : Nat} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (budget : totalSurplus n D ≤ (eligSet n D).card) :
    ∀ w, 2 ≤ fanout D w →
      ∃ i : Fin n, sem_Chain n D i.val w ∧ i ∈ supp n D w := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_minBranch hG hS hC
  have pure := sem_minBranch_pure hb
  have sub : reservedUnits n D b ⊆ units n D :=
    (reserved_subset hS b pure).trans (Finset.filter_subset _ _)
  have all : reservedUnits n D b = units n D :=
    Finset.eq_of_subset_of_card_le sub (by rw [card_units,card_reserved b pure]; exact budget)
  intro w hw
  have unit : (⟨w,0⟩ : Σ _ : Nat, Nat) ∈ units n D := by
    rw [mem_units]
    change w ∈ inner n D ∧ 0+1 < fanout D w
    exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega)),by omega⟩
  rw [← all] at unit
  obtain ⟨i,hi,equal⟩ := Finset.mem_image.mp unit
  have same : b i = w := congrArg Sigma.fst equal
  refine ⟨i,?_,?_⟩
  · rw [← same]
    exact (hb i hi).2.2.1
  · rw [← same,(pure i hi).2]
    simp

lemma fano_nonedge_true_cone_unbranched {D : Dag} (hS : Strict 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D ≤ (eligSet 14 D).card)
    (u v : Fin 14) (nonedge : ¬ Adj u v) (g : Nat)
    (empty : supp 14 D g = ∅)
    (signal : val D (sem_ind ({u,v} : Finset (Fin 14))) g = true) :
    ∀ w, Relation.ReflTransGen (sem_step 14 D) g w →
      val D (sem_ind ({u,v} : Finset (Fin 14))) w = true → fanout D w ≤ 1 := by
  apply pair_signal_no_branch hS u v g empty signal
  · exact tight_surplus_branch_chain sem_heawood_gr hS (sem_heawood_comp hD) budget
  · intro i w chain hiu hiv
    exact pilot_chain_nonedge_pair_false hS hD chain nonedge hiu hiv

lemma fano_nonedge_first_filter {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D ≤ (eligSet 14 D).card)
    (u v : Fin 14) (nonedge : ¬ Adj u v) (g : Nat)
    (empty : supp 14 D g = ∅)
    (signal : val D (sem_ind ({u,v} : Finset (Fin 14))) g = true) :
    ∃ j s, j < D.length ∧ sem_Chain 14 D g (src D (j,s)) ∧
      val D (sem_ind ({u,v} : Finset (Fin 14))) (src D (j,s)) = true ∧
      tag D j = true ∧
      val D (sem_ind ({u,v} : Finset (Fin 14))) (src D (j,!s)) = false ∧
      val D (sem_ind ({u,v} : Finset (Fin 14))) (14+j) = false := by
  classical
  have valid : g < 14 + D.length := by
    by_contra outside
    have value := val_ge D (sem_ind ({u,v} : Finset (Fin 14))) g (by omega)
    rw [signal] at value
    exact Bool.noConfusion value
  have independent : ∀ a ∈ ({u,v} : Finset (Fin 14)),
      ∀ b ∈ ({u,v} : Finset (Fin 14)), ¬ Adj a b := by
    intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact adj_irrefl _
    · exact nonedge
    · exact fun edge => nonedge (adj_symm edge)
    · exact adj_irrefl _
  have finish : val D (sem_ind ({u,v} : Finset (Fin 14))) (outW 14 D) = false := by
    have correct := sem_heawood_comp hD (sem_ind ({u,v} : Finset (Fin 14)))
    have noEdge := sem_ind_no_edge independent
    cases value : val D (sem_ind ({u,v} : Finset (Fin 14))) (outW 14 D) with
    | false => rfl
    | true => exact False.elim (noEdge (correct.mp value))
  exact first_false_filter_chain h.1 _ (live_reaches_out h g valid) signal finish
    (fano_nonedge_true_cone_unbranched h.1 hD budget u v nonedge g empty signal)

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma empty_opposite_other_exit {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    (oppositeEmpty : supp 14 D (src D (sem_bar e)) = ∅)
    {x : Fin 14} (member : x ∈ supp 14 D (src D e)) :
    ∃ f, f ≠ e ∧ sem_W 14 D x = {e,f} ∧
      ∀ y, Adj x y → sem_bar f ∈ sem_W 14 D y := by
  classical
  have he : e ∈ sem_W 14 D x := sem_mem_W.mpr
    ⟨valid,member,by rw [outEmpty]; simp⟩
  obtain ⟨f,hf,hother,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1
    (sem_heawood_comp hD) (matching_adj.2 x).1
  have different : f ≠ e := by
    intro equal
    have bad := (sem_mem_W.mp hother).2.1
    rw [equal,oppositeEmpty] at bad
    exact Finset.notMem_empty _ bad
  have code : sem_W 14 D x = {e,f} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    · rw [Finset.card_pair different.symm]
      exact two x
  refine ⟨f,different,code,?_⟩
  intro y hxy
  obtain ⟨q,hq,hqy,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1
    (sem_heawood_comp hD) hxy
  rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · have bad := (sem_mem_W.mp hqy).2.1
    rw [oppositeEmpty] at bad
    exact (Finset.notMem_empty _ bad).elim
  · exact hqy

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma empty_opposite_rejects_other_nonedge {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (budget : totalSurplus 14 D ≤ (eligSet 14 D).card)
    (twoW : ∀ x, (sem_W 14 D x).card ≤ 2)
    (andEmpty : ∀ j, j < D.length → tag D j = true → supp 14 D (14+j) = ∅)
    (x : Fin 14) (e : Nat × Bool) (he : e ∈ sem_W 14 D x)
    (empty : supp 14 D (src D (sem_bar e)) = ∅) :
    ∃ f, f ≠ e ∧ sem_W 14 D x = {e,f} ∧
      ∀ u v : Fin 14, ¬ Adj u v →
        val D (sem_ind ({u,v} : Finset (Fin 14))) (14+f.1) = true →
        val D (sem_ind ({u,v} : Finset (Fin 14))) (14+e.1) = false := by
  classical
  have ev := (sem_mem_W.mp he).1
  obtain ⟨f,different,code,neighbors⟩ := empty_opposite_other_exit h hD twoW e ev
    (andEmpty e.1 ev (sem_W_and h.1 he)) empty (sem_mem_W.mp he).2.1
  refine ⟨f,different,code,?_⟩
  intro u v nonedge signal
  have hf : f ∈ sem_W 14 D x := by rw [code]; simp
  have fv := (sem_mem_W.mp hf).1
  have fEmpty := andEmpty f.1 fv (sem_W_and h.1 hf)
  obtain ⟨j,s,hj,chain,value,hand,_,last⟩ :=
    fano_nonedge_first_filter h hD budget u v nonedge (14+f.1) fEmpty signal
  have upper := fano_nonedge_true_cone_unbranched h.1 hD budget u v nonedge
    (14+f.1) fEmpty signal (src D (j,s))
    (sem_rtg_mono (fun _ _ step => step.1) chain) value
  have one : fanout D (src D (j,s)) = 1 :=
    Nat.le_antisymm upper (sem_step_fanout (sem_step_src (n := 14) hj s))
  have same := and_on_fullstar_chain_is_other h hD twoW andEmpty x e f he empty
    code neighbors j s hj hand chain one
  simpa only [same] using last

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma fullstar_chain_enters_empty {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (x : Fin 14) (e f : Nat × Bool) (he : e ∈ sem_W 14 D x)
    (empty : supp 14 D (src D (sem_bar e)) = ∅)
    (code : sem_W 14 D x = {e,f})
    (s : Bool) (chain : sem_Chain 14 D (14+f.1) (src D (e.1,s)))
    (one : fanout D (src D (e.1,s)) = 1) : s = !e.2 := by
  classical
  have hj := (sem_mem_W.mp he).1
  have hand := sem_W_and h.1 he
  have two : ∀ q ∈ sem_W 14 D x, q.1 = f.1 ∨ q.1 = e.1 := by
    intro q hq
    rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_contra unequal
  have same : s = e.2 := by cases s <;> cases side : e.2 <;> simp_all
  subst s
  have offroute : ¬ Relation.ReflTransGen (sem_step 14 D) (14+f.1)
      (src D (sem_bar e)) :=
    single_reader_other_unreachable h.1 chain (sem_step_src hj e.2) one
      (sem_step_src hj (!e.2)) (sem_src_ne h.1 hj e.2).symm
  have extended : sem_Chain 14 D (14+f.1) (14+e.1) :=
    Relation.ReflTransGen.tail chain ⟨sem_step_src hj e.2,one⟩
  obtain ⟨u,v,huv,hxu,hxv,_,_⟩ := sem_hw_two_nbrs x x
  have edge := (hc_adjB_iff x u).mp hxu
  have outEmpty : supp 14 D (outW 14 D) = ∅ := heawood_supp_out hD
  have baseFalse : val D (single u) (outW 14 D) = false := by
    cases value : val D (single u) (outW 14 D) with
    | false => rfl
    | true =>
      have member := mem_supp.mpr value
      rw [outEmpty] at member
      exact False.elim (Finset.notMem_empty u member)
  have positive : val D (sem_ins x (single u)) (outW 14 D) = true := by
    apply (sem_heawood_comp hD _).mpr
    refine ⟨x,u,edge,sem_ins_self _ _,sem_ins_ge _ _ u ?_⟩
    simp [single]
  have survives := consumer_barrier_true h.1 x u e he empty f.1 (14+e.1) two
    extended (outW 14 D) (by unfold outW; omega)
    (by rw [outEmpty]; simp) baseFalse positive
  rw [sem_val_gate_src h.1 _ hj e.2,hand,gop_true,Bool.and_eq_true] at survives
  have agrees := two_consumers_offroute_agreement h.1 x u e he empty f.1
    (src D (sem_bar e)) two offroute (by rw [empty]; simp)
  have member : u ∈ supp 14 D (src D (sem_bar e)) :=
    mem_supp.mpr (agrees.trans survives.2)
  rw [empty] at member
  exact Finset.notMem_empty u member

end PEqualNP.Outside.L_meta_6659_aux
