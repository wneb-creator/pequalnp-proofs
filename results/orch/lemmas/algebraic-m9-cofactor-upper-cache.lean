import PNPAccepted6659
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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

lemma single_reader_chain_agreement {n : ℕ} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n) (agree : ∀ k, k ≠ i → x k = y k)
    {a w : ℕ} (chain : sem_Chain n D i.val a) (bound : a ≤ w)
    (same : val D x a = val D y a) : val D x w = val D y w := by
  by_contra changed
  have inputChanged : x i ≠ y i := by
    intro hi
    have equal : x = y := by
      funext k
      by_cases hk : k = i
      · simpa only [hk] using hi
      · exact agree k hk
    exact changed (congrArg (fun z => val D z w) equal)
  have firstChanged : val D x i.val ≠ val D y i.val := by
    simpa only [val_input D x i.val i.isLt,val_input D y i.val i.isLt] using inputChanged
  exact (single_reader_chain_hits hS chain (fun z => val D x z ≠ val D y z)
    w (sem_changed_path hS x y i agree w changed) firstChanged bound) same

lemma ineligible_consumption_insert_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (i c : Fin n) (hi : i ∈ ineligSet n D) (e : ℕ × Bool)
    (he : e ∈ sem_W n D i) (absent : c ∉ supp n D (src D (sem_bar e)))
    (w : ℕ) (bound : n + e.1 ≤ w) (absentW : c ∉ supp n D w) :
    val D (sem_ins i (single c)) w = false := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.mp he
  have chain : sem_Chain n D i.val (src D e) := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi (src D e) carrier
    omega
  have otherSame : val D (single c) (src D (sem_bar e)) =
      val D (sem_ins i (single c)) (src D (sem_bar e)) := by
    by_contra changed
    have reach := sem_rtg_mono (fun _ _ h => h.1)
      (sem_changed_path hS (single c) (sem_ins i (single c)) i
        (sem_ins_agree i (single c)) _ changed)
    exact single_reader_other_unreachable hS chain step one
      (sem_step_src hj (!e.2)) (sem_src_ne hS hj e.2).symm reach
  have otherFalse : val D (single c) (src D (sem_bar e)) = false := by
    cases hv : val D (single c) (src D (sem_bar e)) with
    | false => rfl
    | true => exact False.elim (absent (mem_supp.mpr hv))
  have gateFalse (z : Fin n → Bool) (hz : val D z (src D (sem_bar e)) = false) :
      val D z (n+e.1) = false := by
    rw [val_gate hS z e.1 hj,sem_W_and hS he]
    cases hs : e.2 <;> simp [sem_bar,src,hs] at hz <;> simp [gop,hz]
  have sameGate : val D (single c) (n+e.1) = val D (sem_ins i (single c)) (n+e.1) :=
    (gateFalse _ otherFalse).trans (gateFalse _ (otherSame.symm.trans otherFalse)).symm
  have sameW := single_reader_chain_agreement hS (single c) (sem_ins i (single c)) i
    (sem_ins_agree i (single c)) (Relation.ReflTransGen.tail chain ⟨step,one⟩) bound sameGate
  have baseFalse : val D (single c) w = false := by
    cases hv : val D (single c) w with
    | false => rfl
    | true => exact False.elim (absentW (mem_supp.mpr hv))
  exact sameW.symm.trans baseFalse

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

theorem equality_consumption_before_branch {n : ℕ} {D : Dag} (hS : Strict n D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : e ∈ sem_W n D i)
    {b : ℕ} (chain : sem_Chain n D i.val b) (branch : 2 ≤ fanout D b) : n+e.1 ≤ b := by
  obtain ⟨hj,carrier,_⟩ := sem_mem_W.1 he
  have first := sem_inelig_chain hS hi carrier
  have step : sem_step n D (src D e) (n+e.1) := sem_step_src hj e.2
  have one : fanout D (src D e) = 1 := by
    have lower := sem_step_fanout step
    have upper := mem_ineligSet.mp hi _ carrier
    omega
  rcases sem_chain_fork hS first (sem_rtg_mono (fun _ _ h => h.1) chain) with path | ⟨path,ne⟩
  · rcases Relation.ReflTransGen.cases_head path with equal | ⟨w,initial,rest⟩
    · have same := congrArg (fanout D) equal
      omega
    · have equal : n+e.1 = w := sem_step_unique step initial one
      subst w
      exact sem_rtg_le hS (fun _ _ h => h) rest
  · rcases Relation.ReflTransGen.cases_head path with equal | ⟨w,initial,rest⟩
    · exact False.elim (ne equal)
    · have := initial.2
      omega

theorem equality_cf_singleton_pair {c : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (k : Fin 10) : cof_ext (cf_rho c) (cf_iota l) (single k) =
      sem_ind ({c,cf_iota l k} : Finset (Fin 14)) := by
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  funext u
  have fixed : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c <;> simp [cf_rho,equal]
  have support := cof_ext_single hok k u
  rw [fixed] at support
  have other : sem_ind ({c,cf_iota l k} : Finset (Fin 14)) u = true ↔
      u = cf_iota l k ∨ u = c := by simp [sem_ind,or_comm]
  cases first : cof_ext (cf_rho c) (cf_iota l) (single k) u <;>
    cases second : sem_ind ({c,cf_iota l k} : Finset (Fin 14)) u <;> simp_all

theorem equality_cofactor_empty_branch_empty {D : Dag} (hS : Strict 14 D)
    (hD : Correct D) {c i : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (hi : i ∈ ineligSet 14 D) (hic : i ≠ c) {e : ℕ × Bool} (he : e ∈ sem_W 14 D i)
    (absent : c ∉ supp 14 D (src D (sem_bar e))) {b : ℕ}
    (chain : sem_Chain 14 D i.val b) (branch : 2 ≤ fanout D b) (empty : supp 14 D b = ∅) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro k member
  have value := cof_mem_supp.1 member
  rw [equality_cf_singleton_pair hgood k] at value
  by_cases equal : cf_iota l k = i
  · rw [equal] at value
    have assignment : sem_ind ({c,i} : Finset (Fin 14)) = sem_ins i (single c) := by
      funext u
      by_cases hu : u = i <;> simp [sem_ind,sem_ins,single,hu]
    rw [assignment] at value
    have zero := ineligible_consumption_insert_false hS i c hi e he absent b
      (equality_consumption_before_branch hS hi he chain branch) (by rw [empty]; simp)
    rw [zero] at value
    exact Bool.false_ne_true value
  · have free : cf_rho c (cf_iota l k) = none := (hgood.2.1 _).2 ⟨k,rfl⟩
    have distinct : cf_iota l k ≠ c := by
      intro same
      simpa [same,cf_rho] using free
    have nonedge : ¬ Adj c (cf_iota l k) := by
      intro adjacent
      rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
      cases free
    have zero := pilot_chain_nonedge_pair_false hS hD chain nonedge hic (Ne.symm equal)
    rw [zero] at value
    exact Bool.false_ne_true value


theorem equality_critical_branch_false {n : ℕ} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (v : Fin n) {b : ℕ}
    (chain : sem_Chain n D v.val b)
    (hfalse : val D x (outW n D) = false)
    (htrue : val D (sem_ins v x) (outW n D) = true) : val D x b = false := by
  cases hb : val D x b with
  | false => rfl
  | true =>
    have hb' : val D (sem_ins v x) b = true :=
      val_mono hS x (sem_ins v x)
        (by intro i hi; by_cases h : i = v <;> simp_all [sem_ins]) b hb
    have same := sem_dom_eq hS x (sem_ins v x) v
      (fun k hk => by simp [sem_ins,hk]) b (sem_chain_dom hS chain) (hb.trans hb'.symm)
    rw [hfalse,htrue] at same
    exact Bool.noConfusion same

theorem equality_cofactor_neighbor_branch_empty {D : Dag} (h : StrictLive 14 D)
    (hD : Correct D) {c z : Fin 14} {l : List ℕ} (hgood : cf_good c l)
    (edge : Adj c z) {b : ℕ} (chain : sem_Chain 14 D z.val b) :
    cof_supp D (cf_rho c) (cf_iota l) b = ∅ := by
  classical
  have hC := sem_heawood_comp hD
  have hok : cof_Ok (cf_rho c) (cf_iota l) := ⟨hgood.1,hgood.2.1⟩
  have truefixed (u : Fin 14) : cf_rho c u = some true ↔ u = c := by
    by_cases equal : u = c
    · simp [cf_rho,equal]
    · simp [cf_rho,equal]
  apply Finset.eq_empty_iff_forall_notMem.2
  intro i member
  let base := cof_ext (cf_rho c) (cf_iota l) (single i)
  have supported (u : Fin 14) : base u = true ↔ u = cf_iota l i ∨ u = c := by
    rw [show base u = cof_ext (cf_rho c) (cf_iota l) (single i) u from rfl,
      cof_ext_single hok,truefixed]
  have free : cf_rho c (cf_iota l i) = none := (hgood.2.1 _).2 ⟨i,rfl⟩
  have distinct : cf_iota l i ≠ c := by
    intro equal
    simpa [equal,cf_rho] using free
  have nonedge : ¬ Adj c (cf_iota l i) := by
    intro adjacent
    rw [cf_rho,if_neg distinct,if_pos ((hc_adjB_iff _ _).2 adjacent)] at free
    cases free
  have zero : val D base (outW 14 D) = false := by
    cases value : val D base (outW 14 D) with
    | false => rfl
    | true =>
      obtain ⟨u,v,adjacent,hu,hv⟩ := (hC base).1 value
      rcases (supported u).1 hu with rfl | rfl <;>
        rcases (supported v).1 hv with rfl | rfl
      · exact (adj_irrefl _ adjacent).elim
      · exact (nonedge (adj_symm adjacent)).elim
      · exact (nonedge adjacent).elim
      · exact (adj_irrefl _ adjacent).elim
  have after : val D (sem_ins z base) (outW 14 D) = true := by
    apply (hC _).2
    refine ⟨c,z,edge,?_,?_⟩
    · have basec : base c = true := (supported c).2 (Or.inr rfl)
      have unequal : c ≠ z := fun equal => adj_irrefl z (equal ▸ edge)
      simpa [sem_ins,unequal] using basec
    · simp [sem_ins]
  have falsebranch := equality_critical_branch_false h.1 base z chain zero after
  have truebranch := cof_mem_supp.1 member
  rw [falsebranch] at truebranch
  exact Bool.false_ne_true truebranch

theorem equality_assigned_mem {D : Dag} {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) {i t : Fin 14} (hi : i ∈ ineligSet 14 D)
    (ht : t ∈ supp 14 D (src D (pos i))) : pos i ∈ sem_W 14 D t :=
  sem_mem_W.2 ⟨(hpos.1 i hi).1,ht,by
    rw [(hpos.1 i hi).2.1]
    exact Finset.notMem_empty t⟩

theorem equality_assigned_budget {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i))) :
    J.card ≤ 2 + (ru D b t).card := by
  classical
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have subset : J.image pos ⊆ sem_W 14 D t := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
    exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega

theorem equality_assigned_budget_extra {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t z : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i)))
    (hz : z ∈ eligSet 14 D) (edge : Adj t z) :
    J.card + 1 ≤ 2 + (ru D b t).card := by
  classical
  obtain ⟨H,hHt,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) edge
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have fresh : H ∉ J.image pos := by
    intro he
    obtain ⟨i,hi,equal⟩ := Finset.mem_image.1 he
    have same : z = i := as_priv hpos (hJ i hi).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ i hi).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D t := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hHt
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
      exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega

theorem equality_cofactor_supported_loss {n m : ℕ} {D : Dag} (hS : Strict n D)
    (ρ : Fin n → Option Bool) (ι : Fin m → Fin n)
    (b : Fin n → ℕ) (hb : PureBranch n D b)
    (J : Finset (Fin n)) (Z : Finset ℕ)
    (hJ : ∀ x ∈ J, x ∈ eligSet n D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D ρ ι)
    (hZ : ∀ w ∈ Z, 2 ≤ fanout D w ∧ supp n D w = ∅ ∧ cof_supp D ρ ι w = ∅) :
    cof_surP D ρ ι + J.card + Z.card ≤ totalSurplus n D := by
  classical
  let R := J.image (fun x => (⟨b x,0⟩ : Σ _ : ℕ, ℕ))
  let E := Z.image (fun w => (⟨w,0⟩ : Σ _ : ℕ, ℕ))
  have branch_unit : ∀ w, 2 ≤ fanout D w → (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ units n D := by
    intro w hw
    exact mem_units.2 ⟨sb_mem_inner.2 (lt_of_fanout_pos hS (w := w) (by omega)),by change 0+1 < fanout D w; omega⟩
  have injR : Set.InjOn (fun x => (⟨b x,0⟩ : Σ _ : ℕ, ℕ)) (J : Set (Fin n)) := by
    intro x hx y hy eq
    have wires : b x = b y := congrArg Sigma.fst eq
    have same := (hb x (hJ x hx).1).2
    rw [wires,(hb y (hJ y hy).1).2] at same
    exact (Finset.singleton_injective same).symm
  have injE : Function.Injective (fun w => (⟨w,0⟩ : Σ _ : ℕ, ℕ)) :=
    fun _ _ eq => congrArg Sigma.fst eq
  have disjoint : Disjoint R E := by
    apply Finset.disjoint_left.2
    intro u hu hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨w,hw,eq⟩ := Finset.mem_image.1 hv
    have wires : w = b x := congrArg Sigma.fst eq
    have empty := (hZ w hw).2.1
    rw [wires,(hb x (hJ x hx).1).2] at empty
    have : x ∈ (∅ : Finset (Fin n)) := empty ▸ Finset.mem_singleton_self x
    exact Finset.notMem_empty x this
  have sub : R ∪ E ⊆ units n D := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      exact branch_unit _ (hb x (hJ x hx).1).1
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 hu
      exact branch_unit _ (hZ w hw).1
  have lost : ∀ u ∈ R ∪ E, u ∉ cof_keptP D ρ ι := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      exact (hJ x hx).2
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 hu
      exact cof_lostP_of_supp (hZ w hw).2.2
  have bound := cof_surP_add_lost (R ∪ E) sub lost
  have cardR : R.card = J.card := Finset.card_image_of_injOn injR
  have cardE : E.card = Z.card := Finset.card_image_of_injective _ injE
  rw [Finset.card_union_of_disjoint disjoint,cardR,cardE] at bound
  omega

theorem equality_cofactor_reserved_depleted {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {c x : Fin 14} {l : List ℕ}
    (hx : x ∈ eligSet 14 D) (hne : x ≠ c)
    (inc : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1)
    (common : ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w) :
    (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_kept D (cf_rho c) (cf_iota l) := by
  obtain ⟨w,hw⟩ := common
  obtain ⟨z,hxz,hcz⟩ := sem_heawood_gr.2.2.1 x c hne
  obtain ⟨hs1,_,_,e,he,_,hec⟩ :=
    sem_diff_two_exits sem_heawood_gr h (sem_heawood_comp hD) b hb hne hx inc hw hxz hcz
  have hbx : b x ∈ carrierDiff 14 D x c := sem_mem_diff.2 (by
    rw [(hb x hx).2]
    exact ⟨Finset.mem_singleton_self x,fun hcx => hne (Finset.mem_singleton.1 hcx).symm⟩)
  exact cof_lost_of_deg (cof_diff_deplete h.1 (by simp [cf_rho]) hbx (hb x hx).1 hs1 he hec)

theorem equality_missing_branches_distinct {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b)
    {i j : Fin 14} (hne : i ≠ j)
    (hNj : sem_hw_nb j ⊆ P) (missing : ¬ sup_Occ 14 D P (sem_hw_nb i))
    (hNi : sem_hw_nb i ⊆ P) {u v : ℕ}
    (chaini : sem_Chain 14 D i.val u) (chainj : sem_Chain 14 D j.val v) : u ≠ v := by
  intro eq
  obtain ⟨a,ha1,ha2⟩ := nbr_diff_exists j i (Ne.symm hne)
  obtain ⟨k,s,_,_,_,_,hq⟩ := sem_shared_exact sem_heawood_gr h.1 (sem_heawood_comp hD) P hP
    chaini (sem_chain_dom h.1 (eq.symm ▸ chainj)) ⟨a,hNj (hw_mem_nb.2 ha1),ha1,ha2⟩
  apply missing
  refine ⟨src D (k,s),?_⟩
  ext x
  rw [Finset.mem_inter,hw_mem_nb]
  exact ⟨fun hx => (hq x hx.2).1 hx.1,
    fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩


theorem equality_missing_empty_branch {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hNi : sem_hw_nb i ⊆ P)
    (missing : ¬ sup_Occ 14 D P (sem_hw_nb i)) :
    ∃ w, sem_Chain 14 D i.val w ∧ 2 ≤ fanout D w ∧ supp 14 D w = ∅ := by
  rcases sem_inelig_reach sem_heawood_gr h (sem_heawood_comp hD) hi with chain | branch
  · obtain ⟨j,s,_,_,_,hq⟩ := sem_exact_nbhd sem_heawood_gr h.1 (sem_heawood_comp hD) P hP chain
    apply False.elim
    apply missing
    refine ⟨src D (j,s),?_⟩
    ext x
    rw [Finset.mem_inter,hw_mem_nb]
    exact ⟨fun hx => (hq x hx.2).1 hx.1,
      fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩
  · exact branch

theorem equality_m9_center_absent {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (zero : ru D b 3 = ∅)
    {i : Fin 14} (hi : i ∈ ({0,1,2,5} : Finset (Fin 14))) :
    (3 : Fin 14) ∉ supp 14 D (src D (pos i)) := by
  intro member
  have hi' : i ∈ ineligSet 14 D := by
    rw [hI]
    exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
  have h11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hel7 : (7 : Fin 14) ∈ eligSet 14 D := by
    by_contra hn
    have := hI ▸ sem_mem_inelig.2 hn
    exact (by decide : (7 : Fin 14) ∉ ({0,1,2,5,11} : Finset (Fin 14))) this
  have hj : ∀ j ∈ ({11,i} : Finset (Fin 14)),
      j ∈ ineligSet 14 D ∧ (3 : Fin 14) ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact ⟨h11,(hpos.1 11 h11).2.2.1 3 (by decide)⟩
    · have eq := Finset.mem_singleton.1 hj
      subst j
      exact ⟨hi',member⟩
  have bound := equality_assigned_budget_extra h hD b hb pos hpos {11,i} hj hel7 (by decide : Adj 3 7)
  have ne : (11 : Fin 14) ≠ i := by
    intro eq
    rw [← eq] at hi
    exact (by decide : (11 : Fin 14) ∉ ({0,1,2,5} : Finset (Fin 14))) hi
  rw [Finset.card_pair ne,zero,Finset.card_empty] at bound
  omega

theorem equality_m9_cofactor_supported_upper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (first : sem_FirstBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (zeros : ∀ x ∈ ({3,4,6} : Finset (Fin 14)), ru D b x = ∅)
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    cof_surP D (cf_rho 3) (cf_iota cfL3) ≤ 7 := by
  classical
  have hb := sem_firstBranch_pure first
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have eligible : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)), x ∈ eligSet 14 D := by
    intro x hx
    by_contra hn
    exact Finset.disjoint_left.1
      (by decide : Disjoint ({3,4,6,7,12} : Finset (Fin 14)) {0,1,2,5,11}) hx
      (hI ▸ sem_mem_inelig.2 hn)
  have ineligible : ∀ x ∈ ({2,5,11} : Finset (Fin 14)), x ∈ ineligSet 14 D := by
    intro x hx
    rw [hI]
    exact (by decide : ({2,5,11} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hx
  have Pind : ∀ a ∈ mx_L, ∀ b ∈ mx_L, ¬ Adj a b := by decide +kernel
  have n2 : sem_hw_nb 2 ⊆ mx_L := by decide
  have n5 : sem_hw_nb 5 ⊆ mx_L := by decide
  obtain ⟨u,cu,bu,eu⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 2 (by decide)) n2 missing2
  obtain ⟨v,cv,bv,ev⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 5 (by decide)) n5 missing5
  have different : u ≠ v := equality_missing_branches_distinct h hD mx_L Pind
    (by decide : (2 : Fin 14) ≠ 5) n5 missing2 n2 cu cv
  have empty_transfer : ∀ i ∈ ({2,5} : Finset (Fin 14)), ∀ w,
      sem_Chain 14 D i.val w → 2 ≤ fanout D w → supp 14 D w = ∅ →
        cof_supp D (cf_rho 3) (cf_iota cfL3) w = ∅ := by
    intro i hi w chain branch empty
    have hii : i ∈ ineligSet 14 D := by
      rw [hI]
      exact (by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
    have wi : sem_bar (pos i) ∈ sem_W 14 D i := by
      rw [as_W h hD hpos hii]
      exact Finset.mem_singleton_self _
    apply equality_cofactor_empty_branch_empty h.1 hD cf3_good hii
      ((by decide : ∀ i ∈ ({2,5} : Finset (Fin 14)), i ≠ 3) i hi) wi _ chain branch empty
    rw [sem_bar_bar]
    exact equality_m9_center_absent h hD b hb pos hpos hI (zeros 3 (by decide))
      ((by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
  have lost : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)),
      x ∈ eligSet 14 D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D (cf_rho 3) (cf_iota cfL3) := by
    intro x hx
    refine ⟨eligible x hx,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · intro hk
      have member : (3 : Fin 14) ∈ supp 14 D (b 3) := by
        rw [(hb 3 (eligible 3 (by decide))).2]
        exact Finset.mem_singleton_self _
      exact cof_lost_of_true h.1 (by simp [cf_rho]) member (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 4 (by decide)) (by decide : (4 : Fin 14) ≠ 3)
        (by
          intro q hq h4
          have mem := mem_ru.2 ⟨hq,h4⟩
          rw [zeros 4 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 4 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 6 (by decide)) (by decide : (6 : Fin 14) ≠ 3)
        (by
          intro q hq h6
          have mem := mem_ru.2 ⟨hq,h6⟩
          rw [zeros 6 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 6 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 7) (first 7 (eligible 7 (by decide))).2.2)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 12) (first 12 (eligible 12 (by decide))).2.2)
  have bound := equality_cofactor_supported_loss h.1 (cf_rho 3) (cf_iota cfL3) b hb
    {3,4,6,7,12} {u,v} lost (by
      intro w hw
      rcases Finset.mem_insert.1 hw with eq | hw
      · subst w
        exact ⟨bu,eu,empty_transfer 2 (by decide) u cu bu eu⟩
      · have eq := Finset.mem_singleton.1 hw
        subst w
        exact ⟨bv,ev,empty_transfer 5 (by decide) v cv bv ev⟩)
  rw [show ({3,4,6,7,12} : Finset (Fin 14)).card = 5 from rfl,
    Finset.card_pair different] at bound
  omega


end PEqualNP.Outside.L_meta_6659_aux
