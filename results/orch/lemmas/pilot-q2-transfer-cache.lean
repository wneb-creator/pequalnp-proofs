import PNPNineFree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux
theorem equality_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
    (hprotected : ∀ u, Relation.ReflTransGen (sem_step n D) i u → fanout D u ≤ 1)
    (path : Relation.ReflTransGen (sem_step n D) i w) : sem_Chain n D i w := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c prior step ih =>
    have one : fanout D a = 1 := by
      have := hprotected a prior
      have := sem_step_fanout step
      omega
    exact Relation.ReflTransGen.tail ih ⟨step,one⟩

theorem equality_full_gen_protected {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {i v : Fin 14} (hi : i ∈ ineligSet 14 D) {e : ℕ × Bool}
    (he : sem_W 14 D i = {e}) (hiv : Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ e.1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (sem_bar e)) ↔ Adj i t := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 14 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 14 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := equality_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 14 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 14 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 14 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem equality_residual_co_label {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x t i : Fin 14}
    (hx : x ∈ eligSet 14 D) (ht : t ∈ eligSet 14 D) (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x)
    (inclusion : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    (shared : ∃ w, x ∈ supp 14 D w ∧ t ∈ supp 14 D w) :
    t ∈ supp 14 D (src D (pos i)) := by
  by_cases hxt : x = t
  · exact hxt ▸ (hpos.1 i hi).2.2.1 x hix
  obtain ⟨w,hw⟩ := shared
  obtain ⟨e0,he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb hxt hx inclusion hw
  have hti : t ≠ i := fun equal => sem_mem_inelig.1 hi (equal ▸ ht)
  have hgeo : ∀ i x t : Fin 14, hc_adjB i x = true → t ≠ x → t ≠ i →
      ∃ q, hc_adjB i q = true ∧ q ≠ x ∧ hc_adjB t q = false := by decide +kernel
  obtain ⟨q,hiq,hqx,htq⟩ := hgeo i x t ((hc_adjB_iff _ _).2 hix) (Ne.symm hxt) hti
  have hiq' := (hc_adjB_iff _ _).1 hiq
  have htq' := sem_adjB_false.1 htq
  by_contra hnot
  have heq : pos i = e0 := by
    by_contra hne
    exact hnot (he0 _ (as_mem hpos hi hix) hne)
  obtain ⟨e,he,hnt,hnq⟩ := sem_hw_cover_free h hD hxt (Ne.symm hqx) htq'
  exact hnt (he0 e he (fun equal => hnq (by
    rw [equal,← heq]
    exact (hpos.1 i hi).2.2.1 q hiq')))

theorem equality_three_slot_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x i j z : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) (hxz : Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (hru : (ru D b x).card ≤ 1)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have ai := as_mem hpos hi hix
  have aj := as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have small : (sem_W 14 D x).card ≤ 3 := by
    have := cc_le h hD b hb x
    omega
  have code : sem_W 14 D x = {pos i,pos j,H} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
        Finset.card_pair (Ne.symm nj)]
      exact small
  have full := equality_full_gen_protected h hD hi (as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · have hjmem : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j hj).2.2.2]
          exact Finset.mem_singleton_self j
        exact hij (Finset.mem_singleton.1 (hsub hjmem)).symm
      · exact hzi (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)))
  simpa only [sem_bar_bar] using full

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


def qa_nb : Fin 4 → Finset (Fin 7) := ![{0,1,3},{0,2,6},{1,5,6},{0,4,5}]

def qa_unit (r : Fin 7 → Finset (Fin 3)) (j : Fin 3) : Finset (Fin 7) :=
  Finset.univ.filter (fun t => j ∈ r t)

def qa_consumers (A : Fin 4 → Finset (Fin 7)) (t : Fin 7) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => t ∈ A i)

abbrev qa_allowed (S : Finset (Fin 7)) (U : Finset (Fin 7)) : Prop :=
  U.card ≤ 2 ∨ U = qa_nb 0 ∨ U = qa_nb 1 ∨ U = qa_nb 3 ∨ U = S

set_option maxHeartbeats 0 in
theorem qa_antichain_omit : ∀ q : Fin 3, ∀ A B C : Finset (Fin 3),
    q ∉ A → q ∉ B → q ∉ C → A.Nonempty → B.Nonempty → C.Nonempty →
    ¬ A ⊆ B → ¬ B ⊆ A → ¬ A ⊆ C → ¬ C ⊆ A → ¬ B ⊆ C → ¬ C ⊆ B → False := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem qa_antichain_contain : ∀ q : Fin 3, ∀ A B C : Finset (Fin 3),
    q ∈ A → q ∈ B → q ∈ C →
    ¬ A ⊆ B → ¬ B ⊆ A → ¬ A ⊆ C → ¬ C ⊆ A → ¬ B ⊆ C → ¬ C ⊆ B → False := by
  decide +kernel

theorem qa_two_missing_unit (r : Fin 7 → Finset (Fin 3)) (S : Finset (Fin 7))
    (allowed : ∀ j, qa_allowed S (qa_unit r j))
    (two : (r 0).card = 2)
    (center : (r 0).card + ((Finset.univ.erase 0).filter (fun t => r t ⊆ r 0)).card ≤ 5) :
    ∃ q : Fin 3, q ∉ r 0 ∧ qa_unit r q = S ∧ (0 : Fin 7) ∉ S := by
  classical
  have geo : ∀ R : Finset (Fin 3), R.card = 2 → ∃ q : Fin 3, R = Finset.univ.erase q := by
    decide +kernel
  obtain ⟨q,eq⟩ := geo (r 0) two
  have absent : q ∉ r 0 := by rw [eq]; simp
  have subset (t : Fin 7) : r t ⊆ r 0 ↔ q ∉ r t := by
    rw [eq]
    constructor
    · intro sub member
      exact (Finset.mem_erase.1 (sub member)).1 rfl
    · intro no x hx
      refine Finset.mem_erase.2 ⟨?_,Finset.mem_univ _⟩
      intro equal
      exact no (equal ▸ hx)
  have complement : (Finset.univ.erase (0 : Fin 7)).filter (fun t => ¬ r t ⊆ r 0) = qa_unit r q := by
    ext t
    constructor
    · intro h
      have notsub := (Finset.mem_filter.1 h).2
      have member : q ∈ r t := by
        by_contra no
        exact notsub ((subset t).2 no)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,member⟩
    · intro h
      have member := (Finset.mem_filter.1 h).2
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_erase.2 ⟨?_,Finset.mem_univ _⟩,?_⟩
      · intro equal
        exact absent (equal ▸ member)
      · intro sub
        exact (subset t).1 sub member
  have partition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.erase (0 : Fin 7)) (fun t => r t ⊆ r 0)
  rw [complement,show (Finset.univ.erase (0 : Fin 7)).card = 6 from rfl] at partition
  have large : 3 ≤ (qa_unit r q).card := by omega
  have nozero : (0 : Fin 7) ∉ qa_unit r q := by
    intro member
    exact absent (Finset.mem_filter.1 member).2
  have equal : qa_unit r q = S := by
    rcases allowed q with small | equal | equal | equal | equal
    · omega
    · exact (nozero (by rw [equal]; decide)).elim
    · exact (nozero (by rw [equal]; decide)).elim
    · exact (nozero (by rw [equal]; decide)).elim
    · exact equal
  exact ⟨q,absent,equal,by rw [← equal]; exact nozero⟩

theorem qa_residual_impossible (S : Finset (Fin 7))
    (r : Fin 7 → Finset (Fin 3)) (A : Fin 4 → Finset (Fin 7))
    (allowed : ∀ j, qa_allowed S (qa_unit r j))
    (contains : qa_nb 2 ⊆ S)
    (supersets : ∀ i, qa_nb i ⊆ A i)
    (choices : ∀ i, A i = qa_nb 0 ∨ A i = qa_nb 1 ∨ A i = qa_nb 3 ∨ A i = S)
    (missing : A 2 = S)
    (budget : ∀ t, (qa_consumers A t).card + (if t = 0 then 0 else 1) ≤ 2 + (r t).card)
    (labels : ∀ i x t, x ∈ qa_nb i → (r x).Nonempty → r x ⊆ r t → t ∈ A i)
    (center : (r 0).card + ((Finset.univ.erase 0).filter (fun t => r t ⊆ r 0)).card ≤ 5) :
    False := by
  classical
  have zero_mem : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), (0 : Fin 7) ∈ A i := by
    intro i hi
    exact supersets i ((by decide +kernel : ∀ i ∈ ({0,1,3} : Finset (Fin 4)),
      (0 : Fin 7) ∈ qa_nb i) i hi)
  have three_consumers : 3 ≤ (qa_consumers A 0).card := by
    have sub : ({0,1,3} : Finset (Fin 4)) ⊆ qa_consumers A 0 := by
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,zero_mem i hi⟩
    exact Finset.card_le_card sub
  have b0 := budget 0
  simp only [ite_true,Nat.add_zero] at b0
  have positive : (r 0).Nonempty := Finset.card_pos.1 (by omega)
  have small : (r 0).card ≤ 2 := by
    have bound : (r 0).card ≤ 3 := (Finset.card_le_univ _)
    by_contra hn
    have full : r 0 = Finset.univ := Finset.eq_univ_of_card (r 0) (by change (r 0).card = 3; omega)
    have all : ((Finset.univ.erase (0 : Fin 7)).filter (fun t => r t ⊆ r 0)) = Finset.univ.erase 0 := by
      rw [full]
      simp
    rw [all,full] at center
    have : 9 ≤ 5 := center
    omega
  have nozero : (0 : Fin 7) ∉ S := by
    intro member
    have all : qa_consumers A 0 = Finset.univ := by
      apply Finset.eq_univ_iff_forall.2
      intro i
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases equal : i = 2
      · rw [equal,missing]
        exact member
      · exact zero_mem i ((by decide +kernel : ∀ i : Fin 4, i ≠ 2 →
          i ∈ ({0,1,3} : Finset (Fin 4))) i equal)
    rw [all] at b0
    have two : (r 0).card = 2 := by
      have card : (Finset.univ : Finset (Fin 4)).card = 4 := rfl
      rw [card] at b0
      omega
    obtain ⟨q,_,_,no⟩ := qa_two_missing_unit r S allowed two center
    exact no member
  have exact_rows : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), A i = qa_nb i := by
    intro i hi
    have geometry : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), ∀ j ∈ ({0,1,3} : Finset (Fin 4)),
        qa_nb i ⊆ qa_nb j → i = j := by decide +kernel
    rcases choices i with eq | eq | eq | eq
    · have same := geometry i hi 0 (by decide) (eq ▸ supersets i)
      simpa [same] using eq
    · have same := geometry i hi 1 (by decide) (eq ▸ supersets i)
      simpa [same] using eq
    · have same := geometry i hi 3 (by decide) (eq ▸ supersets i)
      simpa [same] using eq
    · exact (nozero (eq ▸ zero_mem i hi)).elim
  have zero_not_subset : ∀ t : Fin 7, t ≠ 0 → ¬ r 0 ⊆ r t := by
    intro t ht sub
    have member : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), t ∈ qa_nb i := by
      intro i hi
      rw [← exact_rows i hi]
      exact labels i 0 t ((by decide +kernel : ∀ i ∈ ({0,1,3} : Finset (Fin 4)),
        (0 : Fin 7) ∈ qa_nb i) i hi) positive sub
    have intersection : ∀ t : Fin 7, t ∈ qa_nb 0 → t ∈ qa_nb 1 → t ∈ qa_nb 3 → t = 0 := by decide +kernel
    exact ht (intersection t (member 0 (by decide)) (member 1 (by decide)) (member 3 (by decide)))
  have candidates : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), (r t).Nonempty := by
    intro t ht
    have geometry : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), ∃ i ∈ ({0,1,3} : Finset (Fin 4)),
        t ∈ qa_nb i := by decide +kernel
    obtain ⟨i,hi,hti⟩ := geometry t ht
    have two : ({i,2} : Finset (Fin 4)) ⊆ qa_consumers A t := by
      intro j hj
      rcases Finset.mem_insert.1 hj with eqj | hj
      · subst j
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _,supersets i hti⟩
      · have eq := Finset.mem_singleton.1 hj
        subst j
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩
        rw [missing]
        exact contains ((by decide +kernel : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ∈ qa_nb 2) t ht)
    have count := Finset.card_le_card two
    have ne : i ≠ 2 := (by decide : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), i ≠ 2) i hi
    rw [Finset.card_pair ne] at count
    have bt := budget t
    have nt : t ≠ 0 := (by decide : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ≠ 0) t ht
    rw [ite_eq_right nt] at bt
    exact Finset.card_pos.1 (by omega)
  have incomparable : ∀ x ∈ ({1,5,6} : Finset (Fin 7)), ∀ t ∈ ({1,5,6} : Finset (Fin 7)),
      x ≠ t → ¬ r x ⊆ r t := by
    intro x hx t ht different subset
    have geometry : ∀ x ∈ ({1,5,6} : Finset (Fin 7)), ∀ t ∈ ({1,5,6} : Finset (Fin 7)),
        x ≠ t → ∃ i ∈ ({0,1,3} : Finset (Fin 4)), x ∈ qa_nb i ∧ t ∉ qa_nb i := by decide +kernel
    obtain ⟨i,hi,hxi,hti⟩ := geometry x hx t ht different
    have mem := labels i x t hxi (candidates x hx) subset
    rw [exact_rows i hi] at mem
    exact hti mem
  by_cases two : (r 0).card = 2
  · obtain ⟨q,_,unit,_⟩ := qa_two_missing_unit r S allowed two center
    have contain : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), q ∈ r t := by
      intro t ht
      have mem : t ∈ qa_unit r q := by
        rw [unit]
        exact contains ((by decide +kernel : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ∈ qa_nb 2) t ht)
      exact (Finset.mem_filter.1 mem).2
    exact qa_antichain_contain q (r 1) (r 5) (r 6)
      (contain 1 (by decide)) (contain 5 (by decide)) (contain 6 (by decide))
      (incomparable 1 (by decide) 5 (by decide) (by decide))
      (incomparable 5 (by decide) 1 (by decide) (by decide))
      (incomparable 1 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 1 (by decide) (by decide))
      (incomparable 5 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 5 (by decide) (by decide))
  · have one : (r 0).card = 1 := by have := Finset.card_pos.2 positive; omega
    obtain ⟨q,eq⟩ := Finset.card_eq_one.1 one
    have omitted : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), q ∉ r t := by
      intro t ht member
      apply zero_not_subset t ((by decide : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ≠ 0) t ht)
      rw [eq]
      exact Finset.singleton_subset_iff.2 member
    exact qa_antichain_omit q (r 1) (r 5) (r 6)
      (omitted 1 (by decide)) (omitted 5 (by decide)) (omitted 6 (by decide))
      (candidates 1 (by decide)) (candidates 5 (by decide)) (candidates 6 (by decide))
      (incomparable 1 (by decide) 5 (by decide) (by decide))
      (incomparable 5 (by decide) 1 (by decide) (by decide))
      (incomparable 1 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 1 (by decide) (by decide))
      (incomparable 5 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 5 (by decide) (by decide))


def qa_line (t : Fin 7) : Fin 14 := Fin.natAdd 7 t

def qa_point (i : Fin 4) : Fin 14 := ⟨i.val,by omega⟩

noncomputable def qa_mask (D : Dag) (w : ℕ) : Finset (Fin 7) := by
  classical
  exact Finset.univ.filter (fun t => qa_line t ∈ supp 14 D w)

lemma qa_line_injective : Function.Injective qa_line := by
  intro i j hij
  apply Fin.ext
  have := congrArg (Fin.val : Fin 14 → ℕ) hij
  simp only [qa_line, Fin.val_natAdd] at this
  omega

lemma qa_point_injective : Function.Injective qa_point := by
  intro i j hij
  apply Fin.ext
  exact congrArg (Fin.val : Fin 14 → ℕ) hij

lemma qa_geometry :
    (∀ i : Fin 4, qa_point i ∈ ({0,1,2,3} : Finset (Fin 14))) ∧
    (∀ t : Fin 7, qa_line t ∉ ({0,1,2,3} : Finset (Fin 14))) ∧
    (∀ i : Fin 4, ∀ t : Fin 7, t ∈ qa_nb i ↔ Adj (qa_point i) (qa_line t)) ∧
    (∀ t : Fin 7, t ≠ 0 → ∃ z : Fin 14,
      z ∉ ({0,1,2,3} : Finset (Fin 14)) ∧ Adj (qa_line t) z) ∧
    (∀ t : Fin 7, ∃ i ∈ ({0,1,3} : Finset (Fin 4)),
      (0 : Fin 7) ∈ qa_nb i ∧ t ∈ qa_nb i) := by
  simp only [← hc_adjB_iff]
  decide +kernel

lemma qa_circuit_residual_exclusion {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3}) (hB : Bplus 14 D = 13)
    (hS : totalSurplus 14 D ≤ 14)
    (occurs : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), ∃ w, qa_mask D w = qa_nb i)
    (shape : ∃ S : Finset (Fin 7), ∀ w, qa_allowed S (qa_mask D w)) : False := by
  classical
  obtain ⟨S,hshape⟩ := shape
  obtain ⟨b,hb⟩ := exists_pureBranch h hD
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hp := inelig_card_add 14 D
  rw [hI,show ({0,1,2,3} : Finset (Fin 14)).card = 4 from rfl] at hp
  have hres := card_residual h.1 b hb
  have hcard : (residualUnits 14 D b).card = 3 := by omega
  let R := residualUnits 14 D b
  let e : (↑R) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have ainj : Function.Injective a := fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u := by
    intro u
    constructor
    · intro hu
      exact ⟨e ⟨u,hu⟩,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  let r : Fin 7 → Finset (Fin 3) := fun t =>
    Finset.univ.filter (fun k => qa_line t ∈ supp 14 D (a k).1)
  have image (t : Fin 7) : (r t).image a = ru D b (qa_line t) := by
    ext u
    constructor
    · rintro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
      exact mem_ru.2 ⟨(onto _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
    · intro hu
      obtain ⟨hur,hux⟩ := mem_ru.1 hu
      obtain ⟨k,rfl⟩ := (onto u).1 hur
      exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩,rfl⟩
  have card (t : Fin 7) : (r t).card = (ru D b (qa_line t)).card := by
    rw [← image t,Finset.card_image_of_injective _ ainj]
  have point_in (i : Fin 4) : qa_point i ∈ ineligSet 14 D := by
    rw [hI]
    exact qa_geometry.1 i
  have line_el (t : Fin 7) : qa_line t ∈ eligSet 14 D := by
    by_contra hn
    exact qa_geometry.2.1 t (hI ▸ sem_mem_inelig.2 hn)
  let A : Fin 4 → Finset (Fin 7) := fun i => qa_mask D (src D (pos (qa_point i)))
  have supersets (i : Fin 4) : qa_nb i ⊆ A i := by
    intro t ht
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (hpos.1 _ (point_in i)).2.2.1 _ ((qa_geometry.2.2.1 i t).1 ht)⟩
  have choices (i : Fin 4) : A i = qa_nb 0 ∨ A i = qa_nb 1 ∨ A i = qa_nb 3 ∨ A i = S := by
    rcases hshape (src D (pos (qa_point i))) with low | h0 | h1 | h3 | hS
    · have bound := Finset.card_le_card (supersets i)
      have nbcard := (by decide : ∀ i : Fin 4, (qa_nb i).card = 3) i
      change (A i).card ≤ 2 at low
      omega
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr hS))
  have missing : A 2 = S := by
    have sub := supersets 2
    rcases choices 2 with eq | eq | eq | eq
    · rw [eq] at sub
      exact ((by decide : ¬ qa_nb 2 ⊆ qa_nb 0) sub).elim
    · rw [eq] at sub
      exact ((by decide : ¬ qa_nb 2 ⊆ qa_nb 1) sub).elim
    · rw [eq] at sub
      exact ((by decide : ¬ qa_nb 2 ⊆ qa_nb 3) sub).elim
    · exact eq
  have allowed (j : Fin 3) : qa_allowed S (qa_unit r j) := by
    have eq : qa_unit r j = qa_mask D (a j).1 := by
      ext t
      simp only [qa_unit,qa_mask,Finset.mem_filter,Finset.mem_univ,true_and,r]
    rw [eq]
    exact hshape _
  have labels (i : Fin 4) (x t : Fin 7) (hx : x ∈ qa_nb i)
      (nonempty : (r x).Nonempty) (sub : r x ⊆ r t) : t ∈ A i := by
    obtain ⟨k,hk⟩ := nonempty
    have hkx := (Finset.mem_filter.1 hk).2
    have hkt := (Finset.mem_filter.1 (sub hk)).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _,?_⟩
    apply equality_residual_co_label h hD b hb pos hpos (line_el x) (line_el t)
      (point_in i) ((qa_geometry.2.2.1 i x).1 hx)
    · intro u hu hux
      obtain ⟨j,rfl⟩ := (onto u).1 hu
      exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩))).2
    · exact ⟨(a k).1,hkx,hkt⟩
  have budget (t : Fin 7) : (qa_consumers A t).card + (if t = 0 then 0 else 1) ≤ 2 + (r t).card := by
    let J : Finset (Fin 14) := (qa_consumers A t).image qa_point
    have hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ qa_line t ∈ supp 14 D (src D (pos i)) := by
      intro i hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hi
      exact ⟨point_in k,(Finset.mem_filter.1 (Finset.mem_filter.1 hk).2).2⟩
    have hJcard : J.card = (qa_consumers A t).card :=
      Finset.card_image_of_injective _ qa_point_injective
    by_cases ht : t = 0
    · have bound := equality_assigned_budget h hD b hb pos hpos J hJ
      rw [hJcard,← card t] at bound
      simpa only [ht,ite_true,Nat.add_zero] using bound
    · obtain ⟨z,hz,hedge⟩ := qa_geometry.2.2.2.1 t ht
      have hze : z ∈ eligSet 14 D := by
        by_contra hn
        exact hz (hI ▸ sem_mem_inelig.2 hn)
      have bound := equality_assigned_budget_extra h hD b hb pos hpos J hJ hze hedge
      rw [hJcard,← card t] at bound
      simpa only [ht,ite_false] using bound
  let T : Finset (Fin 7) := (Finset.univ.erase 0).filter (fun t => r t ⊆ r 0)
  let X : Finset (Fin 14) := T.image qa_line
  have hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ qa_line 0 ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → qa_line 0 ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ qa_line 0 ∈ supp 14 D w := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    have ht0 : t ≠ 0 := (Finset.mem_erase.1 (Finset.mem_filter.1 ht).1).1
    have sub : r t ⊆ r 0 := (Finset.mem_filter.1 ht).2
    refine ⟨line_el t,fun eq => ht0 (qa_line_injective eq),?_,?_⟩
    · intro u hu hux
      obtain ⟨j,rfl⟩ := (onto u).1 hu
      exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩))).2
    · obtain ⟨i,hi,h0,hit⟩ := qa_geometry.2.2.2.2 t
      obtain ⟨w,hw⟩ := occurs i hi
      refine ⟨w,?_,?_⟩
      · have member : t ∈ qa_mask D w := by rw [hw]; exact hit
        change t ∈ Finset.univ.filter (fun z => qa_line z ∈ supp 14 D w) at member
        exact (Finset.mem_filter.1 member).2
      · have member : (0 : Fin 7) ∈ qa_mask D w := by rw [hw]; exact h0
        change (0 : Fin 7) ∈ Finset.univ.filter (fun z => qa_line z ∈ supp 14 D w) at member
        exact (Finset.mem_filter.1 member).2
  have hJgeo : ∀ i ∈ ({1,2,3} : Finset (Fin 10)), i.val < 4 ∧
      cf_iota cfL7 i ∉ ({0,1,2,3} : Finset (Fin 14)) ∧
      cf_iota cfL7 i ≠ qa_line 0 ∧ ∀ t : Fin 7, cf_iota cfL7 i ≠ qa_line t := by
    decide +kernel
  have bound := equality_cf_nine_free h hD b hb cf7_good (line_el 0) X hX
    {1,2,3} (by decide) (by
      intro i hi
      obtain ⟨small,no,ne,allne⟩ := hJgeo i hi
      refine ⟨small,?_,ne,?_⟩
      · by_contra hn
        exact no (hI ▸ sem_mem_inelig.2 hn)
      · intro member
        obtain ⟨t,_,eq⟩ := Finset.mem_image.1 member
        exact allne t eq.symm)
  have xcard : X.card = T.card := Finset.card_image_of_injective _ qa_line_injective
  change (ru D b (qa_line 0)).card + X.card + 9 ≤ totalSurplus 14 D at bound
  rw [← card 0,xcard] at bound
  apply qa_residual_impossible S r A allowed (by rw [← missing]; exact supersets 2)
    supersets choices missing budget labels
  change (r 0).card + T.card ≤ 5
  omega

end PEqualNP.Outside.L_meta_6659_aux
