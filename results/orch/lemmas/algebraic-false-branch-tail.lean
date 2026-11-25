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

theorem equality_critical_false_surplus {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (x : Fin n → Bool) (P : Finset (Fin n)) (hP : P ⊆ eligSet n D)
    (hfalse : val D x (outW n D) = false)
    (htrue : ∀ v ∈ P, val D (sem_ins v x) (outW n D) = true) :
    P.card ≤ surplusOn D ((inner n D).filter (fun w => val D x w = false)) := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_firstBranch hG hS hC
  have pure := sem_firstBranch_pure hb
  let K := (inner n D).filter (fun w => val D x w = false)
  let f := fun v : Fin n => (⟨b v,0⟩ : Σ _ : ℕ, ℕ)
  have injective : Set.InjOn f (P : Set (Fin n)) :=
    fun v hv u hu eq => sb_reserved_inj b pure (hP hv) (hP hu) eq
  have contained : P.image f ⊆ unitsOn n D K := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 hu
    have unit := reserved_subset hS b pure (Finset.mem_image.2 ⟨v,hP hv,rfl⟩)
    have unit' : f v ∈ units n D := (Finset.mem_filter.1 unit).1
    apply Finset.mem_filter.2
    refine ⟨unit',Finset.mem_filter.2 ⟨(mem_units.1 unit').1,?_⟩⟩
    exact equality_critical_branch_false hS x v (hb v (hP hv)).2.2 hfalse (htrue v hv)
  have count := Finset.card_le_card contained
  rw [Finset.card_image_of_injOn injective,card_unitsOn K (Finset.filter_subset _ _)] at count
  exact count

def equality_line_base (i : Fin 14) : Bool := decide (7 ≤ i.val)

theorem equality_point_false_surplus {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ((eligSet 14 D).filter (fun v => v.val < 7)).card ≤
      surplusOn D ((inner 14 D).filter (fun w => val D equality_line_base w = false)) := by
  have hC := sem_heawood_comp hD
  apply equality_critical_false_surplus sem_heawood_gr h.1 hC equality_line_base _
    (Finset.filter_subset _ _)
  · have noedge : ¬ sem_Edge Adj equality_line_base := by
      rintro ⟨a,b,edge,ha,hb⟩
      have geometry : ∀ a b : Fin 14, 7 ≤ a.val → 7 ≤ b.val → ¬ Adj a b := by
        decide +kernel
      exact geometry a b (by simpa [equality_line_base] using ha)
        (by simpa [equality_line_base] using hb) edge
    cases ho : val D equality_line_base (outW 14 D) with
    | false => rfl
    | true => exact (noedge ((hC _).1 ho)).elim
  · intro v hv
    have hp := (Finset.mem_filter.1 hv).2
    obtain ⟨a,edge,ha⟩ := (by decide +kernel : ∀ v : Fin 14, v.val < 7 →
      ∃ a, Adj v a ∧ 7 ≤ a.val) v hp
    apply (hC _).2
    refine ⟨v,a,edge,?_,?_⟩
    · simp [sem_ins]
    · have hne : a ≠ v := by intro equal; subst a; omega
      simp [sem_ins,hne,equality_line_base,ha]
