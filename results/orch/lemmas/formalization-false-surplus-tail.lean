namespace PEqualNP.Outside.L_meta_6659_aux

lemma false_flow_boolean (t a b : Bool) (last U B : Prop)
    [Decidable last] [Decidable U] [Decidable B]
    (hlast : last → gop t a b = false)
    (hU : U → t = true ∧ (a = true ∨ b = true))
    (hB : B → a = true ∧ b = true) (disj : ¬ (U ∧ B)) :
    (if a = false ∧ ¬ (¬ last ∧ gop t a b = false) then 1 else 0) +
    (if b = false ∧ ¬ (¬ last ∧ gop t a b = false) then 1 else 0) +
    (if (¬ last ∧ gop t a b = false) ∧ a = false ∧ b = false then 1 else 0) +
    (if U then 1 else 0) + (if B then 1 else 0) ≤ 1 + (if last then 1 else 0) := by
  by_cases hl : last <;> by_cases hu : U <;> by_cases hb : B <;>
    cases t <;> cases a <;> cases b <;> simp_all [gop]

def falseInner (n : ℕ) (D : Dag) (base : Fin n → Bool) : Finset ℕ :=
  (inner n D).filter (fun w => val D base w = false)

def falseFlow_exits (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => supp n D (n+j) ∩ P = ∅ ∧
    ((supp n D (opA D j) ∩ P).Nonempty ∨ (supp n D (opB D j) ∩ P).Nonempty))

lemma false_inner_operand {n : ℕ} {D : Dag} (normal : Strict n D)
    (base : Fin n → Bool) {j : ℕ} (hj : j < D.length) :
    (opA D j ∈ falseInner n D base ↔ val D base (opA D j) = false) ∧
    (opB D j ∈ falseInner n D base ↔ val D base (opB D j) = false) := by
  obtain ⟨ha,hb,_⟩ := normal j hj
  simp only [falseInner,Finset.mem_filter,sb_mem_inner]
  constructor <;> constructor
  · exact And.right
  · intro hv; exact ⟨by omega,hv⟩
  · exact And.right
  · intro hv; exact ⟨by omega,hv⟩

lemma false_inner_gate {n : ℕ} {D : Dag} (base : Fin n → Bool)
    {j : ℕ} (hj : j < D.length) :
    n+j ∈ falseInner n D base ↔ ((¬ (j+1 = D.length)) ∧ val D base (n+j) = false) := by
  simp only [falseInner,Finset.mem_filter,sb_mem_inner]
  constructor
  · rintro ⟨hl,hv⟩
    exact ⟨by omega,hv⟩
  · rintro ⟨hl,hv⟩
    exact ⟨by omega,hv⟩

lemma false_inner_sources {n : ℕ} {D : Dag} (h : StrictLive n D)
    (base : Fin n → Bool) :
    (sources n (falseInner n D base)).card =
      ((Finset.univ : Finset (Fin n)).filter (fun i => base i = false)).card := by
  have positive : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have equal : sources n (falseInner n D base) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => base i = false)).image Fin.val) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hf,hin⟩ := Finset.mem_filter.mp hw
      have zero := (Finset.mem_filter.mp hf).2
      rw [val_input D base w hin] at zero
      exact Finset.mem_image.mpr ⟨⟨w,hin⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,zero⟩,rfl⟩
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,i.isLt⟩
      · apply sb_mem_inner.mpr
        have := i.isLt
        omega
      · rw [val_input D base i.val i.isLt]
        exact (Finset.mem_filter.mp hi).2
  rw [equal,Finset.card_image_of_injective _ Fin.val_injective]

lemma false_inner_flow {n : ℕ} {D : Dag} (h : StrictLive n D)
    (base : Fin n → Bool) :
    (exitArcs n D (falseInner n D base)).card +
      (merges n D (falseInner n D base)).card =
      ((Finset.univ : Finset (Fin n)).filter (fun i => base i = false)).card +
      surplusOn D (falseInner n D base) := by
  rw [← false_inner_sources h base]
  apply carrier_flow h _ (Finset.filter_subset _ _)
  intro j hj hout
  have hz := (Finset.mem_filter.mp hout).2
  rw [val_gate h.1 base j hj] at hz
  obtain ⟨ea,eb⟩ := false_inner_operand h.1 base hj
  change opA D j ∈ falseInner n D base ∨ opB D j ∈ falseInner n D base
  rw [ea,eb]
  cases ht : tag D j <;> cases ha : val D base (opA D j) <;>
    cases hb : val D base (opB D j) <;> simp_all [gop]

lemma false_flow_gate_bound {n : ℕ} {D : Dag} (h : StrictLive n D)
    (P : Finset (Fin n)) (base : Fin n → Bool) (hP : ∀ v ∈ P, base v = true)
    (zero : val D base (outW n D) = false) {j : ℕ} (hj : j < D.length) :
    (if opA D j ∈ falseInner n D base ∧ n+j ∉ falseInner n D base then 1 else 0) +
    (if opB D j ∈ falseInner n D base ∧ n+j ∉ falseInner n D base then 1 else 0) +
    (if n+j ∈ falseInner n D base ∧ opA D j ∈ falseInner n D base ∧
      opB D j ∈ falseInner n D base then 1 else 0) +
    (if j ∈ falseFlow_exits n D P then 1 else 0) +
    (if j ∈ sup_big n D P then 1 else 0) ≤ 1 + (if j+1 = D.length then 1 else 0) := by
  have carrier_true (w : ℕ) (hw : (supp n D w ∩ P).Nonempty) : val D base w = true := by
    obtain ⟨v,hv⟩ := hw
    exact sem_val_of_supp h.1 (Finset.mem_inter.mp hv).1 (hP v (Finset.mem_inter.mp hv).2)
  have hU : j ∈ falseFlow_exits n D P → tag D j = true ∧
      (val D base (opA D j) = true ∨ val D base (opB D j) = true) := by
    intro hu
    obtain ⟨_,empty,enter⟩ := Finset.mem_filter.mp hu
    have hand : tag D j = true := by
      cases ht : tag D j
      · have out : (supp n D (n+j) ∩ P).Nonempty := by
          rw [sem_supp_or h.1 hj ht,Finset.union_inter_distrib_right]
          rcases enter with ⟨v,hv⟩ | ⟨v,hv⟩
          · exact ⟨v,Finset.mem_union.mpr (Or.inl hv)⟩
          · exact ⟨v,Finset.mem_union.mpr (Or.inr hv)⟩
        exact False.elim (out.ne_empty empty)
      · rfl
    exact ⟨hand,enter.imp (carrier_true _) (carrier_true _)⟩
  have hB : j ∈ sup_big n D P → val D base (opA D j) = true ∧ val D base (opB D j) = true := by
    intro hb
    have merge := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    exact ⟨carrier_true _ (Finset.mem_filter.mp merge.2.1).2,
      carrier_true _ (Finset.mem_filter.mp merge.2.2).2⟩
  have disj : ¬ (j ∈ falseFlow_exits n D P ∧ j ∈ sup_big n D P) := by
    rintro ⟨hu,hb⟩
    have empty := (Finset.mem_filter.mp hu).2.1
    have out := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.1).2
    exact out.ne_empty empty
  have last : j+1 = D.length → gop (tag D j)
      (val D base (opA D j)) (val D base (opB D j)) = false := by
    intro hl
    rw [← val_gate h.1 base j hj]
    have equal : n+j = outW n D := by unfold outW; omega
    rw [equal]
    exact zero
  obtain ⟨ea,eb⟩ := false_inner_operand h.1 base hj
  simp only [ea,eb,false_inner_gate base hj,val_gate h.1 base j hj]
  exact false_flow_boolean _ _ _ _ _ _ last hU hB disj

lemma false_flow_sum_card (m : ℕ) (S : Finset ℕ) (sub : S ⊆ Finset.range m) :
    (∑ j ∈ Finset.range m, if j ∈ S then 1 else 0) = S.card := by
  rw [← Finset.card_filter]
  congr 1
  ext j
  constructor
  · intro hj; exact (Finset.mem_filter.mp hj).2
  · intro hj; exact Finset.mem_filter.mpr ⟨sub hj,hj⟩

lemma false_surplus_bound {n : ℕ} {D : Dag} (h : StrictLive n D)
    (P : Finset (Fin n)) (base : Fin n → Bool) (hP : ∀ v ∈ P, base v = true)
    (zero : val D base (outW n D) = false) :
    surplusOn D (falseInner n D base) +
      ((Finset.univ : Finset (Fin n)).filter (fun i => base i = false)).card +
      (falseFlow_exits n D P).card + (sup_big n D P).card ≤ D.length + 1 := by
  have positive : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have flow := false_inner_flow h base
  have exitSum : (exitArcs n D (falseInner n D base)).card =
      ∑ j ∈ Finset.range D.length,
        ((if opA D j ∈ falseInner n D base ∧ n+j ∉ falseInner n D base then 1 else 0) +
        (if opB D j ∈ falseInner n D base ∧ n+j ∉ falseInner n D base then 1 else 0)) := by
    rw [exitArcs,sb_card_arcs_filter]
    simp only [sb_src_false,sb_src_true]
  have mergeSum : (merges n D (falseInner n D base)).card =
      ∑ j ∈ Finset.range D.length,
        if n+j ∈ falseInner n D base ∧ opA D j ∈ falseInner n D base ∧
          opB D j ∈ falseInner n D base then 1 else 0 := by
    rw [merges,Finset.card_filter]
  have sumU := false_flow_sum_card D.length (falseFlow_exits n D P) (Finset.filter_subset _ _)
  have bigSub : sup_big n D P ⊆ Finset.range D.length :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have sumB := false_flow_sum_card D.length (sup_big n D P) bigSub
  have lastSet : (Finset.range D.length).filter (fun j => j+1 = D.length) =
      {D.length-1} := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
    omega
  have lastSum : (∑ j ∈ Finset.range D.length, if j+1 = D.length then 1 else 0) = 1 := by
    rw [← Finset.card_filter,lastSet,Finset.card_singleton]
  have bound := Finset.sum_le_sum (s := Finset.range D.length)
    (fun j hj => false_flow_gate_bound h P base hP zero (Finset.mem_range.mp hj))
  simp only [Finset.sum_add_distrib] at bound exitSum
  rw [sumU,sumB,lastSum] at bound
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] at bound
  omega

end PEqualNP.Outside.L_meta_6659_aux
