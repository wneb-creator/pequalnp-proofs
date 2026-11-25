import Floor17Data
namespace PEqualNP.Outside.L_meta_2592.Full

lemma raw_bank : inputs.map observe = List.ofFn raw := by
  rw [← input_list,List.map_ofFn]
  rfl

lemma raw_mem (i : Fin 10) : raw i ∈ inputs.map observe := by
  rw [raw_bank]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

lemma raw_bank_nodup : (inputs.map observe).Nodup := by
  have inj : Function.Injective observe := by
    intro a b h
    have he := congrArg table h
    simpa only [table_observe] using he
  exact (show inputs.Nodup by decide +kernel).map inj

def projectRow (v : Fin 10) (r : Deleted.Row) : Row :=
  Fin.ofNat 1024 ((List.range 10).foldl
    (fun acc i => if r.val.testBit (PEqualNP.Outside.L_meta_2592_aux.vertexAuto v ⟨i % 10,Nat.mod_lt _ (by decide)⟩).val
      then acc ||| (1 <<< i) else acc) 0)

def projectedRaw (v i : Fin 10) : Deleted.Sig :=
  Deleted.inputs.getD (PEqualNP.Outside.L_meta_2592_aux.vertexAuto v i).val Deleted.zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma project_raw_bits : ∀ (v i : Fin 10) (r : Deleted.Row),
    raw i (projectRow v r) = Deleted.bit r (projectedRaw v i) := by
  intro v i
  fin_cases v <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma project_graph_bits : ∀ (v : Fin 10) (r : Deleted.Row),
    observe graph (projectRow v r) = Deleted.observe Deleted.graph r := by
  intro v
  fin_cases v <;> decide +kernel

lemma project_raw (v i : Fin 10) : restrictRows (projectRow v) (raw i) =
    Deleted.observe (projectedRaw v i) := by
  funext r
  exact project_raw_bits v i r

lemma project_graph (v : Fin 10) : restrictRows (projectRow v) (observe graph) =
    Deleted.observe Deleted.graph := by
  funext r
  exact project_graph_bits v r

lemma project_zero (v : Fin 10) : restrictRows (projectRow v) (raw v) = fun _ => false := by
  rw [project_raw]
  have hv : PEqualNP.Outside.L_meta_2592_aux.vertexAuto v v = 9 := by
    simpa only [PEqualNP.Outside.L_meta_2592_aux.vertexAuto_nine] using
      PEqualNP.Outside.L_meta_2592_aux.vertexAuto_involutive v 9
  simp only [projectedRaw,hv]
  change Deleted.observe Deleted.zero = fun _ => false
  funext r
  simp [Deleted.observe,Deleted.bit,Deleted.zero]

lemma project_available (v i : Fin 10) :
    Available true (Deleted.inputs.map Deleted.observe) (restrictRows (projectRow v) (raw i)) := by
  rw [project_raw]
  have free : ∀ j : Fin 10, Deleted.freeWord Deleted.inputs
      (Deleted.inputs.getD j.val Deleted.zero) = true := by decide +kernel
  exact Deleted.freeWord_ok (free (PEqualNP.Outside.L_meta_2592_aux.vertexAuto v i))

lemma projected_first_available (d : Fin 4) (a b : Fin 10) :
    Available true (Deleted.inputs.map Deleted.observe)
      (restrictRows (projectRow a) (comb d.val (raw a) (raw b))) := by
  rw [restrict_comb,project_zero]
  have h : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 := by omega
  rcases h with h | h | h | h
  · simp only [h,comb,ite_true,combine,Bool.false_eq_true,ite_false,Bool.false_and]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · simpa [h,comb,combine] using project_available a b
  · simp only [h,comb,combine,inv,ite_true,ite_false,Bool.false_and]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · simpa [h,comb,combine,inv] using project_available a b

lemma cost_le_mass {R : Type} (w : Wire R) (xs : List (Wire R)) (hw : w ∈ xs) :
    cost w ≤ mass xs := by
  induction xs with
  | nil => simp at hw
  | cons x xs ih =>
    rw [mass_cons]
    rcases List.mem_cons.mp hw with rfl | h
    · omega
    · have := ih h
      omega

lemma first_suffix_floor {k : Nat} (d : Fin 4) (a b : Fin 10)
    (run : Run true (observe graph) k (comb d.val (raw a) (raw b) :: inputs.map observe)) : 16 ≤ k := by
  have nc : ¬ Constant (restrictRows (projectRow a) (observe graph)) := by
    rw [project_graph]
    exact Deleted.observe_proper Deleted.graph_proper
  have supplied : supply true (Deleted.inputs.map Deleted.observe)
      ((comb d.val (raw a) (raw b) :: inputs.map observe).map (restrictRows (projectRow a))) := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hz with rfl | hz
    · exact projected_first_available d a b
    · rw [raw_bank] at hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact project_available a i
  have low : ∀ q bs, Reach true (Deleted.inputs.map Deleted.observe) q bs →
      Available true bs (restrictRows (projectRow a) (observe graph)) → 15 ≤ q := by
    intro q bs hq hit
    rw [project_graph] at hit
    exact Deleted.signed_lower q bs (reach_deleted hq) hit
  have bound := projected_bound (projectRow a) run nc Reach.start supplied low
  have zeroMem : (fun _ : Deleted.Row => false) ∈
      (comb d.val (raw a) (raw b) :: inputs.map observe).map (restrictRows (projectRow a)) := by
    rw [← project_zero a]
    exact List.mem_map_of_mem (List.mem_cons_of_mem _ (raw_mem a))
  have massLo := cost_le_mass _ _ zeroMem
  have cz : cost (fun _ : Deleted.Row => false) = 1 := by
    classical
    simp [cost,Constant]
  rw [cz] at massLo
  omega

end PEqualNP.Outside.L_meta_2592.Full
