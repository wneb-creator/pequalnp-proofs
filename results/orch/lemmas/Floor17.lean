import FullExtension
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_meta_2592.Full

lemma kept_inputs_mem {R : Type} (ka kb : Bool) (a b w : Wire R)
    (rest : List (Wire R)) (hw : w ∈ kept ka a (kept kb b rest)) :
    w ∈ a :: b :: rest := by
  cases ka <;> cases kb <;> simp_all [kept] <;> tauto

lemma Run.rows_agree {R : Type} {u : Bool} {goal : Wire R} {k : Nat}
    {ws : List (Wire R)} (h : Run u goal k ws) (r s : R)
    (agree : ∀ w ∈ ws, w r = w s) : goal r = goal s := by
  induction h using Run.ind with
  | stop => exact agree goal (by simp)
  | perm hp h ih =>
    apply ih
    intro w hw
    exact agree w (hp.mem_iff.mp hw)
  | @two k a b rest op hd ka kb h ih =>
    apply ih
    intro w hw
    rcases List.mem_cons.mp hw with heq | hw
    · subst w
      have ha := agree a (by simp)
      have hb := agree b (by simp)
      unfold comb
      split_ifs <;> simp [combine, inv, ha, hb]
    · exact agree w (kept_inputs_mem ka kb a b w rest hw)

lemma Run.separates {R : Type} {u : Bool} {goal : Wire R} {k : Nat}
    {ws : List (Wire R)} (h : Run u goal k ws) (r s : R)
    (different : goal r ≠ goal s) : ∃ w ∈ ws, w r ≠ w s := by
  by_contra hn
  push_neg at hn
  exact different (Run.rows_agree h r s hn)

end PEqualNP.Outside.L_meta_2592.Full


namespace PEqualNP.Outside.L_meta_2592_aux

def vertexAuto (v : Fin 10) : Fin 10 → Fin 10 :=
  ![![9, 7, 2, 3, 4, 6, 5, 1, 8, 0],
    ![7, 9, 4, 3, 2, 5, 6, 0, 8, 1],
    ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
    ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
    ![7, 2, 1, 6, 9, 5, 3, 0, 8, 4],
    ![6, 1, 2, 3, 8, 9, 0, 7, 4, 5],
    ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
    ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
    ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma vertexAuto_involutive : ∀ (v i : Fin 10), vertexAuto v (vertexAuto v i) = i := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma vertexAuto_nine : ∀ v : Fin 10, vertexAuto v 9 = v := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592.Full

def firstRows : Array Nat := #[0,0,16,4,2,2,2,4,2,8,2,128,2,2,2,4,2,8,2,16,4,16,0,0,1,8,1,4,1,1,1,1,1,256,1,4,1,8,1,16,2,2,8,1,0,0,2,16,2,1,2,1,2,2,2,32,2,8,2,16,4,2,4,1,16,2,0,0,4,1,4,1,4,2,4,4,4,32,4,16,8,2,1,1,1,2,1,4,0,0,1,1,1,2,1,4,1,8,1,64,128,2,1,1,1,2,1,4,1,1,0,0,1,2,1,4,1,8,1,16,2,2,256,1,2,2,2,4,2,1,2,1,0,0,2,4,2,8,2,16,4,2,4,1,32,2,4,4,4,1,4,1,4,2,0,0,4,8,4,16,8,2,8,1,8,2,32,4,8,1,8,1,8,2,8,4,0,0,8,16,16,2,16,1,16,2,16,4,64,1,16,1,16,2,16,4,16,8,0,0,0,0,2,1,20,9,10,5,16,1,32,1,80,257,130,5,258,9,514,65,1,2,0,0,4,2,9,18,20,10,36,130,64,2,129,34,257,10,513,18,9,20,2,4,0,0,8,4,18,5,34,5,72,260,128,4,258,36,514,20,5,10,18,9,4,8,0,0,16,8,36,9,68,10,144,40,256,8,516,72,1,16,10,20,5,18,8,16,0,0,40,144,65,18,129,20,257,48,512,16,1,32,130,36,5,34,9,36,144,40,0,0,65,34,128,32,256,32,513,48,257,80,2,64,260,72,10,68,18,65,34,65,0,0,130,68,256,64,512,64,5,130,34,129,4,128,40,144,20,129,32,128,68,130,0,0,260,136,512,128,9,258,10,257,36,258,8,256,48,257,32,256,64,256,136,260,0,0,520,272,65,514,18,513,20,514,72,516,16,512,48,513,64,512,128,512,272,520,0,0,0,0,2,4,20,2,10,4,16,8,32,128,80,2,130,4,258,8,514,16,1,16,0,0,4,8,9,4,20,1,36,1,64,256,129,4,257,8,513,16,9,2,2,1,0,0,8,16,18,1,34,1,72,2,128,32,258,8,514,16,5,2,18,1,4,2,0,0,16,1,36,1,68,2,144,4,256,32,516,16,1,2,10,1,5,2,8,4,0,0,40,1,65,2,129,4,257,8,512,64,1,2,130,1,5,2,9,4,144,1,0,0,65,2,128,4,256,8,513,16,257,2,2,1,260,2,10,4,18,1,34,1,0,0,130,4,256,8,512,16,5,2,34,1,4,2,40,4,20,1,32,1,68,2,0,0,260,8,512,16,9,2,10,1,36,2,8,4,48,1,32,1,64,2,136,4,0,0,520,16,65,2,18,1,20,2,72,4,16,1,48,1,64,2,128,4,272,8,0,0,0,0,16,1,2,9,2,5,2,1,2,1,2,257,2,5,2,9,2,65,4,2,0,0,1,2,1,18,1,10,1,130,1,2,1,34,1,10,1,18,2,20,8,4,0,0,2,4,2,5,2,5,2,260,2,4,2,36,2,20,4,10,4,9,16,8,0,0,4,8,4,9,4,10,4,40,4,8,4,72,8,16,1,20,1,18,1,16,0,0,1,144,1,18,1,20,1,48,1,16,128,32,1,36,1,34,1,36,1,40,0,0,1,34,1,32,1,32,1,48,2,80,256,64,2,72,2,68,2,65,2,65,0,0,2,68,2,64,2,64,4,130,4,129,32,128,4,144,4,129,4,128,4,130,0,0,4,136,4,128,8,258,8,257,8,258,32,256,8,257,8,256,8,256,8,260,0,0,8,272,16,514,16,513,16,514,16,516,64,512,16,513,16,512,16,512,16,520,0,0]

def raw (i : Fin 10) : Wire Row := observe (inputs.getD i.val zero)
def firstRow (d : Fin 4) (a b i : Fin 10) : Row :=
  Fin.ofNat 1024 ((firstRows[d.val * 200 + a.val * 20 + b.val * 2 + (if i = a then 0 else 1)]?).getD 0)
def changedRow (d : Fin 4) (a b i : Fin 10) : Row :=
  Fin.ofNat 1024 ((firstRow d a b i).val ||| (1 <<< i.val))

abbrev FirstProperty (d : Fin 4) (a : Fin 10) : Prop :=
  ∀ (b i : Fin 10), a ≠ b → (i = a ∨ i = b) →
    observe graph (firstRow d a b i) ≠ observe graph (changedRow d a b i) ∧
    comb d.val (raw a) (raw b) (firstRow d a b i) =
      comb d.val (raw a) (raw b) (changedRow d a b i) ∧
    ∀ j : Fin 10, j ≠ i → raw j (firstRow d a b i) = raw j (changedRow d a b i)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_0 : FirstProperty 0 0 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_1 : FirstProperty 0 1 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_2 : FirstProperty 0 2 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_3 : FirstProperty 0 3 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_4 : FirstProperty 0 4 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_5 : FirstProperty 0 5 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_6 : FirstProperty 0 6 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_7 : FirstProperty 0 7 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_8 : FirstProperty 0 8 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_0_9 : FirstProperty 0 9 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_0 : FirstProperty 1 0 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_1 : FirstProperty 1 1 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_2 : FirstProperty 1 2 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_3 : FirstProperty 1 3 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_4 : FirstProperty 1 4 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_5 : FirstProperty 1 5 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_6 : FirstProperty 1 6 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_7 : FirstProperty 1 7 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_8 : FirstProperty 1 8 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_1_9 : FirstProperty 1 9 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_0 : FirstProperty 2 0 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_1 : FirstProperty 2 1 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_2 : FirstProperty 2 2 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_3 : FirstProperty 2 3 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_4 : FirstProperty 2 4 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_5 : FirstProperty 2 5 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_6 : FirstProperty 2 6 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_7 : FirstProperty 2 7 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_8 : FirstProperty 2 8 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_2_9 : FirstProperty 2 9 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_0 : FirstProperty 3 0 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_1 : FirstProperty 3 1 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_2 : FirstProperty 3 2 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_3 : FirstProperty 3 3 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_4 : FirstProperty 3 4 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_5 : FirstProperty 3 5 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_6 : FirstProperty 3 6 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_7 : FirstProperty 3 7 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_8 : FirstProperty 3 8 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstWitness_3_9 : FirstProperty 3 9 := by decide +kernel

lemma first_witness (d : Fin 4) (a : Fin 10) : FirstProperty d a := by
  fin_cases d <;> fin_cases a
  · exact firstWitness_0_0
  · exact firstWitness_0_1
  · exact firstWitness_0_2
  · exact firstWitness_0_3
  · exact firstWitness_0_4
  · exact firstWitness_0_5
  · exact firstWitness_0_6
  · exact firstWitness_0_7
  · exact firstWitness_0_8
  · exact firstWitness_0_9
  · exact firstWitness_1_0
  · exact firstWitness_1_1
  · exact firstWitness_1_2
  · exact firstWitness_1_3
  · exact firstWitness_1_4
  · exact firstWitness_1_5
  · exact firstWitness_1_6
  · exact firstWitness_1_7
  · exact firstWitness_1_8
  · exact firstWitness_1_9
  · exact firstWitness_2_0
  · exact firstWitness_2_1
  · exact firstWitness_2_2
  · exact firstWitness_2_3
  · exact firstWitness_2_4
  · exact firstWitness_2_5
  · exact firstWitness_2_6
  · exact firstWitness_2_7
  · exact firstWitness_2_8
  · exact firstWitness_2_9
  · exact firstWitness_3_0
  · exact firstWitness_3_1
  · exact firstWitness_3_2
  · exact firstWitness_3_3
  · exact firstWitness_3_4
  · exact firstWitness_3_5
  · exact firstWitness_3_6
  · exact firstWitness_3_7
  · exact firstWitness_3_8
  · exact firstWitness_3_9

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

lemma first_keeps_all {k : Nat} {d : Fin 4} {a b : Fin 10} {ka kb : Bool}
    {rest : List (Wire Row)} (hab : a ≠ b)
    (perm : (raw a :: raw b :: rest).Perm (inputs.map observe))
    (run : Run true (observe graph) k
      (comb d.val (raw a) (raw b) :: kept ka (raw a) (kept kb (raw b) rest))) :
    ∀ i : Fin 10, (i = a ∨ i = b) → raw i ∈ kept ka (raw a) (kept kb (raw b) rest) := by
  intro i hi
  by_contra absent
  obtain ⟨different,gateSame,otherSame⟩ := first_witness d a b i hab hi
  apply different
  apply Run.rows_agree run
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact gateSame
  · have old := perm.mem_iff.mp (kept_inputs_mem ka kb (raw a) (raw b) w rest hw)
    rw [raw_bank] at old
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp old
    apply otherSame j
    rintro rfl
    exact absent hw

lemma first_split {k : Nat} (run : Run true (observe graph) k (inputs.map observe)) :
    ∃ (s : Nat) (d : Fin 4) (a b : Fin 10), k = s+1 ∧ a ≠ b ∧
      Run true (observe graph) s (comb d.val (raw a) (raw b) :: inputs.map observe) := by
  cases k with
  | zero =>
    change List.Perm [observe graph] (inputs.map observe) at run
    have len := run.length_eq
    simp only [List.length_cons,List.length_nil,List.length_map] at len
    have il : inputs.length = 10 := rfl
    omega
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,allowedOp,perm,tail⟩ := run
    have small : op < 4 := by
      rcases allowedOp with h | ⟨_,h⟩ <;> omega
    have ha := perm.mem_iff.mp (show a ∈ a :: b :: rest from by simp)
    have hb := perm.mem_iff.mp (show b ∈ a :: b :: rest from by simp)
    rw [raw_bank] at ha hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have nodup := perm.nodup_iff.mpr raw_bank_nodup
    have noA := (List.nodup_cons.mp nodup).1
    have noB := (List.nodup_cons.mp (List.nodup_cons.mp nodup).2).1
    have notEqual : raw i ≠ raw j := by
      intro h
      apply noA
      simp [h]
    have ij : i ≠ j := fun h => notEqual (congrArg raw h)
    have keptAll := first_keeps_all (d:=⟨op,small⟩) ij perm tail
    have kaTrue : ka = true := by
      cases ka
      · have h := keptAll i (Or.inl rfl)
        apply False.elim
        apply noA
        cases kb <;> simp_all [kept]
      · rfl
    have kbTrue : kb = true := by
      cases kb
      · have h := keptAll j (Or.inr rfl)
        rw [kaTrue] at h
        simp only [kept,ite_true,Bool.false_eq_true,ite_false,List.mem_cons] at h
        rcases h with h | h
        · exact False.elim (notEqual h.symm)
        · exact False.elim (noB h)
      · rfl
    refine ⟨s,⟨op,small⟩,i,j,rfl,ij,?_⟩
    rw [kaTrue,kbTrue] at tail
    simp only [kept,ite_true] at tail
    exact Run.perm (perm.cons _) tail

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

lemma binary_seventeen (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) :
    17 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨k,hk,run⟩ := circuit_run C legal computes
  obtain ⟨s,d,a,b,heq,_,tail⟩ := first_split run
  have hs := first_suffix_floor d a b tail
  omega

lemma seventeen_not_lower (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have lower := binary_seventeen C legal computes
  have total := count_partition C.gates
  rw [not_count_eq]
  change 17 + C.gates.countP isNot ≤ C.gates.length
  omega

lemma two_not_bound (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x)
    (small : C.size ≤ 19) : PEqualNP.NotBracket.notCount C ≤ 2 := by
  have lower := seventeen_not_lower C legal computes
  omega

end PEqualNP.Outside.L_meta_2592.Full
