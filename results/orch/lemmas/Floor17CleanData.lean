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

end PEqualNP.Outside.L_meta_2592.Full
