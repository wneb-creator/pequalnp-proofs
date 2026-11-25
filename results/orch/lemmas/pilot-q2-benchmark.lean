import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6659_aux

def q2_bit (m : Fin 128) (t : Fin 7) : Bool :=
  ![![false,false,false,false,false,false,false],![true,false,false,false,false,false,false],![false,true,false,false,false,false,false],![true,true,false,false,false,false,false],![false,false,true,false,false,false,false],![true,false,true,false,false,false,false],![false,true,true,false,false,false,false],![true,true,true,false,false,false,false],![false,false,false,true,false,false,false],![true,false,false,true,false,false,false],![false,true,false,true,false,false,false],![true,true,false,true,false,false,false],![false,false,true,true,false,false,false],![true,false,true,true,false,false,false],![false,true,true,true,false,false,false],![true,true,true,true,false,false,false],![false,false,false,false,true,false,false],![true,false,false,false,true,false,false],![false,true,false,false,true,false,false],![true,true,false,false,true,false,false],![false,false,true,false,true,false,false],![true,false,true,false,true,false,false],![false,true,true,false,true,false,false],![true,true,true,false,true,false,false],![false,false,false,true,true,false,false],![true,false,false,true,true,false,false],![false,true,false,true,true,false,false],![true,true,false,true,true,false,false],![false,false,true,true,true,false,false],![true,false,true,true,true,false,false],![false,true,true,true,true,false,false],![true,true,true,true,true,false,false],![false,false,false,false,false,true,false],![true,false,false,false,false,true,false],![false,true,false,false,false,true,false],![true,true,false,false,false,true,false],![false,false,true,false,false,true,false],![true,false,true,false,false,true,false],![false,true,true,false,false,true,false],![true,true,true,false,false,true,false],![false,false,false,true,false,true,false],![true,false,false,true,false,true,false],![false,true,false,true,false,true,false],![true,true,false,true,false,true,false],![false,false,true,true,false,true,false],![true,false,true,true,false,true,false],![false,true,true,true,false,true,false],![true,true,true,true,false,true,false],![false,false,false,false,true,true,false],![true,false,false,false,true,true,false],![false,true,false,false,true,true,false],![true,true,false,false,true,true,false],![false,false,true,false,true,true,false],![true,false,true,false,true,true,false],![false,true,true,false,true,true,false],![true,true,true,false,true,true,false],![false,false,false,true,true,true,false],![true,false,false,true,true,true,false],![false,true,false,true,true,true,false],![true,true,false,true,true,true,false],![false,false,true,true,true,true,false],![true,false,true,true,true,true,false],![false,true,true,true,true,true,false],![true,true,true,true,true,true,false],![false,false,false,false,false,false,true],![true,false,false,false,false,false,true],![false,true,false,false,false,false,true],![true,true,false,false,false,false,true],![false,false,true,false,false,false,true],![true,false,true,false,false,false,true],![false,true,true,false,false,false,true],![true,true,true,false,false,false,true],![false,false,false,true,false,false,true],![true,false,false,true,false,false,true],![false,true,false,true,false,false,true],![true,true,false,true,false,false,true],![false,false,true,true,false,false,true],![true,false,true,true,false,false,true],![false,true,true,true,false,false,true],![true,true,true,true,false,false,true],![false,false,false,false,true,false,true],![true,false,false,false,true,false,true],![false,true,false,false,true,false,true],![true,true,false,false,true,false,true],![false,false,true,false,true,false,true],![true,false,true,false,true,false,true],![false,true,true,false,true,false,true],![true,true,true,false,true,false,true],![false,false,false,true,true,false,true],![true,false,false,true,true,false,true],![false,true,false,true,true,false,true],![true,true,false,true,true,false,true],![false,false,true,true,true,false,true],![true,false,true,true,true,false,true],![false,true,true,true,true,false,true],![true,true,true,true,true,false,true],![false,false,false,false,false,true,true],![true,false,false,false,false,true,true],![false,true,false,false,false,true,true],![true,true,false,false,false,true,true],![false,false,true,false,false,true,true],![true,false,true,false,false,true,true],![false,true,true,false,false,true,true],![true,true,true,false,false,true,true],![false,false,false,true,false,true,true],![true,false,false,true,false,true,true],![false,true,false,true,false,true,true],![true,true,false,true,false,true,true],![false,false,true,true,false,true,true],![true,false,true,true,false,true,true],![false,true,true,true,false,true,true],![true,true,true,true,false,true,true],![false,false,false,false,true,true,true],![true,false,false,false,true,true,true],![false,true,false,false,true,true,true],![true,true,false,false,true,true,true],![false,false,true,false,true,true,true],![true,false,true,false,true,true,true],![false,true,true,false,true,true,true],![true,true,true,false,true,true,true],![false,false,false,true,true,true,true],![true,false,false,true,true,true,true],![false,true,false,true,true,true,true],![true,true,false,true,true,true,true],![false,false,true,true,true,true,true],![true,false,true,true,true,true,true],![false,true,true,true,true,true,true],![true,true,true,true,true,true,true]] m t

def q2_ctx (c : Fin 34) (i : Fin 5) : Fin 128 :=
  ![![99,11,69,99,49],![102,11,69,102,49],![103,11,69,103,49],![103,11,103,103,49],![106,11,69,106,49],![107,11,69,107,49],![107,107,69,107,49],![110,11,69,110,49],![111,11,69,111,49],![111,11,111,111,49],![111,111,69,111,49],![111,111,111,111,49],![114,11,69,114,49],![115,11,69,115,49],![115,11,69,115,115],![118,11,69,118,49],![119,11,69,119,49],![119,11,69,119,119],![119,11,119,119,49],![119,11,119,119,119],![122,11,69,122,49],![123,11,69,123,49],![123,11,69,123,123],![123,123,69,123,49],![123,123,69,123,123],![126,11,69,126,49],![127,11,69,127,49],![127,11,69,127,127],![127,11,127,127,49],![127,11,127,127,127],![127,127,69,127,49],![127,127,69,127,127],![127,127,127,127,49],![127,127,127,127,127]] c i

def q2_unit (c : Fin 34) (k : Fin 33) : Fin 128 :=
  ![0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,64,65,66,68,72,80,96,11,69,49,q2_ctx c 0] k

def q2_nb (i : Fin 4) : Fin 128 := ![11,69,98,49] i

def q2_shared (x t : Fin 7) : Bool :=
  ![![true,true,true,true,true,true,true],![true,true,false,true,false,false,false],![true,false,true,false,false,false,true],![true,true,false,true,false,false,false],![true,false,false,false,true,true,false],![true,false,false,false,true,true,false],![true,false,true,false,false,false,true]] x t

def q2_count (u v w : Fin 128) (t : Fin 7) : ℕ :=
  (q2_bit u t).toNat + (q2_bit v t).toNat + (q2_bit w t).toNat

def q2_sub (u v w : Fin 128) (x t : Fin 7) : Bool :=
  (!q2_bit u x || q2_bit u t) && (!q2_bit v x || q2_bit v t) &&
    (!q2_bit w x || q2_bit w t)

def q2_empty (u v w : Fin 128) (x : Fin 7) : Bool :=
  !q2_bit u x && !q2_bit v x && !q2_bit w x

def q2_force (u v w : Fin 128) (x t : Fin 7) : Bool :=
  q2_sub u v w x t && (!q2_empty u v w x || q2_shared x t)

def q2_row (u v w : Fin 128) (i : Fin 4) (t : Fin 7) : Bool :=
  ![q2_force u v w 0 t || q2_force u v w 1 t || q2_force u v w 3 t,q2_force u v w 0 t || q2_force u v w 2 t || q2_force u v w 6 t,q2_force u v w 1 t || q2_force u v w 5 t || q2_force u v w 6 t,q2_force u v w 0 t || q2_force u v w 4 t || q2_force u v w 5 t] i

def q2_budget_at (c : Fin 34) (u v w : Fin 128) (t : Fin 7) : Bool :=
  decide ((q2_bit (q2_ctx c 1) t).toNat + (q2_bit (q2_ctx c 2) t).toNat +
    (q2_bit (q2_ctx c 3) t).toNat + (q2_bit (q2_ctx c 4) t).toNat +
    (if t = 0 then 0 else 1) ≤ 2 + q2_count u v w t)

def q2_budget (c : Fin 34) (u v w : Fin 128) : Bool :=
  q2_budget_at c u v w 0 && q2_budget_at c u v w 1 && q2_budget_at c u v w 2 && q2_budget_at c u v w 3 && q2_budget_at c u v w 4 && q2_budget_at c u v w 5 && q2_budget_at c u v w 6

def q2_center (u v w : Fin 128) : Bool :=
  decide (q2_count u v w 0 + (q2_sub u v w 1 0).toNat + (q2_sub u v w 2 0).toNat + (q2_sub u v w 3 0).toNat + (q2_sub u v w 4 0).toNat + (q2_sub u v w 5 0).toNat + (q2_sub u v w 6 0).toNat ≤ 5)

def q2_labels (c : Fin 34) (u v w : Fin 128) : Bool :=
  (!q2_row u v w 0 0 || q2_bit (q2_ctx c 1) 0) &&
    (!q2_row u v w 0 1 || q2_bit (q2_ctx c 1) 1) &&
    (!q2_row u v w 0 2 || q2_bit (q2_ctx c 1) 2) &&
    (!q2_row u v w 0 3 || q2_bit (q2_ctx c 1) 3) &&
    (!q2_row u v w 0 4 || q2_bit (q2_ctx c 1) 4) &&
    (!q2_row u v w 0 5 || q2_bit (q2_ctx c 1) 5) &&
    (!q2_row u v w 0 6 || q2_bit (q2_ctx c 1) 6) &&
    (!q2_row u v w 1 0 || q2_bit (q2_ctx c 2) 0) &&
    (!q2_row u v w 1 1 || q2_bit (q2_ctx c 2) 1) &&
    (!q2_row u v w 1 2 || q2_bit (q2_ctx c 2) 2) &&
    (!q2_row u v w 1 3 || q2_bit (q2_ctx c 2) 3) &&
    (!q2_row u v w 1 4 || q2_bit (q2_ctx c 2) 4) &&
    (!q2_row u v w 1 5 || q2_bit (q2_ctx c 2) 5) &&
    (!q2_row u v w 1 6 || q2_bit (q2_ctx c 2) 6) &&
    (!q2_row u v w 2 0 || q2_bit (q2_ctx c 3) 0) &&
    (!q2_row u v w 2 1 || q2_bit (q2_ctx c 3) 1) &&
    (!q2_row u v w 2 2 || q2_bit (q2_ctx c 3) 2) &&
    (!q2_row u v w 2 3 || q2_bit (q2_ctx c 3) 3) &&
    (!q2_row u v w 2 4 || q2_bit (q2_ctx c 3) 4) &&
    (!q2_row u v w 2 5 || q2_bit (q2_ctx c 3) 5) &&
    (!q2_row u v w 2 6 || q2_bit (q2_ctx c 3) 6) &&
    (!q2_row u v w 3 0 || q2_bit (q2_ctx c 4) 0) &&
    (!q2_row u v w 3 1 || q2_bit (q2_ctx c 4) 1) &&
    (!q2_row u v w 3 2 || q2_bit (q2_ctx c 4) 2) &&
    (!q2_row u v w 3 3 || q2_bit (q2_ctx c 4) 3) &&
    (!q2_row u v w 3 4 || q2_bit (q2_ctx c 4) 4) &&
    (!q2_row u v w 3 5 || q2_bit (q2_ctx c 4) 5) &&
    (!q2_row u v w 3 6 || q2_bit (q2_ctx c 4) 6)

def q2_bad (c : Fin 34) (a b d : Fin 33) : Bool :=
  let u := q2_unit c a
  let v := q2_unit c b
  let w := q2_unit c d
  q2_center u v w && q2_budget c u v w && q2_labels c u v w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_benchmark : ∀ b d : Fin 33, q2_bad 0 0 b d = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_6659_aux
