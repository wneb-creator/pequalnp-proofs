import FewNotBase

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

def inputBit : Fin 10 → Fin 10 := ![9,7,5,8,6,4,2,0,3,1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma assign_testBit : ∀ (r : Row) (i : Fin 10), assign r i = r.val.testBit (inputBit i).val := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def encode (x : Fin 10 → Bool) : Row :=
  let v : BitVec 10 := (BitVec.ofBoolListLE [x 7,x 9,x 6,x 8,x 5,x 2,x 4,x 1,x 3,x 0]).cast rfl
  v.toFin

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma assign_encode (x : Fin 10 → Bool) (i : Fin 10) : assign (encode x) i = x i := by
  rw [assign_testBit]
  change (BitVec.ofBoolListLE [x 7,x 9,x 6,x 8,x 5,x 2,x 4,x 1,x 3,x 0]).getLsbD (inputBit i).val = x i
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl

def rowMove (σ : Fin 10 → Fin 10) (r : Row) : Row :=
  encode (fun i => assign r (σ i))

lemma rowMove_assign (σ : Fin 10 → Fin 10) (r : Row) (i : Fin 10) :
    assign (rowMove σ r) i = assign r (σ i) := assign_encode _ i

lemma rowMove_target (σ : Fin 10 → Fin 10)
    (invariant : ∀ x : Fin 10 → Bool, f10 (fun i => x (σ i)) = f10 x) (r : Row) :
    bit (rowMove σ r) target = bit r target := by
  rw [rowTarget,rowTarget]
  have hx : assign (rowMove σ r) = fun i => assign r (σ i) := funext (rowMove_assign σ r)
  rw [hx]
  exact invariant _

end PEqualNP.Outside.L_meta_2592.FewNot.Extended

namespace PEqualNP.Outside.L_meta_2592.FewNot

def vertexEmbedding (σ : Fin 10 → Fin 10) (r : Row) : Extended.Row :=
  Extended.rowMove σ (embed r)

lemma vertexEmbedding_assign (σ : Fin 10 → Fin 10) (r : Row) (i : Fin 10) :
    Extended.assign (vertexEmbedding σ r) i = Extended.assign (embed r) (σ i) :=
  Extended.rowMove_assign σ (embed r) i

lemma vertexEmbedding_pin (σ : Fin 10 → Fin 10) (i : Fin 10) :
    (fun r : Row => Extended.bit (vertexEmbedding σ r) (Extended.pins.getD i.val Extended.zero)) =
      (fun r : Row => Extended.bit (embed r) (Extended.pins.getD (σ i).val Extended.zero)) := by
  funext r
  exact vertexEmbedding_assign σ r i

lemma vertexEmbedding_target (σ : Fin 10 → Fin 10)
    (invariant : ∀ x : Fin 10 → Bool, Extended.f10 (fun i => x (σ i)) = Extended.f10 x) :
    (fun r : Row => Extended.bit (vertexEmbedding σ r) Extended.target) =
      (fun r : Row => Extended.bit (embed r) Extended.target) := by
  funext r
  rw [Extended.rowTarget,Extended.rowTarget]
  have hx : Extended.assign (vertexEmbedding σ r) = fun i => Extended.assign (embed r) (σ i) :=
    funext (vertexEmbedding_assign σ r)
  rw [hx]
  exact invariant _

lemma embed_first_zero (r : Row) : Extended.assign (embed r) 0 = false := by
  rw [Extended.assign_testBit]
  change r.val.testBit 9 = false
  have h : ∀ r : Row, r.val.testBit 9 = false := by decide +kernel
  exact h r

lemma vertexEmbedding_zero (σ : Fin 10 → Fin 10) (i : Fin 10) (hi : σ i = 0) :
    (fun r : Row => Extended.bit (vertexEmbedding σ r) (Extended.pins.getD i.val Extended.zero)) =
      fun _ => false := by
  funext r
  change Extended.assign (vertexEmbedding σ r) i = false
  rw [vertexEmbedding_assign,hi,embed_first_zero]

end PEqualNP.Outside.L_meta_2592.FewNot
