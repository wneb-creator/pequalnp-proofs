import Mathlib

namespace PEqualNP.Outside.L_meta_2592_aux.SignedEncoding

def evalSigned (op : Fin 4) (a b : Bool) : Bool :=
  match op.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

def signedParams (op : Fin 4) : Bool × Bool × Bool :=
  match op.val with
  | 0 => (false, false, false)
  | 1 => (true, true, true)
  | 2 => (false, true, false)
  | _ => (true, false, false)

def normalCode : Bool → Bool → Bool → Fin 4 × Bool
  | false, false, false => (0, false)
  | false, false, true => (2, false)
  | false, true, false => (3, false)
  | false, true, true => (1, true)
  | true, false, false => (1, false)
  | true, false, true => (3, true)
  | true, true, false => (2, true)
  | true, true, true => (0, true)

lemma signed_zero : ∀ op : Fin 4, evalSigned op false false = false := by
  decide +kernel

lemma signed_params_correct : ∀ (op : Fin 4) (a b : Bool),
    evalSigned op a b =
      Bool.xor ((Bool.xor a (signedParams op).1) &&
        (Bool.xor b (signedParams op).2.1)) (signedParams op).2.2 := by
  decide +kernel

lemma normal_code_correct : ∀ (disj pa pb a b : Bool),
    Bool.xor (evalSigned (normalCode disj pa pb).1 a b) (normalCode disj pa pb).2 =
      if disj then (Bool.xor a pa) || (Bool.xor b pb)
      else (Bool.xor a pa) && (Bool.xor b pb) := by
  decide +kernel

lemma normal_code_baseline : ∀ (disj pa pb : Bool),
    (normalCode disj pa pb).2 = if disj then pa || pb else pa && pb := by
  decide +kernel

lemma normal_code_physical_params : ∀ (disj pa pb : Bool),
    let code := normalCode disj pa pb
    let ps := signedParams code.1
    Bool.xor ps.2.2 code.2 = disj ∧
      Bool.xor ps.1 (Bool.xor ps.2.2 code.2) = pa ∧
      Bool.xor ps.2.1 (Bool.xor ps.2.2 code.2) = pb := by
  decide +kernel

lemma physical_gate_decode : ∀ (a b ca cb co pa pb pj : Bool),
    let za := Bool.xor a pa
    let zb := Bool.xor b pb
    let da := Bool.xor pa (Bool.xor ca (Bool.xor co pj))
    let db := Bool.xor pb (Bool.xor cb (Bool.xor co pj))
    let output := if Bool.xor co pj then (Bool.xor za da) || (Bool.xor zb db)
      else (Bool.xor za da) && (Bool.xor zb db)
    output = Bool.xor (Bool.xor ((Bool.xor a ca) && (Bool.xor b cb)) co) pj := by
  decide +kernel

def normalValue {α : Type} (z : α) (f : α → Bool) (x : α) : Bool :=
  Bool.xor (f x) (f z)

lemma normalValue_zero {α : Type} (z : α) (f : α → Bool) : normalValue z f z = false := by
  simp [normalValue]

lemma normalValue_not {α : Type} (z : α) (f : α → Bool) :
    normalValue z (fun x => !f x) = normalValue z f := by
  funext x
  change Bool.xor (!(f x)) (!(f z)) = Bool.xor (f x) (f z)
  cases f x <;> cases f z <;> rfl

lemma recoverValue {α : Type} (z : α) (f : α → Bool) (x : α) :
    Bool.xor (normalValue z f x) (f z) = f x := by
  unfold normalValue
  cases f x <;> cases f z <;> rfl

end PEqualNP.Outside.L_meta_2592_aux.SignedEncoding
