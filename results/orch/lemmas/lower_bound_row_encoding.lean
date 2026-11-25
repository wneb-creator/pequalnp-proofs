import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.RowEncoding

abbrev Row := Fin 1024
abbrev Sig := BitVec 1024

def position : Fin 10 → Fin 10 := ![9,7,5,8,6,4,2,0,3,1]
def variableAt : Fin 10 → Fin 10 := ![7,9,6,8,5,2,4,1,3,0]

lemma variableAt_position : ∀ j : Fin 10, variableAt (position j) = j := by decide +kernel
lemma position_variableAt : ∀ j : Fin 10, position (variableAt j) = j := by decide +kernel

def decode (r : Row) (j : Fin 10) : Bool :=
  (BitVec.ofFin r : BitVec 10).getLsbD (position j).val

def encode (x : Fin 10 → Bool) : Row :=
  let word : BitVec 10 :=
    (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 10 => x (variableAt j)))).cast List.length_ofFn
  word.toFin

lemma decode_encode (x : Fin 10 → Bool) : decode (encode x) = x := by
  funext j
  simp only [decode, encode, BitVec.ofFin_toFin, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [Fin.isLt, dite_true, Option.getD_some]
  change x (variableAt (position j)) = x j
  rw [variableAt_position]

lemma encode_decode : ∀ r : Row, encode (decode r) = r := by
  decide +kernel

lemma decode_injective : Function.Injective decode :=
  Function.LeftInverse.injective encode_decode

lemma encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

def move (p : Fin 10 → Fin 10) (r : Row) : Row := encode (fun j => decode r (p j))

lemma decode_move (p : Fin 10 → Fin 10) (r : Row) (j : Fin 10) :
    decode (move p r) j = decode r (p j) := by
  rw [move,decode_encode]

lemma move_injective (p : Fin 10 → Fin 10) (hp : Function.Surjective p) :
    Function.Injective (move p) := by
  intro r s h
  apply decode_injective
  funext j
  obtain ⟨j,rfl⟩ := hp j
  have hh := congrArg (fun t => decode t j) h
  simpa only [decode_move] using hh

lemma move_surjective (p : Fin 10 → Fin 10) (hp : Function.Surjective p) :
    Function.Surjective (move p) :=
  ((Fintype.bijective_iff_injective_and_card (move p)).mpr
    ⟨move_injective p hp, rfl⟩).2

def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val

def table (f : Row → Bool) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

lemma bit_table (f : Row → Bool) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [r.isLt]

lemma bit_ext {a b : Sig} (h : ∀ r, bit r a = bit r b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact h ⟨j,hj⟩

def transform (p : Fin 10 → Fin 10) (a : Sig) : Sig :=
  table (fun r => bit (move p r) a)

lemma bit_transform (p : Fin 10 → Fin 10) (a : Sig) (r : Row) :
    bit r (transform p a) = bit (move p r) a := bit_table _ _

lemma transform_injective (p : Fin 10 → Fin 10) (hp : Function.Surjective p) :
    Function.Injective (transform p) := by
  intro a b h
  apply bit_ext
  intro r
  obtain ⟨r,rfl⟩ := move_surjective p hp r
  have hh := congrArg (bit r) h
  simpa only [bit_transform] using hh

lemma transform_zero (p : Fin 10 → Fin 10) : transform p 0 = 0 := by
  apply bit_ext
  intro r
  rw [bit_transform]
  simp [bit]

lemma transform_one (p : Fin 10 → Fin 10) :
    transform p (BitVec.allOnes 1024) = BitVec.allOnes 1024 := by
  apply bit_ext
  intro r
  rw [bit_transform]
  unfold bit
  rw [BitVec.getLsbD_allOnes,BitVec.getLsbD_allOnes]
  simp

lemma bit_and (a b : Sig) (r : Row) : bit r (a &&& b) = (bit r a && bit r b) := by
  simp [bit]

lemma bit_or (a b : Sig) (r : Row) : bit r (a ||| b) = (bit r a || bit r b) := by
  simp [bit]

lemma bit_not (a : Sig) (r : Row) : bit r (~~~a) = !(bit r a) := by
  simp [bit,r.isLt]

lemma transform_and (p : Fin 10 → Fin 10) (a b : Sig) :
    transform p (a &&& b) = transform p a &&& transform p b := by
  apply bit_ext
  intro r
  rw [bit_transform,bit_and,bit_and,bit_transform,bit_transform]

lemma transform_or (p : Fin 10 → Fin 10) (a b : Sig) :
    transform p (a ||| b) = transform p a ||| transform p b := by
  apply bit_ext
  intro r
  rw [bit_transform,bit_or,bit_or,bit_transform,bit_transform]

lemma transform_not (p : Fin 10 → Fin 10) (a : Sig) :
    transform p (~~~a) = ~~~transform p a := by
  apply bit_ext
  intro r
  rw [bit_transform,bit_not,bit_not,bit_transform]

end PEqualNP.Outside.L_meta_2592_aux.RowEncoding
