import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2592_aux

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

abbrev Wire (R : Type) := R → Bool

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]

def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

namespace Extended

abbrev Sig := BitVec 1024

abbrev Row := Fin 1024

def zero : Sig := 0

def bin (d : Nat) (a b : Sig) : Sig := if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val

def observe (a : Sig) : Wire Row := fun r => bit r a

def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]

def initial : List Sig := pins

def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

end Extended

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux

def primaryWire (i : Fin 10) : Extended.Sig := Extended.initial.getD i.val Extended.zero

lemma primaryWire_list : List.ofFn primaryWire = Extended.initial := rfl

lemma initial_mem_index (a : Extended.Sig) : a ∈ Extended.initial ↔ ∃ i : Fin 10, primaryWire i = a := by
  rw [← primaryWire_list, List.mem_ofFn]

lemma primaryWire_mem (i : Fin 10) : primaryWire i ∈ Extended.initial :=
  (initial_mem_index _).mpr ⟨i, rfl⟩

def projectionMasks (i : Fin 10) : List Nat :=
  ([[1,2,4,8,16,32,64,128,256],
    [8,16,1,2,4,256,512,32,64],
    [2,4,8,16,1,64,128,256,512],
    [16,1,2,4,8,512,32,64,128],
    [4,8,16,1,2,128,256,512,32],
    [64,256,32,128,512,2,8,1,4],
    [512,64,256,32,128,16,2,8,1],
    [128,512,64,256,32,4,16,2,8],
    [32,128,512,64,256,1,4,16,2],
    [256,32,128,512,64,8,1,4,16]] : List (List Nat)).getD i.val []

def projectionRows (i : Fin 10) (r : Row) : Extended.Row :=
  ⟨((List.range 9).foldl (fun z b =>
    if r.val.testBit b then z ||| (projectionMasks i).getD b 0 else z) 0) % 1024,
    Nat.mod_lt _ (by decide)⟩

def projectedAt (i : Fin 10) (a : Extended.Sig) : Sig :=
  table fun r => Extended.bit (projectionRows i r) a

lemma observe_projectedAt (i : Fin 10) (a : Extended.Sig) :
    restrictRows (projectionRows i) (Extended.observe a) = observe (projectedAt i a) := by
  funext r
  exact (bit_table _ _).symm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectedAt_target : ∀ i : Fin 10, projectedAt i Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectedAt_primary : ∀ i : Fin 10, projectedAt i (primaryWire i) = zero := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectedAt_permitted : ∀ i : Fin 10,
    Extended.initial.all (fun a => (projectedAt i a == zero) || inputs.contains (projectedAt i a)) = true := by
  decide +kernel

lemma projection_bit_bin (r : Row) (d : Nat) (a b : Sig) : bit r (bin d a b) =
    (if d = 0 then bit r a && bit r b else if d = 1 then bit r a || bit r b else
      if d = 2 then bit r a && !(bit r b) else !(bit r a) && bit r b) := by
  unfold bin
  split_ifs <;> simp [bit]

lemma projection_extended_bit_bin (r : Extended.Row) (d : Nat) (a b : Extended.Sig) :
    Extended.bit r (Extended.bin d a b) =
      (if d = 0 then Extended.bit r a && Extended.bit r b else
        if d = 1 then Extended.bit r a || Extended.bit r b else
          if d = 2 then Extended.bit r a && !(Extended.bit r b) else
            !(Extended.bit r a) && Extended.bit r b) := by
  unfold Extended.bin
  split_ifs <;> simp [Extended.bit]

lemma projectedAt_bin (i : Fin 10) (d : Nat) (a b : Extended.Sig) :
    projectedAt i (Extended.bin d a b) = bin d (projectedAt i a) (projectedAt i b) := by
  apply bit_ext
  intro r
  change bit r (table _) = _
  rw [bit_table, projection_extended_bit_bin, projection_bit_bin]
  simp only [projectedAt, bit_table]


end PEqualNP.Outside.L_meta_2592_aux
