import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Signed
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Row := Fin 512
abbrev Wire (R : Type) := R → Bool
def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
lemma observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
namespace Extended
abbrev Sig := BitVec 1024
def zero : Sig := 0
abbrev Row := Fin 1024
def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val
def observe (a : Sig) : Wire Row := fun r => bit r a
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
end Extended
def vertexMoves : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [3, 2, 1, 0, 4, 8, 7, 6, 5, 9], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [3, 2, 1, 6, 8, 4, 7, 0, 9, 5], [8, 3, 2, 1, 6, 5, 4, 7, 0, 9], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]
def pinPositions : List Nat := [9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def rowsAt (v : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 (((List.range 10).map fun i =>
    if r.val.testBit (pinPositions.getD ((vertexMoves.getD v.val []).getD i 0) 0)
    then 2 ^ (pinPositions.getD i 0) else 0).sum)

def projectedBy (v : Fin 10) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (rowsAt v r) a)

lemma observe_projectedBy (v : Fin 10) (a : Extended.Sig) :
    restrictRows (rowsAt v) (Extended.observe a) = observe (projectedBy v a) := by
  exact (observe_table _).symm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectionChecked : ∀ v : Fin 10,
    projectedBy v Extended.target = graph ∧
    projectedBy v (Extended.pins.getD v.val Extended.zero) = zero ∧
    Extended.pins.all (fun a => (projectedBy v a == zero) || inputs.contains (projectedBy v a)) = true := by
  decide +kernel

lemma pin_projection (a : Extended.Sig) (mem : a ∈ Extended.pins) :
    ∃ rows : Row → Extended.Row,
      Constant (restrictRows rows (Extended.observe a)) ∧
      restrictRows rows (Extended.observe Extended.target) = observe graph ∧
      ∀ b ∈ Extended.pins,
        Available true (inputs.map observe) (restrictRows rows (Extended.observe b)) := by
  have listing : List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) =
      Extended.pins := by rfl
  rw [←listing] at mem
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp mem
  obtain ⟨targetEq, zeroEq, supplyEq⟩ := projectionChecked v
  have isZero : observe zero = fun _ => false := by funext r; simp [observe, bit, zero]
  refine ⟨rowsAt v, ?_, ?_, ?_⟩
  · rw [observe_projectedBy, zeroEq]
    exact ⟨false, isZero⟩
  · rw [observe_projectedBy, targetEq]
  · intro b hb
    rw [observe_projectedBy]
    have allowed := List.all_eq_true.mp supplyEq b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at allowed
    rcases allowed with hz | hin
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hin, rfl⟩)

end PEqualNP.Outside.L_meta_2592.Signed
