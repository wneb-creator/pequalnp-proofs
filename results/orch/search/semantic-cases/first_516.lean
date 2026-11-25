import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate

def initial : List (BitVec 10) :=
  [0, 1, 2, 4, 8, 16, 32, 64, 113, 128, 204, 256, 387, 512, 550, 792, 1023]

def extend (xs : List (BitVec 10)) (v : BitVec 10) : List (BitVec 10) :=
  (xs ++ xs.map (fun u => u &&& v)).eraseDups

def ors (xs : List (BitVec 10)) : List (BitVec 10) :=
  (xs.flatMap (fun a => xs.map (fun b => a ||| b))).eraseDups

def full (xs : List (BitVec 10)) : List (BitVec 10) :=
  xs.filter (fun u => (u &&& 31) == 31)

def finish (xs : List (BitVec 10)) : Bool :=
  (full xs).all (fun u => xs.all (fun a => xs.all (fun b => !((u &&& (a ||| b)) == 31))))

def checkFirst (v : BitVec 10) : Bool :=
  let xs := extend initial v
  (ors xs).all (fun w => finish (extend xs w))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_516 : checkFirst 516 = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate

#print axioms PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate.first_516
