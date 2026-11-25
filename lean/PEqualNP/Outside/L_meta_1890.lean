import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def reviewEdges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(6,9),(6,8),(5,8)]

def reviewInput (s : Nat) (i : Fin 10) : Bool := s.testBit i.val

def reviewEdge (s : Nat) : Bool :=
  reviewEdges.any fun e => s.testBit e.1 && s.testBit e.2

def reviewBoundary : List Nat :=
  reviewEdges.map (fun e => 2^e.1 + 2^e.2) ++
  [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]

def reviewCandidate : Circuit :=
  ⟨[⟨.or,[2,3]⟩, ⟨.or,[11,7]⟩, ⟨.and,[0,12]⟩,
    ⟨.or,[3,4]⟩, ⟨.or,[14,8]⟩, ⟨.and,[1,15]⟩,
    ⟨.or,[4,5]⟩, ⟨.and,[2,17]⟩,
    ⟨.and,[3,5]⟩, ⟨.and,[4,6]⟩,
    ⟨.or,[13,16]⟩, ⟨.or,[21,18]⟩, ⟨.or,[22,19]⟩,
    ⟨.or,[23,20]⟩, ⟨.not,[24]⟩],25⟩

def reviewPins (s : Nat) : List Bool :=
  List.ofFn (reviewInput s) ++ [s.testBit 0 && s.testBit 2]

lemma reviewCandidate_fan : FanInTwo reviewCandidate := by
  simp [FanInTwo, reviewCandidate]
lemma reviewCandidate_size : reviewCandidate.size = 15 := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma reviewCandidate_boundary :
    reviewBoundary.all (fun s => reviewCandidate.eval (reviewPins s) == reviewEdge s) = true := by
  decide +kernel

lemma reviewCandidate_wrong :
    reviewCandidate.eval (reviewPins 0) ≠ reviewEdge 0 := by decide +kernel

end PEqualNP.Outside.L_meta_1890
