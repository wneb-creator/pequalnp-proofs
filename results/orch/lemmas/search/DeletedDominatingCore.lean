namespace PEqualNP.Outside.L_meta_2592_aux

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def petersenValue (x : Fin 10 → Bool) : Bool :=
  petersenEdges.any (fun e => x e.1 && x e.2)

def petersenIndependentMasks : List Nat :=
  [69, 521, 385, 138, 50, 770, 276, 548, 104, 208, 773, 201, 554, 402, 116]

def petersenMaskInput (m : Nat) (i : Fin 10) : Bool :=
  m.testBit i.val

set_option maxHeartbeats 400000 in
theorem petersen_deleted_dominating (x : Fin 10 → Bool)
    (h0 : x 0 = false) (h1 : x 1 = false) (h4 : x 4 = false) (h5 : x 5 = false)
    (independent : petersenValue x = false)
    (dom1 : (x 2 || x 6) = true) (dom4 : (x 3 || x 9) = true)
    (dom5 : (x 7 || x 8) = true) :
    x = petersenMaskInput 772 ∨ x = petersenMaskInput 200 := by
  cases h2 : x 2 <;> cases h3 : x 3 <;> cases h6 : x 6 <;>
    cases h7 : x 7 <;> cases h8 : x 8 <;> cases h9 : x 9 <;>
    simp_all [petersenValue, petersenEdges, funext_iff,
      Fin.forall_fin_succ, petersenMaskInput] <;> decide

end PEqualNP.Outside.L_meta_2592_aux
