import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.SemanticAllInputs

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def bits (r : ℕ) (i : Fin 10) : Bool := r.testBit i.val

def vertex (v : Fin 9) : Fin 10 := ⟨v.val + 1, by omega⟩

def sensitiveRows (v : Fin 9) : List ℕ :=
  ![[1, 4, 5, 9, 20, 36, 52, 64, 65, 68, 69, 72, 73, 80, 84, 96, 100, 104, 112, 116, 129, 137, 192, 193, 200, 201, 208, 257, 260, 261, 276, 385, 513, 516, 517, 521, 548, 769, 772, 773],
    [2, 8, 9, 10, 18, 34, 40, 42, 50, 72, 73, 104, 128, 129, 130, 136, 137, 138, 144, 146, 192, 193, 200, 201, 208, 258, 274, 384, 385, 386, 400, 402, 514, 520, 521, 522, 546, 552, 554, 770],
    [4, 5, 16, 18, 20, 36, 48, 50, 52, 68, 69, 80, 84, 100, 112, 116, 144, 146, 208, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402, 516, 517, 548, 768, 769, 770, 772, 773],
    [1, 5, 8, 9, 10, 40, 42, 65, 69, 72, 73, 104, 129, 136, 137, 138, 193, 200, 201, 257, 261, 385, 512, 513, 514, 516, 517, 520, 521, 522, 544, 546, 548, 552, 554, 768, 769, 770, 772, 773],
    [1, 5, 9, 65, 69, 73, 128, 129, 130, 136, 137, 138, 144, 146, 192, 193, 200, 201, 208, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402, 513, 517, 521, 768, 769, 770, 772, 773],
    [2, 10, 18, 34, 42, 50, 130, 138, 146, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402, 512, 513, 514, 516, 517, 520, 521, 522, 544, 546, 548, 552, 554, 768, 769, 770, 772, 773],
    [4, 5, 20, 32, 34, 36, 40, 42, 48, 50, 52, 68, 69, 84, 96, 100, 104, 112, 116, 260, 261, 276, 512, 513, 514, 516, 517, 520, 521, 522, 544, 546, 548, 552, 554, 768, 769, 770, 772, 773],
    [8, 9, 10, 32, 34, 36, 40, 42, 48, 50, 52, 64, 65, 68, 69, 72, 73, 80, 84, 96, 100, 104, 112, 116, 136, 137, 138, 192, 193, 200, 201, 208, 520, 521, 522, 544, 546, 548, 552, 554],
    [16, 18, 20, 48, 50, 52, 64, 65, 68, 69, 72, 73, 80, 84, 96, 100, 104, 112, 116, 128, 129, 130, 136, 137, 138, 144, 146, 192, 193, 200, 201, 208, 272, 274, 276, 384, 385, 386, 400, 402]] v

def rootValue (r : ℕ) (a : Fin 11) : Bool :=
  if a.val = 10 then !(r.testBit 0) else r.testBit a.val

def binary (op a b : Bool) : Bool := if op then a || b else a && b

def edges : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adjacent (a b : Fin 11) : Prop :=
  (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma sensitiveRows_correct : ∀ (v : Fin 9) (r : ℕ), r ∈ sensitiveRows v →
    bits r (vertex v) = false ∧ target (bits r) = false ∧
      target (Function.update (bits r) (vertex v) true) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma first_binary_boolean_check : ∀ (v : Fin 9) (a b : Fin 11) (hop gop : Bool),
    a ≠ b → a.val ≠ (vertex v).val → b.val ≠ (vertex v).val →
    (sensitiveRows v).all (fun r =>
      decide (binary hop (rootValue r a) (rootValue r b) = !gop)) = true →
    (((a = 0 ∧ b = 10) ∨ (a = 10 ∧ b = 0)) ∧ hop ≠ gop) ∨
      (hop = false ∧ gop = true ∧ adjacent a b) := by
  unfold adjacent
  decide +kernel

lemma first_binary_classification (v : Fin 9) (a b : Fin 11) (hop gop : Bool)
    (different : a ≠ b) (outsideA : a.val ≠ (vertex v).val)
    (outsideB : b.val ≠ (vertex v).val)
    (preserves : ∀ r ∈ sensitiveRows v,
      binary hop (rootValue r a) (rootValue r b) = !gop) :
    (((a = 0 ∧ b = 10) ∨ (a = 10 ∧ b = 0)) ∧ hop ≠ gop) ∨
      (hop = false ∧ gop = true ∧ adjacent a b) := by
  apply first_binary_boolean_check v a b hop gop different outsideA outsideB
  simpa only [List.all_eq_true, decide_eq_true_eq] using preserves

end PEqualNP.Outside.L_meta_2592_aux.SemanticAllInputs
