import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_9033_aux

def edges : List (Fin 256) := [65, 129, 10, 34, 20, 132, 40, 136, 48, 80, 96]

def negatives : List (Fin 256) := [7, 13, 19, 25, 37, 70, 76, 146, 160, 194]

def columns : List Nat := [2147418115, 663661903884, 34144976944,
  21653750532, 103293914128, 414195942664, 581968119809, 1065151898146]

def rows : List (Fin 256) := [65, 129, 10, 34, 20, 132, 0, 0, 40, 136,
  48, 80, 0, 128, 64, 96, 7, 13, 19, 25, 7, 13, 19, 25, 7, 13,
  19, 25, 37, 37, 37, 70, 76, 70, 76, 146, 146, 160, 160, 194]

abbrev submask (a b : Fin 256) : Prop := a.val &&& b.val = a.val

def edgeFunction (x : Fin 256) : Bool := edges.any fun e => decide (submask e x)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma column_rows : ∀ (i : Fin 8) (k : Fin 40),
    (columns.getD i.val 0).testBit k.val =
      (rows.getD k.val 0).val.testBit i.val := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma target_rows : ∀ k : Fin 40,
    edgeFunction (rows.getD k.val 0) = (36671 : Nat).testBit k.val := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma negatives_appear : ∀ n ∈ negatives,
    ∃ k : Fin 24, rows.getD (16 + k.val) 0 = n := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma independent_covered : ∀ x : Fin 256, edgeFunction x = false →
    ∃ y ∈ negatives, submask x y := by
  decide +kernel

lemma monotone_table_unique (f : Fin 256 → Bool)
    (mono : ∀ a b, submask a b → f a = true → f b = true)
    (positive : ∀ e ∈ edges, f e = true)
    (negative : ∀ n ∈ negatives, f n = false) :
    ∀ x, f x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨n, hn, hxn⟩ := independent_covered x hx
    cases hfx : f x with
    | false => rfl
    | true =>
      have hntrue := mono x n hxn hfx
      rw [negative n hn] at hntrue
      contradiction
  | true =>
    obtain ⟨e, he, hex⟩ := List.any_eq_true.mp hx
    exact mono e x (of_decide_eq_true hex) (positive e he)

namespace CoreMIM

abbrev G (n : Nat) := List (Fin n × Fin n)

def noLoop {n : Nat} (E : G n) : Bool := E.all fun e => e.1 != e.2

def isIM {n : Nat} (E : G n) (m : Nat) : Bool :=
  E.all fun e => !(m.testBit e.1.val && m.testBit e.2.val)

def isMIM (n : Nat) (E : G n) (m : Nat) : Bool :=
  isIM E m && (List.finRange n).all fun v =>
    m.testBit v.val || !isIM E (Nat.lor m (1 <<< v.val))

def mIMs (n : Nat) (E : G n) : List Nat :=
  (List.range (2 ^ n)).filter (isMIM n E)

def coreEdges : G 5 := [(0, 2), (0, 4), (1, 2), (1, 3), (2, 3)]

set_option maxRecDepth 10000 in
lemma core_loopless : noLoop coreEdges = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma core_maximal_independent_sets : mIMs 5 coreEdges = [3, 9, 18, 20, 24] := by
  decide +kernel

lemma core_mk3_premise : noLoop coreEdges = true ∧ 5 ≤ (mIMs 5 coreEdges).length := by
  rw [core_maximal_independent_sets]
  exact ⟨core_loopless, by decide⟩

end CoreMIM


end PEqualNP.Outside.L_meta_9033_aux
