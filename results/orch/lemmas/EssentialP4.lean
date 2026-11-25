import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448.essentialP4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wide : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def short : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 6]⟩], 7⟩

def val (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def killedFirst : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, []⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def killedLast : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [1, 2]⟩, ⟨.or, []⟩], 8⟩

lemma wide_fun : ∀ x, circuitFun 4 wide x = val x := by decide

lemma short_fun : ∀ x, circuitFun 4 short x = val x := by decide

lemma killedFirst_fun : ∀ x, circuitFun 4 killedFirst x = false := by decide

lemma killedLast_fun : ∀ x, circuitFun 4 killedLast x = false := by decide

lemma wide_mono : Monotone2 wide := by simp [Monotone2, wide]

lemma short_mono : Monotone2 short := by simp [Monotone2, short]

lemma wide_size : wide.size = 5 := rfl

lemma short_size : short.size = 4 := rfl

lemma not_total_minimum : ¬ IsMinimalMonoCircuit 4 wide := by
  intro h
  have hF : circuitFun 4 short = circuitFun 4 wide := by
    funext x
    rw [short_fun, wide_fun]
  have hsize := h.2 short short_mono hF
  change 5 ≤ 4 at hsize
  omega

def adj (a b : Fin 4) : Prop := a.val + 1 = b.val ∨ b.val + 1 = a.val

lemma no_triangle : ∀ a b c, adj a b → adj b c → ¬ adj c a := by
  unfold adj
  decide

lemma no_four_cycle : ∀ a b c d,
    adj a b → adj b c → adj c d → adj d a → a = c ∨ b = d := by
  unfold adj
  decide

lemma no_star : ¬ ∃ center : Fin 4, ∀ a b, adj a b → a = center ∨ b = center := by
  unfold adj
  decide

lemma edges_accepted : ∀ a b, adj a b →
    val (fun v => decide (v = a ∨ v = b)) = true := by
  unfold adj
  decide

def andCount (C : Circuit) : ℕ := C.gates.countP fun g =>
  match g.op with
  | .and => true
  | _ => false

lemma wide_ands : andCount wide = 2 := rfl

lemma short_ands : andCount short = 2 := rfl

end PEqualNP.Outside.L_meta_2448.essentialP4
