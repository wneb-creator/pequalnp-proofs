import PEqualNP.Defs
import PackedDecoder

namespace PEqualNP.Outside.L_meta_2732_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def prefixWitness (F : (Fin 14 → Bool) → Bool)
    (a b : Fin 14) (c d : Fin 15) (op₁ op₂ : GateOp) (D : Circuit) : Prop :=
  a < b ∧ c < d ∧
  (op₁ = GateOp.and ∨ op₁ = GateOp.or) ∧
  (op₂ = GateOp.and ∨ op₂ = GateOp.or) ∧
  Monotone2 D ∧ D.size ≤ 24 ∧
  ∀ x : Fin 14 → Bool,
    let w := List.ofFn x ++ [op₁.eval [x a, x b]]
    D.eval (w ++ [op₂.eval [w.getD c.val false, w.getD d.val false]]) = F x

end PEqualNP.Outside.L_meta_2732_aux

namespace PEqualNP.Outside.L_meta_2732_aux.PackedWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def op (b : Bool) : GateOp := if b then GateOp.or else GateOp.and

def code (a b : ℕ) (o : Bool) : ℕ := a + 64 * b + if o then 4096 else 0

def program (a b : Fin 14) (c d : Fin 15) (u v : Bool) (tail : List ℕ) : List ℕ :=
  code a.val b.val u :: code c.val d.val v :: tail

def tailCircuit (tail : List ℕ) : Circuit := ⟨tail.map Packed.X3, 15 + tail.length⟩

def target (x : Fin 14 → Bool) : Bool :=
  decide (∃ u v : Fin 14, (u.val, v.val) ∈ Packed.edges ∧ x u = true ∧ x v = true)

lemma op_ok (b : Bool) : op b = GateOp.and ∨ op b = GateOp.or := by
  cases b <;> simp [op]

lemma code_gate (a b : ℕ) (o : Bool) (ha : a < 64) (hb : b < 64) :
    Packed.X3 (code a b o) = ⟨op o, [a, b]⟩ := by
  cases o
  · have h : a + 64 * b < 4096 := by omega
    have h1 : (a + 64 * b) % 64 = a := by omega
    have h2 : (a + 64 * b) / 64 % 64 = b := by omega
    simp [Packed.X3, code, op, h, h1, h2]
  · have h : ¬ a + 64 * b + 4096 < 4096 := by omega
    have h1 : (a + 64 * b + 4096) % 64 = a := by omega
    have h2 : (a + 64 * b + 4096) / 64 % 64 = b := by omega
    simp [Packed.X3, code, op, h, h1, h2]

lemma raw (a b : Fin 14) (c d : Fin 15) (u v : Bool) (tail : List ℕ)
    (hab : a < b) (hcd : c < d) (hlen : tail.length ≤ 24)
    (hcheck : ((program a b c d u v tail).foldl Packed.X2 Packed.nums).getD
      (15 + tail.length) 0 = 2097151) :
    prefixWitness target a b c d (op u) (op v) (tailCircuit tail) := by
  refine ⟨hab, hcd, op_ok u, op_ok v, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hg
    by_cases ht : t < 4096 <;> simp [Packed.X3, ht]
  · change (tail.map Packed.X3).length ≤ 24
    simpa using hlen
  · intro x
    let P := program a b c d u v tail
    have el : 13 + P.length = 15 + tail.length := by simp [P, program]; omega
    have hp : (P.foldl Packed.X2 Packed.nums).getD (13 + P.length) 0 = 2097151 := by
      rw [el]
      exact hcheck
    have ev := Packed.decode P hp x
    rw [el] at ev
    change (Circuit.mk
      (Packed.X3 (code a.val b.val u) :: Packed.X3 (code c.val d.val v) :: tail.map Packed.X3)
      (15 + tail.length)).eval (List.ofFn x) = target x at ev
    rw [code_gate a.val b.val u (by have := a.isLt; omega) (by have := b.isLt; omega),
      code_gate c.val d.val v (by have := c.isLt; omega) (by have := d.isLt; omega)] at ev
    let w := List.ofFn x
    let pref := w ++ [(op u).eval [w.getD a.val false, w.getD b.val false]]
    change (tailCircuit tail).eval
      (pref ++ [(op v).eval [pref.getD c.val false, pref.getD d.val false]]) = target x at ev
    have get (i : Fin 14) : w.getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp [w]), List.getElem_ofFn]
    have eq : pref = w ++ [(op u).eval [x a, x b]] := by
      rw [← get a, ← get b]
    rw [eq] at ev
    exact ev

end PEqualNP.Outside.L_meta_2732_aux.PackedWitness
