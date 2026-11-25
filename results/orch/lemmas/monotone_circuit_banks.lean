import mode_realize
import input_relabel

namespace PEqualNP.Outside.L_meta_1886_aux.MonotoneCircuitBanks

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Stronger
open Extended CanonicalBank

lemma pins_plain : pins.all plainWord = true := by decide +kernel

lemma canonical_plain : ∀ (d : Fin 4) (j : Fin 2), (bank d j).all plainWord = true := by
  decide +kernel

def other (j : Fin 2) : Fin 10 := ⟨j.val + 1,by omega⟩

lemma other_zero : other 0 = 1 := by decide +kernel

def supplied (d : Fin 4) (j : Fin 2) (x : Fin 10 → Bool) : Bool :=
  if d.val = 0 then x 0 && x (other j)
  else if d.val = 1 then x 0 || x (other j)
  else if d.val = 2 then x 0 && !(x (other j))
  else !(x 0) && x (other j)

lemma canonical_rows (d : Fin 4) (j : Fin 2) (r : Extended.Row) :
    (bank d j).map (bit r) = List.ofFn (assign r) ++ [supplied d j (assign r)] := by
  have hb : bit r (extra d j) = supplied d j (assign r) := by
    rw [CanonicalBank.extra,transport_bit_bin]
    rfl
  simp only [bank,List.map_append,rowPins,List.map_cons,List.map_nil,hb]

lemma realize_raw (C : Circuit) (p : Fin 10 → Fin 10)
    (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p)) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ pins := by
  let D := InputRelabel.circuit p C
  have dm : Monotone2 D := InputRelabel.circuit_mono p C mono
  have dc : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f10 x := by
    intro x
    have he := InputRelabel.circuit_eval p C x []
    simp only [List.append_nil] at he
    exact he.trans (computes x)
  obtain ⟨k,S,hk,run,raw⟩ := realizeMonotoneBank D pins dm pins_plain (fun r => by
    rw [rowPins,dc,rowTarget])
  refine ⟨k,S,?_,run,raw⟩
  simpa only [D,InputRelabel.circuit_size] using hk

lemma realize_canonical (C : Circuit) (p : Fin 10 → Fin 10) (d : Fin 4) (j : Fin 2)
    (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [supplied d j x]) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ bank d j := by
  let D := InputRelabel.circuit p C
  have dm : Monotone2 D := InputRelabel.circuit_mono p C mono
  have dc : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [supplied d j x]) = f10 x := by
    intro x
    exact (InputRelabel.circuit_eval p C x [supplied d j x]).trans (computes x)
  obtain ⟨k,S,hk,run,raw⟩ := realizeMonotoneBank D (bank d j) dm (canonical_plain d j) (fun r => by
    rw [canonical_rows,dc,rowTarget])
  refine ⟨k,S,?_,run,raw⟩
  simpa only [D,InputRelabel.circuit_size] using hk

lemma realize_supplied (C : Circuit) (p : Fin 10 → Fin 10) (choice : Bool)
    (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [if choice = true then x 0 && x 1 else x 0 || x 1]) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧
      ∀ a ∈ S, a ∈ bank (if choice = true then 0 else 1) 0 := by
  apply realize_canonical C p (if choice = true then 0 else 1) 0 mono
  intro x
  cases choice <;> simpa [supplied,other_zero] using computes x

end PEqualNP.Outside.L_meta_1886_aux.MonotoneCircuitBanks
