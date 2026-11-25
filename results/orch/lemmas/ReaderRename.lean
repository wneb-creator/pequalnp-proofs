import ReaderDeletion
import PermutationSupport
import PermutationRename

namespace PEqualNP.Outside.L_meta_2592.ReaderDeletion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Automorphisms

def readsLiteral (i : Fin 10) (g : Gate) : Bool :=
  let xs := match g.op with | .not => g.inputs.take 1 | _ => g.inputs
  xs.contains i.val || xs.contains 10

lemma renamed_zero (σ : Equiv.Perm (Fin 10)) (i : Fin 10) (hi : σ i = 0) (j : Nat) :
    renameWire σ j = 0 ↔ j = i.val := by
  unfold renameWire
  split_ifs with h
  · constructor
    · intro he
      have eq : σ ⟨j,h⟩ = σ i := (Fin.ext he).trans hi.symm
      exact congrArg Fin.val (σ.injective eq)
    · intro he
      have eq : (⟨j,h⟩ : Fin 10) = i := Fin.ext he
      simp [eq,hi]
  · constructor
    · omega
    · intro he
      have := i.isLt
      omega

lemma renamed_ten (σ : Equiv.Perm (Fin 10)) (j : Nat) :
    renameWire σ j = 10 ↔ j = 10 := by
  unfold renameWire
  split_ifs with h
  · have := (σ ⟨j,h⟩).isLt
    omega
  · rfl

lemma renamed_contains_zero (σ : Equiv.Perm (Fin 10)) (i : Fin 10)
    (hi : σ i = 0) (xs : List Nat) :
    (xs.map (renameWire σ)).contains 0 = xs.contains i.val := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨j,hj,he⟩
    exact (renamed_zero σ i hi j).mp he ▸ hj
  · intro hm
    exact ⟨i.val,hm,(renamed_zero σ i hi i.val).mpr rfl⟩

lemma renamed_contains_ten (σ : Equiv.Perm (Fin 10)) (xs : List Nat) :
    (xs.map (renameWire σ)).contains 10 = xs.contains 10 := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨j,hj,he⟩
    exact (renamed_ten σ j).mp he ▸ hj
  · intro hm
    exact ⟨10,hm,(renamed_ten σ 10).mpr rfl⟩

lemma renamed_reader (σ : Equiv.Perm (Fin 10)) (i : Fin 10)
    (hi : σ i = 0) (g : Gate) : r0 (renameGate σ g) = readsLiteral i g := by
  rcases g with ⟨op, xs⟩
  cases op <;> simp only [r0,renameGate,readsLiteral,← List.map_take,
    renamed_contains_zero σ i hi,renamed_contains_ten]


lemma readers_le_two_any (h15 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 p9 15)
    (i : Fin 10) (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 18)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x i]) = p10 x) :
    C.gates.countP (readsLiteral i) ≤ 2 := by
  let j : Fin 10 := if i = 0 then 1 else 0
  have hij : i ≠ j := by
    dsimp [j]
    split_ifs with h
    · subst i
      decide
    · exact h
  obtain ⟨σ, hi, _, invariant⟩ := canonical_pair i j hij
  have invariant' : ∀ x : Fin 10 → Bool, p10 (fun v => x (σ v)) = p10 x := by
    intro x
    simpa [p10, Automorphisms.value,Automorphisms.edges,List.any_cons,List.any_nil,
      Bool.or_false,Bool.or_assoc] using invariant x
  have hs' : (renameCircuit σ C).size ≤ 18 := by
    rw [renameCircuit_size]
    exact hs
  have hc' : ∀ x : Fin 10 → Bool,
      (renameCircuit σ C).eval (List.ofFn x ++ [!x 0]) = p10 x := by
    intro x
    rw [renameCircuit_eval]
    have h := hc (fun v => x (σ v))
    simpa only [hi,invariant' x] using h
  have hb := readers_le_two h15 (renameCircuit σ C)
    (renameCircuit_fanInTwo σ C hf) hs' hc'
  simpa only [renameCircuit,List.countP_map,Function.comp_def,renamed_reader σ i hi] using hb

lemma first_not_eval_any (i : Fin 10) (gs : List Gate) (output : Nat) (x : Fin 10 → Bool) :
    (Circuit.mk (⟨.not,[i.val]⟩ :: gs) output).eval (List.ofFn x) =
      (Circuit.mk gs output).eval (List.ofFn x ++ [!x i]) := by
  simp only [Circuit.eval,Circuit.wires,List.foldl_cons,GateOp.eval,List.map_cons,List.map_nil,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

lemma first_not_readers_le_two_any
    (h15 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 p9 15)
    (i : Fin 10) (gs : List Gate) (output : Nat)
    (hf : FanInTwo (Circuit.mk (⟨.not,[i.val]⟩ :: gs) output))
    (hs : (Circuit.mk (⟨.not,[i.val]⟩ :: gs) output).size ≤ 19)
    (hc : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨.not,[i.val]⟩ :: gs) output).eval (List.ofFn x) = p10 x) :
    gs.countP (readsLiteral i) ≤ 2 := by
  apply readers_le_two_any h15 i (Circuit.mk gs output)
  · intro g hg
    exact hf g (List.mem_cons_of_mem _ hg)
  · change gs.length ≤ 18
    change gs.length + 1 ≤ 19 at hs
    omega
  · intro x
    rw [← first_not_eval_any]
    exact hc x

end PEqualNP.Outside.L_meta_2592.ReaderDeletion
