import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

def occurs {n : Nat} : DMFormula n → Fin n → Nat
  | .lit j _, i => if j = i then 1 else 0
  | .and a b, i => occurs a i + occurs b i
  | .or a b, i => occurs a i + occurs b i

def literalTable (i : Fin 3) (b : Bool) : Nat :=
  let p := if i.val = 0 then 170 else if i.val = 1 then 204 else 240
  if b then p else Nat.xor 255 p

def pruningTables : DMFormula 3 → List Nat
  | .lit i b => [0, 255, literalTable i b]
  | .and a b => ([0, 255] ++ (pruningTables a).flatMap
      (fun x => (pruningTables b).map (Nat.land x))).eraseDups
  | .or a b => ([0, 255] ++ (pruningTables a).flatMap
      (fun x => (pruningTables b).map (Nat.lor x))).eraseDups

end PEqualNP.Outside.L_meta_2592.FormulaPruning

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

def joinProjection (isOr : Bool) : Option (DMFormula 3) → Option (DMFormula 3) →
    Option (DMFormula 3)
  | none, b => b
  | a, none => a
  | some a, some b => some (if isOr then .or a b else .and a b)

def project {n : Nat} (ρ : Fin n → Option (Fin 3)) : DMFormula n → Option (DMFormula 3)
  | .lit i b => (ρ i).map (fun j => .lit j b)
  | .and a b => joinProjection false (project ρ a) (project ρ b)
  | .or a b => joinProjection true (project ρ a) (project ρ b)

def tablesOpt : Option (DMFormula 3) → List Nat
  | none => [0,255]
  | some a => pruningTables a

def occursOpt (a : Option (DMFormula 3)) (i : Fin 3) : Nat :=
  match a with
  | none => 0
  | some φ => occurs φ i

def leavesOpt : Option (DMFormula 3) → Nat
  | none => 0
  | some φ => φ.leaves

def cofactorInput {n : Nat} (ρ : Fin n → Option (Fin 3)) (base : Fin n → Bool)
    (r : Fin 8) (i : Fin n) : Bool :=
  match ρ i with
  | none => base i
  | some j => r.val.testBit j.val

def realizes (a : Option (DMFormula 3)) (f : Fin 8 → Bool) : Prop :=
  ∃ t ∈ tablesOpt a, ∀ r, f r = t.testBit r.val

end PEqualNP.Outside.L_meta_2592.FormulaPruning

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

lemma true_table_bit (r : Fin 8) : (255 : Nat).testBit r.val = true := by
  fin_cases r <;> decide

lemma literal_table_bit : ∀ (i : Fin 3) (b : Bool) (r : Fin 8),
    (literalTable i b).testBit r.val =
      if b then r.val.testBit i.val else !r.val.testBit i.val := by
  decide +kernel

lemma constants_mem (a : Option (DMFormula 3)) :
    0 ∈ tablesOpt a ∧ 255 ∈ tablesOpt a := by
  cases a with
  | none => simp [tablesOpt]
  | some a => cases a <;> simp [tablesOpt, pruningTables]

lemma constant_realizes (a : Option (DMFormula 3)) (b : Bool) :
    realizes a (fun _ => b) := by
  cases b with
  | false => exact ⟨0, (constants_mem a).1, by intro r; simp⟩
  | true => exact ⟨255, (constants_mem a).2, fun r => (true_table_bit r).symm⟩

lemma realizes_join (a b : Option (DMFormula 3)) (f g : Fin 8 → Bool) (isOr : Bool)
    (hf : realizes a f) (hg : realizes b g) :
    realizes (joinProjection isOr a b) (fun r => if isOr then f r || g r else f r && g r) := by
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨v, hv, hgv⟩ := hg
  cases a with
  | none =>
    have hu' : u = 0 ∨ u = 255 := by simpa [tablesOpt] using hu
    rcases hu' with rfl | rfl
    · cases isOr with
      | false =>
        refine ⟨0, (constants_mem _).1, ?_⟩
        intro r
        simp [hfu r]
      | true =>
        refine ⟨v, ?_, ?_⟩
        · simpa [joinProjection] using hv
        · intro r; simp [hfu r, hgv r]
    · cases isOr with
      | false =>
        refine ⟨v, ?_, ?_⟩
        · simpa [joinProjection] using hv
        · intro r; simp [hfu r, hgv r, true_table_bit]
      | true =>
        refine ⟨255, (constants_mem _).2, ?_⟩
        intro r
        simp [hfu r, true_table_bit]
  | some a =>
    cases b with
    | none =>
      have hv' : v = 0 ∨ v = 255 := by simpa [tablesOpt] using hv
      rcases hv' with rfl | rfl
      · cases isOr with
        | false =>
          refine ⟨0, (constants_mem _).1, ?_⟩
          intro r; simp [hgv r]
        | true =>
          refine ⟨u, ?_, ?_⟩
          · simpa [joinProjection] using hu
          · intro r; simp [hfu r, hgv r]
      · cases isOr with
        | false =>
          refine ⟨u, ?_, ?_⟩
          · simpa [joinProjection] using hu
          · intro r; simp [hfu r, hgv r, true_table_bit]
        | true =>
          refine ⟨255, (constants_mem _).2, ?_⟩
          intro r; simp [hgv r, true_table_bit]
    | some b =>
      cases isOr with
      | false =>
        refine ⟨Nat.land u v, ?_, ?_⟩
        · simp only [joinProjection, Bool.false_eq_true, ite_false, tablesOpt, pruningTables,
            List.mem_eraseDups, List.mem_append]
          right
          exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨v, hv, rfl⟩⟩
        · intro r
          simp [hfu r, hgv r, Nat.testBit_land]
      | true =>
        refine ⟨Nat.lor u v, ?_, ?_⟩
        · simp only [joinProjection, ite_true, tablesOpt, pruningTables,
            List.mem_eraseDups, List.mem_append]
          right
          exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨v, hv, rfl⟩⟩
        · intro r
          simp [hfu r, hgv r, Nat.testBit_lor]

lemma project_realizes {n : Nat} (ρ : Fin n → Option (Fin 3)) (base : Fin n → Bool)
    (φ : DMFormula n) :
    realizes (project ρ φ) (fun r => φ.eval (cofactorInput ρ base r)) := by
  induction φ with
  | lit i b =>
    cases hi : ρ i with
    | none =>
      simpa [project, hi, DMFormula.eval, cofactorInput] using
        constant_realizes none (if b then base i else !base i)
    | some j =>
      refine ⟨literalTable j b, ?_, ?_⟩
      · simp [project, hi, tablesOpt, pruningTables]
      · intro r
        simpa [DMFormula.eval, cofactorInput, hi] using (literal_table_bit j b r).symm
  | and a b ha hb =>
    simpa [project, DMFormula.eval] using realizes_join (project ρ a) (project ρ b)
      (fun r => a.eval (cofactorInput ρ base r))
      (fun r => b.eval (cofactorInput ρ base r)) false ha hb
  | or a b ha hb =>
    simpa [project, DMFormula.eval] using realizes_join (project ρ a) (project ρ b)
      (fun r => a.eval (cofactorInput ρ base r))
      (fun r => b.eval (cofactorInput ρ base r)) true ha hb

end PEqualNP.Outside.L_meta_2592.FormulaPruning
