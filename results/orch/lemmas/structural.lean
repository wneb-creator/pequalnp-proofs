import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Subgraphs

def adjacent (a b : Fin 10) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any fun e =>
    decide ((a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1))

def pairMap : Fin 10 → Fin 10 → Fin 10 → Fin 10 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
      ![0, 4, 9, 7, 5, 1, 3, 6, 2, 8],
      ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
      ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
      ![0, 5, 7, 9, 4, 1, 8, 2, 6, 3],
      ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
      ![0, 4, 9, 7, 5, 1, 3, 6, 2, 8]],
    ![![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
      ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
      ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
      ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
      ![1, 0, 4, 9, 6, 2, 5, 3, 7, 8],
      ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
      ![1, 6, 9, 7, 2, 0, 8, 4, 5, 3],
      ![1, 2, 7, 9, 6, 0, 3, 5, 4, 8],
      ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7],
      ![1, 6, 9, 7, 2, 0, 8, 4, 5, 3]],
    ![![2, 1, 0, 5, 7, 3, 6, 4, 8, 9],
      ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9],
      ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
      ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
      ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![2, 7, 5, 0, 1, 3, 9, 8, 4, 6],
      ![2, 1, 6, 9, 7, 3, 0, 8, 4, 5],
      ![2, 7, 9, 6, 1, 3, 5, 4, 8, 0],
      ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
      ![2, 7, 9, 6, 1, 3, 5, 4, 8, 0]],
    ![![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![3, 2, 7, 9, 4, 8, 1, 5, 6, 0],
      ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0],
      ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0],
      ![3, 2, 7, 9, 4, 8, 1, 5, 6, 0],
      ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0],
      ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1]],
    ![![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 3, 2, 7, 9, 0, 8, 1, 5, 6],
      ![4, 3, 8, 6, 9, 0, 2, 5, 1, 7],
      ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![4, 0, 5, 8, 3, 9, 1, 7, 6, 2],
      ![4, 9, 6, 8, 3, 0, 7, 1, 5, 2],
      ![4, 9, 7, 2, 3, 0, 6, 5, 1, 8],
      ![4, 3, 8, 6, 9, 0, 2, 5, 1, 7],
      ![4, 9, 7, 2, 3, 0, 6, 5, 1, 8]],
    ![![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 7, 2, 3, 8, 0, 9, 1, 4, 6],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 0, 4, 9, 7, 8, 1, 3, 6, 2],
      ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
      ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3]],
    ![![6, 1, 0, 5, 8, 9, 2, 4, 7, 3],
      ![6, 1, 0, 5, 8, 9, 2, 4, 7, 3],
      ![6, 1, 2, 3, 8, 9, 0, 7, 4, 5],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2],
      ![6, 8, 5, 0, 1, 9, 3, 7, 4, 2],
      ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0],
      ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0],
      ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0],
      ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0]],
    ![![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
      ![7, 2, 1, 0, 5, 9, 3, 6, 4, 8],
      ![7, 2, 3, 8, 5, 9, 1, 4, 6, 0],
      ![7, 2, 3, 8, 5, 9, 1, 4, 6, 0],
      ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8],
      ![7, 5, 0, 1, 2, 9, 8, 4, 6, 3],
      ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
      ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
      ![7, 5, 8, 3, 2, 9, 0, 6, 4, 1],
      ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0]],
    ![![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
      ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7],
      ![8, 3, 2, 7, 5, 6, 4, 1, 9, 0],
      ![8, 3, 2, 7, 5, 6, 4, 1, 9, 0],
      ![8, 3, 4, 0, 5, 6, 2, 9, 1, 7],
      ![8, 5, 0, 1, 6, 3, 7, 4, 2, 9],
      ![8, 6, 9, 7, 5, 3, 1, 4, 2, 0],
      ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
      ![8, 3, 2, 7, 5, 6, 4, 1, 9, 0],
      ![8, 6, 9, 7, 5, 3, 1, 4, 2, 0]],
    ![![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0],
      ![9, 4, 3, 8, 6, 7, 0, 2, 5, 1],
      ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
      ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
      ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0],
      ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
      ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0]]]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairMap_injective : ∀ a b : Fin 10, Function.Injective (pairMap a b) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairMap_adjacent : ∀ a b u v : Fin 10,
    adjacent (pairMap a b u) (pairMap a b v) = adjacent u v := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairMap_zero : ∀ a b : Fin 10, pairMap a b 0 = a := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pairMap_second : ∀ a b : Fin 10, a ≠ b →
    pairMap a b (if adjacent a b then 1 else 2) = b := by
  decide +kernel

noncomputable def pairPerm (a b : Fin 10) : Equiv.Perm (Fin 10) :=
  Equiv.ofBijective (pairMap a b)
    (Finite.injective_iff_bijective.mp (pairMap_injective a b))

lemma normalize_pair (a b : Fin 10) (h : a ≠ b) :
    ∃ p : Equiv.Perm (Fin 10), p 0 = a ∧
      p (if adjacent a b then 1 else 2) = b ∧
      ∀ u v : Fin 10, adjacent (p u) (p v) = adjacent u v := by
  exact ⟨pairPerm a b, pairMap_zero a b, pairMap_second a b h, pairMap_adjacent a b⟩

def edgeFun (x : Fin 10 → Bool) : Bool :=
  decide (∃ a b : Fin 10, adjacent a b = true ∧ x a = true ∧ x b = true)

lemma edgeFun_permute (p : Equiv.Perm (Fin 10))
    (hp : ∀ a b, adjacent (p a) (p b) = adjacent a b) (x : Fin 10 → Bool) :
    edgeFun (x ∘ p) = edgeFun x := by
  unfold edgeFun
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨p a, p b, (hp a b).trans hab, ha, hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    refine ⟨p.symm a, p.symm b, ?_, ?_, ?_⟩
    · calc
        adjacent (p.symm a) (p.symm b) = adjacent a b := by
          simpa only [Equiv.apply_symm_apply] using (hp (p.symm a) (p.symm b)).symm
        _ = true := hab
    · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using ha
    · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hb

def falseNeighbor : Fin 10 → Fin 10 → Fin 10 :=
  ![![1, 2, 1, 2, 3, 7, 1, 2, 3, 4],
    ![4, 0, 3, 2, 0, 0, 8, 2, 3, 4],
    ![1, 0, 1, 4, 0, 0, 1, 5, 3, 4],
    ![1, 0, 1, 2, 0, 0, 1, 2, 5, 4],
    ![1, 0, 1, 2, 0, 0, 1, 2, 3, 6],
    ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4],
    ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4],
    ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4],
    ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4],
    ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4]]

def trueNeighbor : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 0, 3, 2, 0, 0, 8, 2, 3, 6],
    ![1, 0, 1, 4, 3, 7, 1, 5, 3, 4],
    ![4, 2, 0, 2, 0, 0, 8, 2, 5, 4],
    ![1, 0, 3, 0, 3, 0, 1, 5, 3, 6],
    ![4, 2, 1, 4, 0, 7, 1, 2, 5, 4],
    ![5, 2, 1, 2, 3, 0, 1, 5, 5, 4],
    ![4, 6, 3, 2, 0, 0, 0, 2, 6, 6],
    ![1, 0, 7, 4, 0, 7, 1, 0, 3, 7],
    ![1, 0, 1, 8, 0, 8, 8, 2, 0, 4],
    ![1, 0, 1, 2, 9, 0, 9, 9, 3, 0]]

def lowerInput (a b : Fin 10) (fixed : Bool) (j : Fin 10) : Bool :=
  decide (j = (if fixed then trueNeighbor a b else falseNeighbor a b)) ||
    (decide (j = a) && fixed)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma lowerInput_fixed : ∀ a b : Fin 10, a ≠ b → ∀ fixed : Bool,
    lowerInput a b fixed a = fixed ∧ lowerInput a b fixed b = false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma lowerInput_rejects : ∀ a b : Fin 10, a ≠ b → ∀ fixed : Bool,
    edgeFun (lowerInput a b fixed) = false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma lowerInput_accepts : ∀ a b : Fin 10, a ≠ b → ∀ fixed : Bool,
    edgeFun (Function.update (lowerInput a b fixed) b true) = true := by
  decide +kernel

lemma remains_essential (a b : Fin 10) (hab : a ≠ b) (fixed : Bool) :
    ∃ x y : Fin 10 → Bool, x a = fixed ∧ y a = fixed ∧
      (∀ j, j ≠ b → x j = y j) ∧ edgeFun x ≠ edgeFun y := by
  refine ⟨lowerInput a b fixed, Function.update (lowerInput a b fixed) b true,
    (lowerInput_fixed a b hab fixed).1, ?_, ?_, ?_⟩
  · simpa only [Function.update_of_ne hab] using (lowerInput_fixed a b hab fixed).1
  · intro j hj
    simp only [Function.update_of_ne hj]
  · rw [lowerInput_rejects a b hab fixed, lowerInput_accepts a b hab fixed]
    decide

end PEqualNP.Outside.L_meta_2592_aux.Subgraphs
