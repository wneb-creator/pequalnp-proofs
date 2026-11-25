import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Restriction

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def probe (u v w : Fin 10) (a b : Bool) : Fin 10 → Bool :=
  fun i => if i = u then a else if i = v then b else decide (i = w)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma left_probe : ∀ u v : Fin 10, u ≠ v →
    ∃ w : Fin 10, ∀ a b : Bool, petersen (probe u v w a b) = a := by
  decide +kernel

lemma right_probe (u v : Fin 10) (hne : u ≠ v) :
    ∃ w : Fin 10, ∀ a b : Bool, petersen (probe u v w a b) = b := by
  obtain ⟨w, hw⟩ := left_probe v u hne.symm
  refine ⟨w, fun a b => ?_⟩
  have eq : probe u v w a b = probe v u w b a := by
    funext i
    simp only [probe]
    by_cases hu : i = u
    · subst i
      simp [hne]
    · by_cases hv : i = v
      · subst i
        simp [hne.symm]
      · simp [hu, hv]
  rw [eq, hw]

lemma no_pair_code (u v : Fin 10) (hne : u ≠ v)
    (code : Bool → Bool → Bool) :
    ∃ a b : Fin 10 → Bool,
      (∀ i, i ≠ u → i ≠ v → a i = b i) ∧
      code (a u) (a v) = code (b u) (b v) ∧ petersen a ≠ petersen b := by
  by_contra! hf
  have depends (w : Fin 10) (a b c d : Bool)
      (same : code a b = code c d) :
      petersen (probe u v w a b) = petersen (probe u v w c d) := by
    apply hf (probe u v w a b) (probe u v w c d)
    · intro i hi hj
      simp [probe, hi, hj]
    · simpa [probe, hne.symm] using same
  obtain ⟨p, hp⟩ := left_probe u v hne
  obtain ⟨q, hq⟩ := right_probe u v hne
  have h01 : code false false ≠ code true false := by
    intro same
    have impossible := depends p false false true false same
    rw [hp, hp] at impossible
    cases impossible
  have h02 : code false false ≠ code false true := by
    intro same
    have impossible := depends q false false false true same
    rw [hq, hq] at impossible
    cases impossible
  have h12 : code true false ≠ code false true := by
    intro same
    have impossible := depends p true false false true same
    rw [hp, hp] at impossible
    cases impossible
  have pigeonhole : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False := by decide
  exact pigeonhole _ _ _ h01 h02 h12


def perm (v : Fin 10) : Fin 10 → Fin 10 :=
  ![![2,3,8,6,1,7,4,5,9,0],
    ![3,4,9,7,2,8,0,6,5,1],
    ![0,4,9,6,1,5,3,7,8,2],
    ![0,1,6,9,4,5,2,8,7,3],
    ![1,2,7,5,0,6,3,9,8,4],
    ![1,2,3,4,0,6,7,8,9,5],
    ![0,4,3,2,1,5,9,8,7,6],
    ![0,1,6,8,5,4,2,9,3,7],
    ![0,1,2,7,5,4,6,3,9,8],
    ![0,1,2,3,4,5,6,7,8,9]] v

def permInv (v : Fin 10) : Fin 10 → Fin 10 :=
  ![![9,4,0,1,6,7,3,5,2,8],
    ![6,9,4,0,1,8,7,3,5,2],
    ![0,4,9,6,1,5,3,7,8,2],
    ![0,1,6,9,4,5,2,8,7,3],
    ![4,0,1,6,9,3,5,2,8,7],
    ![4,0,1,2,3,9,5,6,7,8],
    ![0,4,3,2,1,5,9,8,7,6],
    ![0,1,6,8,5,4,2,9,3,7],
    ![0,1,2,7,5,4,6,3,9,8],
    ![0,1,2,3,4,5,6,7,8,9]] v

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma perm_inverse : ∀ v i : Fin 10, permInv v (perm v i) = i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma perm_right_inverse : ∀ v i : Fin 10, perm v (permInv v i) = i := by
  decide +kernel

lemma perm_last : ∀ v : Fin 10, perm v 9 = v := by decide

lemma perm_preserves (v : Fin 10) (x : Fin 10 → Bool) :
    petersen (x ∘ perm v) = petersen x := by
  fin_cases v <;> simp [perm, petersen] <;> ac_rfl

def liftInput (v : Fin 10) (x : Fin 9 → Bool) : Fin 10 → Bool :=
  fun i => Fin.lastCases false x (permInv v i)

lemma liftInput_removed (v : Fin 10) (x : Fin 9 → Bool) : liftInput v x v = false := by
  have eq : permInv v v = 9 := by
    have h := perm_inverse v 9
    rwa [perm_last] at h
  change Fin.lastCases false x (permInv v v) = false
  rw [eq]
  rfl

lemma liftInput_petersen (v : Fin 10) (x : Fin 9 → Bool) :
    petersen (liftInput v x) = petersen (Fin.lastCases false x) := by
  have eq : liftInput v x ∘ perm v = Fin.lastCases false x := by
    funext i
    simp [liftInput, perm_inverse]
  rw [← perm_preserves v (liftInput v x), eq]

end PEqualNP.Outside.L_meta_2592_aux.Restriction
