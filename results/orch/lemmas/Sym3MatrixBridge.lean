import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace PEqualNP.Outside.L_gct_231.Sym3Matrix

def wittQ (u : Fin 5 → ℂ) : ℂ := 2*u 0*u 2+2*u 1*u 3+18*(u 4)^2
def minor (u v : Fin 5 → ℂ) (i j : Fin 5) : ℂ := u i*v j-u j*v i
def cubic (u : Fin 5 → ℂ) : ℂ := (((-27648) * ((u 4) ^ 3)) + ((-26) * ((u 2) ^ 3)) + (26 * ((u 3) ^ 3)) + ((-13824) * (u 4) * ((u 0) ^ 2)) + ((-13824) * (u 4) * ((u 1) ^ 2)) + ((-4608) * (u 1) * ((u 0) ^ 2)) + ((-1152) * (u 3) * ((u 0) ^ 2)) + ((-576) * (u 2) * ((u 0) ^ 2)) + ((-120) * (u 0) * ((u 2) ^ 2)) + ((-39) * (u 3) * ((u 2) ^ 2)) + (39 * (u 2) * ((u 3) ^ 2)) + (120 * (u 1) * ((u 3) ^ 2)) + (504 * (u 4) * ((u 2) ^ 2)) + (504 * (u 4) * ((u 3) ^ 2)) + (576 * (u 3) * ((u 1) ^ 2)) + (1152 * (u 2) * ((u 1) ^ 2)) + (4608 * (u 0) * ((u 1) ^ 2)) + ((-1152) * (u 0) * (u 1) * (u 2)) + ((-240) * (u 0) * (u 2) * (u 3)) + (240 * (u 1) * (u 2) * (u 3)) + (504 * (u 2) * (u 3) * (u 4)) + (576 * (u 0) * (u 2) * (u 4)) + (576 * (u 1) * (u 3) * (u 4)) + (1152 * (u 0) * (u 1) * (u 3)) + (13824 * (u 0) * (u 1) * (u 4)))

lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    (M 0 0 * M 1 1 + M 0 1 * M 1 0) * (M 2 2 * M 3 3 + M 2 3 * M 3 2) + (M 0 0 * M 1 2 + M 0 2 * M 1 0) * (M 2 1 * M 3 3 + M 2 3 * M 3 1) + (M 0 0 * M 1 3 + M 0 3 * M 1 0) * (M 2 1 * M 3 2 + M 2 2 * M 3 1) + (M 0 1 * M 1 2 + M 0 2 * M 1 1) * (M 2 0 * M 3 3 + M 2 3 * M 3 0) + (M 0 1 * M 1 3 + M 0 3 * M 1 1) * (M 2 0 * M 3 2 + M 2 2 * M 3 0) + (M 0 2 * M 1 3 + M 0 3 * M 1 2) * (M 2 0 * M 3 1 + M 2 1 * M 3 0) := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring



def support (a b c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,c,d,0],![c,b,e,0],![d,e,f,0],![0,0,0,0]]

noncomputable def wittMatrix (u : Fin 5 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  support (-u 2/3-u 3/6-2*u 4) (u 2/6-u 3/6-2*u 4)
    (u 1+u 2/24+u 3/12+u 4) (u 0-u 1+u 2/24-u 3/24+u 4)
    (-u 0-u 2/12-u 3/24+u 4) (u 2/6+u 3/3-2*u 4)

noncomputable def coordinates (M : Matrix (Fin 4) (Fin 4) ℂ) : Fin 5 → ℂ :=
  ![M 0 0/4+M 0 1/2+M 0 2/2-M 1 2/2,
    M 0 0/4+M 1 1/4+M 0 1,
    -2*M 0 0+2*M 1 1,
    -2*M 0 0-4*M 1 1-4*M 0 1-4*M 0 2-4*M 1 2,
    (M 0 1+M 0 2+M 1 2)/3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma support_sum_zero (a b c d e f : ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+z*support a b c d e f r s)=24) : a+b+f+2*(c+d+e)=0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  simp [perm4,support,Matrix.of_apply] at h1 hm1 h2 hm2
  linear_combination (1/9:ℂ)*(h1-hm1)-(1/72:ℂ)*(h2-hm2)

lemma support_shape (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ i j : Fin 4, M i j=M j i) (hz : ∀ j : Fin 4, M 3 j=0) :
    M=support (M 0 0) (M 1 1) (M 0 1) (M 0 2) (M 1 2) (M 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [support,hz,hs 0 3,hs 1 3,hs 2 3,hs 1 0,hs 2 0,hs 2 1]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma support_decode (a b c d e f : ℂ) (hS : a+b+f+2*(c+d+e)=0) :
    wittMatrix (coordinates (support a b c d e f))=support a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wittMatrix,coordinates,support] <;> try ring
  linear_combination -hS

lemma matrix_decode (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ i j : Fin 4, M i j=M j i) (hz : ∀ j : Fin 4, M 3 j=0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) => (1:ℂ)+z*M r s)=24) :
    wittMatrix (coordinates M)=M := by
  have hshape := support_shape M hs hz
  rw [hshape] at hp ⊢
  exact support_decode _ _ _ _ _ _ (support_sum_zero _ _ _ _ _ _ hp)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma witt_permanent (u : Fin 5 → ℂ) (z : ℂ) :
    Matrix.permanent (Matrix.of fun (r s : Fin 4) => (1:ℂ)+z*wittMatrix u r s)=
      24+z^2*wittQ u+(z^3/2304)*cubic u := by
  simp [perm4,wittMatrix,support,Matrix.of_apply,wittQ,cubic]
  ring

lemma witt_linear (u v : Fin 5 → ℂ) (a b : ℂ) :
    wittMatrix (fun r => a*u r+b*v r)=
      Matrix.of (fun (r s : Fin 4) => a*wittMatrix u r s+b*wittMatrix v r s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wittMatrix,support,Matrix.of_apply] <;> ring

lemma coordinates_proportional (u v : Fin 5 → ℂ) (hu : u≠0)
    (hm : ∀ i j : Fin 5, minor u v i j=0) : ∃ c : ℂ, v=fun r => c*u r := by
  have hi : ∃ i : Fin 5, u i≠0 := by
    by_contra hn
    apply hu
    funext i
    exact Classical.not_not.mp ((not_exists.mp hn) i)
  obtain ⟨i,hi⟩ := hi
  refine ⟨v i/u i,?_⟩
  funext j
  have he := hm i j
  dsimp [minor] at he
  field_simp [hi]
  linear_combination he

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma zero_row_pair_dependent
    (hcoordinate : ∀ u v : Fin 5 → ℂ,
      (∀ a b : ℂ, wittQ (fun r => a*u r+b*v r)=0) →
      (∀ a b : ℂ, cubic (fun r => a*u r+b*v r)=0) →
      ∀ i j : Fin 5, minor u v i j=0)
    (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ i j : Fin 4, A i j=A j i) (hsB : ∀ i j : Fin 4, B i j=B j i)
    (hzA : ∀ j : Fin 4, A 3 j=0) (hzB : ∀ j : Fin 4, B 3 j=0) (hA : A≠0)
    (hp : ∀ a b : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+a*A r s+b*B r s)=24) :
    ∃ c : ℂ, B=Matrix.of fun (r s : Fin 4) => c*A r s := by
  have hAp (z : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) => (1:ℂ)+z*A r s)=24 := by
    simpa using hp z 0
  have hBp (z : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) => (1:ℂ)+z*B r s)=24 := by
    simpa using hp 0 z
  have hDA := matrix_decode A hsA hzA hAp
  have hDB := matrix_decode B hsB hzB hBp
  let u := coordinates A
  let v := coordinates B
  have hper (a b z : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+z*wittMatrix (fun i => a*u i+b*v i) r s)=24 := by
    have he := hp (z*a) (z*b)
    rw [witt_linear]
    simp only [Matrix.of_apply]
    change Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1:ℂ)+z*(a*wittMatrix (coordinates A) r s+b*wittMatrix (coordinates B) r s))=24
    rw [hDA,hDB]
    convert he using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply]
    ring
  have hQC (a b : ℂ) : wittQ (fun i => a*u i+b*v i)=0 ∧ cubic (fun i => a*u i+b*v i)=0 := by
    have h1 := hper a b 1
    have hm1 := hper a b (-1)
    rw [witt_permanent] at h1 hm1
    constructor
    · linear_combination (1/2:ℂ)*(h1+hm1)
    · linear_combination (1152:ℂ)*(h1-hm1)
  have hu : u≠0 := by
    intro hu
    apply hA
    rw [← hDA]
    change wittMatrix u=0
    rw [hu]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wittMatrix,support]
  obtain ⟨c,hc⟩ := coordinates_proportional u v hu (hcoordinate u v (fun a b => (hQC a b).1) (fun a b => (hQC a b).2))
  refine ⟨c,?_⟩
  rw [← hDB,← hDA]
  change wittMatrix v=Matrix.of fun (r s : Fin 4) => c*wittMatrix u r s
  rw [hc]
  have he := witt_linear u u c 0
  simpa using he

end PEqualNP.Outside.L_gct_231.Sym3Matrix
