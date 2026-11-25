import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

def ca (x y : ℂ) : ℂ := x + y
def cm (x y : ℂ) : ℂ := x * y
def cp (x : ℂ) (n : ℕ) : ℂ := x ^ n
def cz (z : ℤ) : ℂ := z

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

def model (a b c d e f g k i j rr x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![ca (cm (cz (1)) (cm (a) (y))) (cm (cz (1)) (cm (b) (z))), ca (cm (cz (1)) (cm (c) (y))) (cm (cz (1)) (cm (d) (z))), cm (cz (1)) (cm (e) (z)), cm (cz (1)) (cm (f) (y))], ![ca (cm (cz (1)) (cm (c) (y))) (cm (cz (1)) (cm (d) (z))), ca (cm (cz (1)) (cm (g) (y))) (cm (cz (1)) (cm (k) (z))), cm (cz (1)) (cm (i) (z)), cm (cz (1)) (cm (j) (y))], ![cm (cz (1)) (cm (e) (z)), cm (cz (1)) (cm (i) (z)), ca (ca (cm (cz (-1)) (cm (b) (z))) (ca (cm (cz (-2)) (cm (d) (z))) (cm (cz (-2)) (cm (e) (z))))) (ca (ca (cm (cz (-1)) (cm (k) (z))) (cm (cz (-2)) (cm (i) (z)))) (ca (cm (cz (1)) (cm (rr) (x))) (cm (cz (-1)) (x)))), cm (cz (1)) (x)], ![cm (cz (1)) (cm (f) (y)), cm (cz (1)) (cm (j) (y)), cm (cz (1)) (x), ca (ca (cm (cz (-1)) (cm (a) (y))) (ca (cm (cz (-2)) (cm (c) (y))) (cm (cz (-2)) (cm (f) (y))))) (ca (ca (cm (cz (-1)) (cm (g) (y))) (cm (cz (-2)) (cm (j) (y)))) (ca (cm (cz (-1)) (cm (rr) (x))) (cm (cz (-1)) (x))))]]

def coefficients (a b c d e f g k i j rr : ℂ) : Fin 19 → ℂ :=
  ![ca (ca (ca (ca (cm (cm (cz (-1)) (cp a 2)) (cm (g) (rr))) (ca (cm (cz (1)) (cm (cp a 2) (g))) (cm (cm (cz (-1)) (a)) (cm (cp c 2) (rr))))) (ca (cm (cz (1)) (cm (a) (cp c 2))) (ca (cm (cm (cz (-2)) (a)) (cm (c) (cm (g) (rr)))) (cm (cm (cz (2)) (a)) (cm (c) (g)))))) (ca (ca (cm (cm (cz (-2)) (a)) (cm (f) (cm (g) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (f) (g))) (cm (cm (cz (-1)) (a)) (cm (cp g 2) (rr))))) (ca (ca (cm (cz (1)) (cm (a) (cp g 2))) (cm (cm (cz (-2)) (a)) (cm (g) (cm (j) (rr))))) (ca (cm (cm (cz (2)) (a)) (cm (g) (j))) (cm (cm (cz (1)) (a)) (cm (cp j 2) (rr))))))) (ca (ca (ca (cm (cz (-1)) (cm (a) (cp j 2))) (ca (cm (cz (-2)) (cm (cp c 3) (rr))) (cm (cz (2)) (cp c 3)))) (ca (cm (cm (cz (-2)) (cp c 2)) (cm (f) (rr))) (ca (cm (cz (2)) (cm (cp c 2) (f))) (cm (cm (cz (-1)) (cp c 2)) (cm (g) (rr)))))) (ca (ca (cm (cz (1)) (cm (cp c 2) (g))) (ca (cm (cm (cz (-2)) (cp c 2)) (cm (j) (rr))) (cm (cz (2)) (cm (cp c 2) (j))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (f) (cm (j) (rr)))) (cm (cm (cz (-2)) (c)) (cm (f) (j)))) (ca (cm (cm (cz (1)) (cp f 2)) (cm (g) (rr))) (cm (cz (-1)) (cm (cp f 2) (g))))))),
    ca (ca (ca (ca (ca (cm (cm (cz (-1)) (cp a 2)) (cm (k) (rr))) (ca (cm (cz (1)) (cm (cp a 2) (k))) (cm (cm (cz (2)) (a)) (cm (b) (g))))) (ca (cm (cm (cz (-2)) (a)) (cm (c) (cm (d) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (c) (d))) (cm (cm (cz (-2)) (a)) (cm (c) (cm (k) (rr))))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (c) (k))) (ca (cm (cm (cz (2)) (a)) (cm (d) (cm (g) (rr)))) (cm (cm (cz (2)) (a)) (cm (d) (g))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (e) (cm (g) (rr)))) (cm (cm (cz (2)) (a)) (cm (e) (g)))) (ca (cm (cm (cz (-2)) (a)) (cm (f) (cm (k) (rr)))) (cm (cm (cz (2)) (a)) (cm (f) (k))))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (g) (k))) (ca (cm (cm (cz (2)) (a)) (cm (g) (cm (i) (rr)))) (cm (cm (cz (2)) (a)) (cm (g) (i))))) (ca (cm (cm (cz (-2)) (a)) (cm (k) (cm (j) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (k) (j))) (cm (cm (cz (2)) (a)) (cm (i) (j)))))) (ca (ca (cm (cm (cz (1)) (b)) (cm (cp c 2) (rr))) (ca (cm (cz (1)) (cm (b) (cp c 2))) (cm (cm (cz (-2)) (b)) (cm (c) (cm (g) (rr)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (c) (g))) (cm (cm (cz (-2)) (b)) (cm (f) (cm (g) (rr))))) (ca (cm (cm (cz (2)) (b)) (cm (f) (g))) (cm (cm (cz (-1)) (b)) (cm (cp g 2) (rr)))))))) (ca (ca (ca (ca (cm (cz (1)) (cm (b) (cp g 2))) (ca (cm (cm (cz (-2)) (b)) (cm (g) (cm (j) (rr)))) (cm (cm (cz (2)) (b)) (cm (g) (j))))) (ca (cm (cm (cz (1)) (b)) (cm (cp j 2) (rr))) (ca (cm (cz (-1)) (cm (b) (cp j 2))) (cm (cm (cz (-2)) (cp c 2)) (cm (d) (rr)))))) (ca (ca (cm (cz (6)) (cm (cp c 2) (d))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (e) (rr))) (cm (cz (2)) (cm (cp c 2) (e))))) (ca (ca (cm (cm (cz (1)) (cp c 2)) (cm (k) (rr))) (cm (cz (1)) (cm (cp c 2) (k)))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (i) (rr))) (cm (cz (2)) (cm (cp c 2) (i))))))) (ca (ca (ca (cm (cm (cz (-4)) (c)) (cm (d) (cm (f) (rr)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (f))) (cm (cm (cz (-2)) (c)) (cm (d) (cm (g) (rr)))))) (ca (cm (cm (cz (2)) (c)) (cm (d) (g))) (ca (cm (cm (cz (-4)) (c)) (cm (d) (cm (j) (rr)))) (cm (cm (cz (4)) (c)) (cm (d) (j)))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (e) (j))) (ca (cm (cm (cz (2)) (c)) (cm (f) (i))) (cm (cm (cz (2)) (d)) (cm (f) (cm (j) (rr)))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (f) (j))) (cm (cm (cz (2)) (e)) (cm (f) (g)))) (ca (cm (cm (cz (1)) (cp f 2)) (cm (k) (rr))) (cm (cz (-1)) (cm (cp f 2) (k)))))))),
    ca (ca (ca (ca (cm (cz (-1)) (cm (cp a 2) (rr))) (ca (cm (cz (1)) (cp a 2)) (cm (cm (cz (-4)) (a)) (cm (c) (rr))))) (ca (ca (cm (cz (4)) (cm (a) (c))) (cm (cm (cz (-2)) (a)) (cm (f) (rr)))) (ca (cm (cz (2)) (cm (a) (f))) (cm (cm (cz (-2)) (a)) (cm (g) (rr)))))) (ca (ca (cm (cz (2)) (cm (a) (g))) (ca (cm (cz (2)) (cm (a) (j))) (cm (cz (-4)) (cm (cp c 2) (rr))))) (ca (ca (cm (cz (4)) (cp c 2)) (cm (cm (cz (-2)) (c)) (cm (f) (rr)))) (ca (cm (cz (4)) (cm (c) (f))) (cm (cm (cz (-4)) (c)) (cm (g) (rr))))))) (ca (ca (ca (cm (cz (4)) (cm (c) (g))) (ca (cm (cm (cz (-2)) (c)) (cm (j) (rr))) (cm (cz (4)) (cm (c) (j))))) (ca (ca (cm (cz (1)) (cm (cp f 2) (rr))) (cm (cz (-1)) (cp f 2))) (ca (cm (cz (2)) (cm (f) (g))) (cm (cm (cz (2)) (f)) (cm (j) (rr)))))) (ca (ca (cm (cz (-2)) (cm (f) (j))) (ca (cm (cz (-1)) (cm (cp g 2) (rr))) (cm (cz (1)) (cp g 2)))) (ca (ca (cm (cm (cz (-2)) (g)) (cm (j) (rr))) (cm (cz (2)) (cm (g) (j)))) (ca (cm (cz (1)) (cm (cp j 2) (rr))) (cm (cz (-1)) (cp j 2)))))),
    ca (ca (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (b) (k))) (ca (cm (cm (cz (-1)) (a)) (cm (cp d 2) (rr))) (cm (cz (1)) (cm (a) (cp d 2))))) (ca (cm (cm (cz (2)) (a)) (cm (d) (cm (k) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (d) (k))) (cm (cm (cz (2)) (a)) (cm (e) (cm (k) (rr))))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (e) (k))) (ca (cm (cm (cz (1)) (a)) (cm (cp k 2) (rr))) (cm (cz (1)) (cm (a) (cp k 2))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (k) (cm (i) (rr)))) (cm (cm (cz (2)) (a)) (cm (k) (i)))) (ca (cm (cm (cz (-1)) (a)) (cm (cp i 2) (rr))) (cm (cz (-1)) (cm (a) (cp i 2))))))) (ca (ca (ca (cm (cm (cz (1)) (cp b 2)) (cm (g) (rr))) (ca (cm (cz (1)) (cm (cp b 2) (g))) (cm (cm (cz (2)) (b)) (cm (c) (cm (d) (rr)))))) (ca (cm (cm (cz (2)) (b)) (cm (c) (d))) (ca (cm (cm (cz (-2)) (b)) (cm (c) (cm (k) (rr)))) (cm (cm (cz (2)) (b)) (cm (c) (k)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (d) (cm (g) (rr)))) (ca (cm (cm (cz (2)) (b)) (cm (d) (g))) (cm (cm (cz (2)) (b)) (cm (e) (cm (g) (rr)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (e) (g))) (cm (cm (cz (-2)) (b)) (cm (f) (cm (k) (rr))))) (ca (cm (cm (cz (2)) (b)) (cm (f) (k))) (cm (cm (cz (2)) (b)) (cm (g) (k)))))))) (ca (ca (ca (ca (cm (cm (cz (2)) (b)) (cm (g) (cm (i) (rr)))) (ca (cm (cm (cz (2)) (b)) (cm (g) (i))) (cm (cm (cz (-2)) (b)) (cm (k) (cm (j) (rr)))))) (ca (cm (cm (cz (2)) (b)) (cm (k) (j))) (ca (cm (cm (cz (2)) (b)) (cm (i) (j))) (cm (cm (cz (2)) (c)) (cm (cp d 2) (rr)))))) (ca (ca (cm (cz (6)) (cm (c) (cp d 2))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (e) (rr)))) (cm (cm (cz (4)) (c)) (cm (d) (e))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (d) (cm (k) (rr)))) (cm (cm (cz (2)) (c)) (cm (d) (k)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (i) (rr)))) (cm (cm (cz (4)) (c)) (cm (d) (i))))))) (ca (ca (ca (cm (cm (cz (-2)) (c)) (cm (e) (cm (i) (rr)))) (ca (cm (cm (cz (-2)) (c)) (cm (e) (i))) (cm (cm (cz (-2)) (cp d 2)) (cm (f) (rr))))) (ca (cm (cz (2)) (cm (cp d 2) (f))) (ca (cm (cm (cz (-1)) (cp d 2)) (cm (g) (rr))) (cm (cz (1)) (cm (cp d 2) (g)))))) (ca (ca (cm (cm (cz (-2)) (cp d 2)) (cm (j) (rr))) (ca (cm (cz (2)) (cm (cp d 2) (j))) (cm (cm (cz (2)) (d)) (cm (e) (j))))) (ca (ca (cm (cm (cz (2)) (d)) (cm (f) (i))) (cm (cm (cz (-1)) (cp e 2)) (cm (g) (rr)))) (ca (cm (cz (-1)) (cm (cp e 2) (g))) (cm (cm (cz (2)) (e)) (cm (f) (k)))))))),
    ca (ca (ca (ca (ca (cm (cz (2)) (cm (a) (b))) (cm (cz (4)) (cm (a) (d)))) (ca (cm (cm (cz (2)) (a)) (cm (e) (rr))) (cm (cz (2)) (cm (a) (e))))) (ca (ca (cm (cz (2)) (cm (a) (k))) (cm (cz (2)) (cm (a) (i)))) (ca (cm (cz (4)) (cm (b) (c))) (cm (cm (cz (-2)) (b)) (cm (f) (rr)))))) (ca (ca (ca (cm (cz (2)) (cm (b) (f))) (cm (cz (2)) (cm (b) (g)))) (ca (cm (cz (2)) (cm (b) (j))) (cm (cz (8)) (cm (c) (d))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (e) (rr))) (cm (cz (4)) (cm (c) (e)))) (ca (cm (cz (4)) (cm (c) (k))) (cm (cm (cz (2)) (c)) (cm (i) (rr))))))) (ca (ca (ca (ca (cm (cz (4)) (cm (c) (i))) (cm (cm (cz (-2)) (d)) (cm (f) (rr)))) (ca (cm (cz (4)) (cm (d) (f))) (cm (cz (4)) (cm (d) (g))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (j) (rr))) (cm (cz (4)) (cm (d) (j)))) (ca (cm (cz (2)) (cm (e) (f))) (cm (cz (2)) (cm (e) (g)))))) (ca (ca (ca (cm (cz (2)) (cm (e) (j))) (cm (cz (2)) (cm (f) (k)))) (ca (cm (cz (2)) (cm (f) (i))) (cm (cz (2)) (cm (g) (k))))) (ca (ca (cm (cm (cz (2)) (g)) (cm (i) (rr))) (cm (cz (2)) (cm (g) (i)))) (ca (cm (cm (cz (-2)) (k)) (cm (j) (rr))) (ca (cm (cz (2)) (cm (k) (j))) (cm (cz (2)) (cm (i) (j)))))))),
    ca (ca (ca (cm (cz (-2)) (cm (a) (rr))) (cm (cz (2)) (a))) (ca (cm (cz (-4)) (cm (c) (rr))) (cm (cz (4)) (c)))) (ca (ca (cm (cz (4)) (f)) (cm (cz (-2)) (cm (g) (rr)))) (ca (cm (cz (2)) (g)) (cm (cz (4)) (j)))),
    ca (ca (ca (ca (cm (cm (cz (1)) (cp b 2)) (cm (k) (rr))) (ca (cm (cz (1)) (cm (cp b 2) (k))) (cm (cm (cz (1)) (b)) (cm (cp d 2) (rr))))) (ca (cm (cz (1)) (cm (b) (cp d 2))) (ca (cm (cm (cz (2)) (b)) (cm (d) (cm (k) (rr)))) (cm (cm (cz (2)) (b)) (cm (d) (k)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (e) (cm (k) (rr)))) (ca (cm (cm (cz (2)) (b)) (cm (e) (k))) (cm (cm (cz (1)) (b)) (cm (cp k 2) (rr))))) (ca (ca (cm (cz (1)) (cm (b) (cp k 2))) (cm (cm (cz (2)) (b)) (cm (k) (cm (i) (rr))))) (ca (cm (cm (cz (2)) (b)) (cm (k) (i))) (cm (cm (cz (-1)) (b)) (cm (cp i 2) (rr))))))) (ca (ca (ca (cm (cz (-1)) (cm (b) (cp i 2))) (ca (cm (cz (2)) (cm (cp d 3) (rr))) (cm (cz (2)) (cp d 3)))) (ca (cm (cm (cz (2)) (cp d 2)) (cm (e) (rr))) (ca (cm (cz (2)) (cm (cp d 2) (e))) (cm (cm (cz (1)) (cp d 2)) (cm (k) (rr)))))) (ca (ca (cm (cz (1)) (cm (cp d 2) (k))) (ca (cm (cm (cz (2)) (cp d 2)) (cm (i) (rr))) (cm (cz (2)) (cm (cp d 2) (i))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (e) (cm (i) (rr)))) (cm (cm (cz (-2)) (d)) (cm (e) (i)))) (ca (cm (cm (cz (-1)) (cp e 2)) (cm (k) (rr))) (cm (cz (-1)) (cm (cp e 2) (k))))))),
    ca (ca (ca (ca (cm (cz (1)) (cm (cp b 2) (rr))) (ca (cm (cz (1)) (cp b 2)) (cm (cm (cz (4)) (b)) (cm (d) (rr))))) (ca (ca (cm (cz (4)) (cm (b) (d))) (cm (cm (cz (2)) (b)) (cm (e) (rr)))) (ca (cm (cz (2)) (cm (b) (e))) (cm (cm (cz (2)) (b)) (cm (k) (rr)))))) (ca (ca (cm (cz (2)) (cm (b) (k))) (ca (cm (cz (2)) (cm (b) (i))) (cm (cz (4)) (cm (cp d 2) (rr))))) (ca (ca (cm (cz (4)) (cp d 2)) (cm (cm (cz (2)) (d)) (cm (e) (rr)))) (ca (cm (cz (4)) (cm (d) (e))) (cm (cm (cz (4)) (d)) (cm (k) (rr))))))) (ca (ca (ca (cm (cz (4)) (cm (d) (k))) (ca (cm (cm (cz (2)) (d)) (cm (i) (rr))) (cm (cz (4)) (cm (d) (i))))) (ca (ca (cm (cz (-1)) (cm (cp e 2) (rr))) (cm (cz (-1)) (cp e 2))) (ca (cm (cz (2)) (cm (e) (k))) (cm (cm (cz (-2)) (e)) (cm (i) (rr)))))) (ca (ca (cm (cz (-2)) (cm (e) (i))) (ca (cm (cz (1)) (cm (cp k 2) (rr))) (cm (cz (1)) (cp k 2)))) (ca (ca (cm (cm (cz (2)) (k)) (cm (i) (rr))) (cm (cz (2)) (cm (k) (i)))) (ca (cm (cz (-1)) (cm (cp i 2) (rr))) (cm (cz (-1)) (cp i 2)))))),
    ca (ca (ca (cm (cz (2)) (cm (b) (rr))) (cm (cz (2)) (b))) (ca (cm (cz (4)) (cm (d) (rr))) (cm (cz (4)) (d)))) (ca (ca (cm (cz (4)) (e)) (cm (cz (2)) (cm (k) (rr)))) (ca (cm (cz (2)) (k)) (cm (cz (4)) (i)))),
    ca (ca (ca (ca (ca (ca (cm (cm (cz (1)) (cp a 2)) (cm (b) (g))) (cm (cm (cz (2)) (cp a 2)) (cm (d) (g)))) (ca (cm (cm (cz (2)) (cp a 2)) (cm (e) (g))) (cm (cm (cz (1)) (cp a 2)) (cm (g) (k))))) (ca (ca (cm (cm (cz (2)) (cp a 2)) (cm (g) (i))) (cm (cm (cz (1)) (a)) (cm (b) (cp c 2)))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (c) (g)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (f) (g))))))) (ca (ca (ca (cm (cm (cz (1)) (a)) (cm (b) (cp g 2))) (cm (cm (cz (2)) (a)) (cm (b) (cm (g) (j))))) (ca (cm (cm (cz (-1)) (a)) (cm (b) (cp j 2))) (cm (cm (cz (2)) (a)) (cm (cp c 2) (d))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (cp c 2) (e))) (cm (cm (cz (1)) (a)) (cm (cp c 2) (k)))) (ca (cm (cm (cz (2)) (a)) (cm (cp c 2) (i))) (cm (cm (cz (4)) (a)) (cm (c) (cm (d) (g)))))))) (ca (ca (ca (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (e) (g)))) (cm (cm (cz (2)) (a)) (cm (c) (cm (g) (k))))) (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (g) (i)))) (cm (cm (cz (4)) (a)) (cm (d) (cm (f) (g)))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (d) (cp g 2))) (cm (cm (cz (4)) (a)) (cm (d) (cm (g) (j))))) (ca (cm (cm (cz (-2)) (a)) (cm (d) (cp j 2))) (cm (cm (cz (4)) (a)) (cm (e) (cm (f) (g))))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (e) (cp g 2))) (cm (cm (cz (4)) (a)) (cm (e) (cm (g) (j))))) (ca (cm (cm (cz (-2)) (a)) (cm (e) (cp j 2))) (cm (cm (cz (2)) (a)) (cm (f) (cm (g) (k)))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (f) (cm (g) (i)))) (cm (cm (cz (1)) (a)) (cm (cp g 2) (k)))) (ca (cm (cm (cz (2)) (a)) (cm (cp g 2) (i))) (cm (cm (cz (2)) (a)) (cm (g) (cm (k) (j))))))))) (ca (ca (ca (ca (ca (cm (cm (cz (4)) (a)) (cm (g) (cm (i) (j)))) (cm (cm (cz (-1)) (a)) (cm (k) (cp j 2)))) (ca (cm (cm (cz (-2)) (a)) (cm (i) (cp j 2))) (cm (cz (2)) (cm (b) (cp c 3))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (cp c 2) (f))) (cm (cm (cz (1)) (b)) (cm (cp c 2) (g)))) (ca (cm (cm (cz (2)) (b)) (cm (cp c 2) (j))) (cm (cm (cz (-2)) (b)) (cm (c) (cm (f) (j))))))) (ca (ca (ca (cm (cm (cz (-1)) (b)) (cm (cp f 2) (g))) (cm (cz (4)) (cm (cp c 3) (d)))) (ca (cm (cz (4)) (cm (cp c 3) (e))) (cm (cz (2)) (cm (cp c 3) (k))))) (ca (ca (cm (cz (4)) (cm (cp c 3) (i))) (cm (cm (cz (4)) (cp c 2)) (cm (d) (f)))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (d) (g))) (cm (cm (cz (4)) (cp c 2)) (cm (d) (j))))))) (ca (ca (ca (ca (cm (cm (cz (4)) (cp c 2)) (cm (e) (f))) (cm (cm (cz (2)) (cp c 2)) (cm (e) (g)))) (ca (cm (cm (cz (4)) (cp c 2)) (cm (e) (j))) (cm (cm (cz (2)) (cp c 2)) (cm (f) (k))))) (ca (ca (cm (cm (cz (4)) (cp c 2)) (cm (f) (i))) (cm (cm (cz (1)) (cp c 2)) (cm (g) (k)))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (g) (i))) (cm (cm (cz (2)) (cp c 2)) (cm (k) (j)))))) (ca (ca (ca (cm (cm (cz (4)) (cp c 2)) (cm (i) (j))) (cm (cm (cz (-4)) (c)) (cm (d) (cm (f) (j))))) (ca (cm (cm (cz (-4)) (c)) (cm (e) (cm (f) (j)))) (cm (cm (cz (-2)) (c)) (cm (f) (cm (k) (j)))))) (ca (ca (cm (cm (cz (-4)) (c)) (cm (f) (cm (i) (j)))) (cm (cm (cz (-2)) (d)) (cm (cp f 2) (g)))) (ca (cm (cm (cz (-2)) (e)) (cm (cp f 2) (g))) (ca (cm (cm (cz (-1)) (cp f 2)) (cm (g) (k))) (cm (cm (cz (-2)) (cp f 2)) (cm (g) (i))))))))),
    ca (ca (ca (cm (cz (-1)) (cm (cp a 2) (g))) (ca (cm (cz (-1)) (cm (a) (cp c 2))) (cm (cm (cz (-2)) (a)) (cm (c) (g))))) (ca (cm (cm (cz (-2)) (a)) (cm (f) (g))) (ca (cm (cz (-1)) (cm (a) (cp g 2))) (cm (cm (cz (-2)) (a)) (cm (g) (j)))))) (ca (ca (cm (cz (1)) (cm (a) (cp j 2))) (ca (cm (cz (-2)) (cp c 3)) (cm (cz (-2)) (cm (cp c 2) (f))))) (ca (ca (cm (cz (-1)) (cm (cp c 2) (g))) (cm (cz (-2)) (cm (cp c 2) (j)))) (ca (cm (cm (cz (2)) (c)) (cm (f) (j))) (cm (cz (1)) (cm (cp f 2) (g)))))),
    ca (ca (ca (ca (ca (ca (cm (cm (cz (1)) (cp a 2)) (cm (b) (k))) (ca (cm (cm (cz (2)) (cp a 2)) (cm (d) (k))) (cm (cm (cz (2)) (cp a 2)) (cm (e) (k))))) (ca (cm (cz (1)) (cm (cp a 2) (cp k 2))) (ca (cm (cm (cz (2)) (cp a 2)) (cm (k) (i))) (cm (cz (-1)) (cm (cp a 2) (cp i 2)))))) (ca (ca (cm (cm (cz (1)) (a)) (cm (cp b 2) (g))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (c) (d)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (c) (k)))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (d) (g)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (e) (g))))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (f) (k)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (g) (k)))))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (g) (i)))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (k) (j)))) (cm (cm (cz (4)) (a)) (cm (c) (cp d 2))))) (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (d) (e)))) (ca (cm (cm (cz (6)) (a)) (cm (c) (cm (d) (k)))) (cm (cm (cz (4)) (a)) (cm (c) (cm (d) (i))))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (e) (k)))) (ca (cm (cm (cz (-2)) (a)) (cm (c) (cm (e) (i)))) (cm (cm (cz (2)) (a)) (cm (c) (cp k 2))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (k) (i)))) (cm (cm (cz (-2)) (a)) (cm (c) (cp i 2)))) (ca (cm (cm (cz (4)) (a)) (cm (d) (cm (f) (k)))) (cm (cm (cz (2)) (a)) (cm (d) (cm (g) (k))))))))) (ca (ca (ca (ca (cm (cm (cz (4)) (a)) (cm (d) (cm (k) (j)))) (ca (cm (cm (cz (-1)) (a)) (cm (cp e 2) (g))) (cm (cm (cz (4)) (a)) (cm (e) (cm (f) (k)))))) (ca (cm (cm (cz (2)) (a)) (cm (e) (cm (g) (k)))) (ca (cm (cm (cz (4)) (a)) (cm (e) (cm (k) (j)))) (cm (cm (cz (2)) (a)) (cm (f) (cp k 2)))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (f) (cm (k) (i)))) (ca (cm (cm (cz (-2)) (a)) (cm (f) (cp i 2))) (cm (cm (cz (1)) (a)) (cm (g) (cp k 2))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (g) (cm (k) (i)))) (cm (cm (cz (-1)) (a)) (cm (g) (cp i 2)))) (ca (cm (cm (cz (2)) (a)) (cm (cp k 2) (j))) (cm (cm (cz (4)) (a)) (cm (k) (cm (i) (j)))))))) (ca (ca (ca (cm (cm (cz (-2)) (a)) (cm (cp i 2) (j))) (ca (cm (cm (cz (2)) (cp b 2)) (cm (c) (g))) (cm (cm (cz (2)) (cp b 2)) (cm (f) (g))))) (ca (cm (cz (1)) (cm (cp b 2) (cp g 2))) (ca (cm (cm (cz (2)) (cp b 2)) (cm (g) (j))) (cm (cz (-1)) (cm (cp b 2) (cp j 2)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (cp c 2) (d))) (ca (cm (cm (cz (4)) (b)) (cm (c) (cm (d) (f)))) (cm (cm (cz (6)) (b)) (cm (c) (cm (d) (g)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (c) (cm (d) (j)))) (cm (cm (cz (4)) (b)) (cm (c) (cm (e) (g))))) (ca (cm (cm (cz (2)) (b)) (cm (c) (cm (g) (k)))) (cm (cm (cz (4)) (b)) (cm (c) (cm (g) (i)))))))))) (ca (ca (ca (ca (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (f) (g)))) (ca (cm (cm (cz (-2)) (b)) (cm (d) (cm (f) (j)))) (cm (cm (cz (2)) (b)) (cm (d) (cp g 2))))) (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (g) (j)))) (ca (cm (cm (cz (-2)) (b)) (cm (d) (cp j 2))) (cm (cm (cz (4)) (b)) (cm (e) (cm (f) (g))))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (e) (cp g 2))) (ca (cm (cm (cz (4)) (b)) (cm (e) (cm (g) (j)))) (cm (cm (cz (-2)) (b)) (cm (e) (cp j 2))))) (ca (ca (cm (cm (cz (-1)) (b)) (cm (cp f 2) (k))) (cm (cm (cz (2)) (b)) (cm (f) (cm (g) (k))))) (ca (cm (cm (cz (4)) (b)) (cm (f) (cm (g) (i)))) (cm (cm (cz (1)) (b)) (cm (cp g 2) (k))))))) (ca (ca (ca (cm (cm (cz (2)) (b)) (cm (cp g 2) (i))) (ca (cm (cm (cz (2)) (b)) (cm (g) (cm (k) (j)))) (cm (cm (cz (4)) (b)) (cm (g) (cm (i) (j)))))) (ca (cm (cm (cz (-1)) (b)) (cm (k) (cp j 2))) (ca (cm (cm (cz (-2)) (b)) (cm (i) (cp j 2))) (cm (cz (8)) (cm (cp c 2) (cp d 2)))))) (ca (ca (cm (cm (cz (8)) (cp c 2)) (cm (d) (e))) (ca (cm (cm (cz (4)) (cp c 2)) (cm (d) (k))) (cm (cm (cz (8)) (cp c 2)) (cm (d) (i))))) (ca (ca (cm (cm (cz (-4)) (cp c 2)) (cm (e) (i))) (cm (cm (cz (8)) (c)) (cm (cp d 2) (f)))) (ca (cm (cm (cz (4)) (c)) (cm (cp d 2) (g))) (cm (cm (cz (8)) (c)) (cm (cp d 2) (j)))))))) (ca (ca (ca (ca (cm (cm (cz (8)) (c)) (cm (d) (cm (e) (f)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (e) (g)))) (cm (cm (cz (8)) (c)) (cm (d) (cm (e) (j)))))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (f) (k)))) (ca (cm (cm (cz (8)) (c)) (cm (d) (cm (f) (i)))) (cm (cm (cz (2)) (c)) (cm (d) (cm (g) (k))))))) (ca (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (g) (i)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (k) (j)))) (cm (cm (cz (8)) (c)) (cm (d) (cm (i) (j)))))) (ca (ca (cm (cm (cz (-2)) (c)) (cm (cp e 2) (g))) (cm (cm (cz (-4)) (c)) (cm (e) (cm (f) (i))))) (ca (cm (cm (cz (-2)) (c)) (cm (e) (cm (g) (i)))) (cm (cm (cz (-4)) (c)) (cm (e) (cm (i) (j)))))))) (ca (ca (ca (cm (cm (cz (-4)) (cp d 2)) (cm (f) (j))) (ca (cm (cm (cz (-4)) (d)) (cm (e) (cm (f) (j)))) (cm (cm (cz (-2)) (d)) (cm (cp f 2) (k))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (f) (cm (k) (j)))) (cm (cm (cz (-4)) (d)) (cm (f) (cm (i) (j))))) (ca (cm (cm (cz (-2)) (cp e 2)) (cm (f) (g))) (cm (cz (-1)) (cm (cp e 2) (cp g 2)))))) (ca (ca (cm (cm (cz (-2)) (cp e 2)) (cm (g) (j))) (ca (cm (cz (1)) (cm (cp e 2) (cp j 2))) (cm (cm (cz (-2)) (e)) (cm (cp f 2) (k))))) (ca (ca (cm (cm (cz (2)) (e)) (cm (f) (cm (i) (j)))) (cm (cz (-1)) (cm (cp f 2) (cp k 2)))) (ca (cm (cm (cz (-2)) (cp f 2)) (cm (k) (i))) (cm (cz (1)) (cm (cp f 2) (cp i 2))))))))),
    ca (ca (ca (ca (ca (cm (cz (1)) (cm (cp a 2) (b))) (ca (cm (cz (2)) (cm (cp a 2) (d))) (cm (cz (2)) (cm (cp a 2) (e))))) (ca (cm (cm (cz (4)) (a)) (cm (b) (c))) (ca (cm (cm (cz (2)) (a)) (cm (b) (f))) (cm (cm (cz (6)) (a)) (cm (c) (d)))))) (ca (ca (cm (cm (cz (6)) (a)) (cm (c) (e))) (ca (cm (cm (cz (2)) (a)) (cm (c) (k))) (cm (cm (cz (2)) (a)) (cm (c) (i))))) (ca (cm (cm (cz (4)) (a)) (cm (d) (f))) (ca (cm (cm (cz (2)) (a)) (cm (d) (g))) (cm (cm (cz (4)) (a)) (cm (e) (f))))))) (ca (ca (ca (cm (cm (cz (-2)) (a)) (cm (k) (j))) (ca (cm (cm (cz (-2)) (a)) (cm (i) (j))) (cm (cz (3)) (cm (b) (cp c 2))))) (ca (cm (cm (cz (2)) (b)) (cm (c) (f))) (ca (cm (cm (cz (2)) (b)) (cm (c) (g))) (cm (cm (cz (2)) (b)) (cm (c) (j)))))) (ca (ca (cm (cz (-1)) (cm (b) (cp f 2))) (ca (cm (cm (cz (-2)) (b)) (cm (f) (g))) (cm (cm (cz (-2)) (b)) (cm (f) (j))))) (ca (cm (cz (2)) (cm (cp c 2) (d))) (ca (cm (cz (2)) (cm (cp c 2) (e))) (cm (cz (3)) (cm (cp c 2) (k)))))))) (ca (ca (ca (ca (cm (cz (2)) (cm (cp c 2) (i))) (ca (cm (cm (cz (6)) (c)) (cm (d) (g))) (cm (cm (cz (2)) (c)) (cm (e) (g))))) (ca (cm (cm (cz (2)) (c)) (cm (e) (j))) (ca (cm (cm (cz (2)) (c)) (cm (f) (k))) (cm (cm (cz (2)) (c)) (cm (f) (i)))))) (ca (ca (cm (cm (cz (4)) (c)) (cm (g) (k))) (ca (cm (cm (cz (6)) (c)) (cm (g) (i))) (cm (cm (cz (2)) (c)) (cm (k) (j))))) (ca (cm (cz (-2)) (cm (d) (cp f 2))) (ca (cm (cm (cz (-2)) (d)) (cm (f) (j))) (cm (cz (2)) (cm (d) (cp g 2))))))) (ca (ca (ca (cm (cm (cz (4)) (d)) (cm (g) (j))) (ca (cm (cz (-2)) (cm (d) (cp j 2))) (cm (cz (-2)) (cm (e) (cp f 2))))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (g))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (j))) (cm (cm (cz (-2)) (f)) (cm (k) (j)))))) (ca (ca (cm (cm (cz (-2)) (f)) (cm (i) (j))) (ca (cm (cz (1)) (cm (cp g 2) (k))) (cm (cz (2)) (cm (cp g 2) (i))))) (ca (ca (cm (cm (cz (2)) (g)) (cm (k) (j))) (cm (cm (cz (4)) (g)) (cm (i) (j)))) (ca (cm (cz (-1)) (cm (k) (cp j 2))) (cm (cz (-2)) (cm (i) (cp j 2)))))))),
    ca (ca (ca (cm (cz (-2)) (cp a 2)) (ca (cm (cz (-8)) (cm (a) (c))) (cm (cz (-4)) (cm (a) (f))))) (ca (cm (cz (-2)) (cm (a) (g))) (ca (cm (cz (-6)) (cp c 2)) (cm (cz (-4)) (cm (c) (f)))))) (ca (ca (cm (cz (-8)) (cm (c) (g))) (ca (cm (cz (-4)) (cm (c) (j))) (cm (cz (2)) (cp f 2)))) (ca (ca (cm (cz (4)) (cm (f) (j))) (cm (cz (-2)) (cp g 2))) (ca (cm (cz (-4)) (cm (g) (j))) (cm (cz (2)) (cp j 2))))),
    ca (ca (ca (ca (ca (ca (cm (cm (cz (1)) (a)) (cm (cp b 2) (k))) (cm (cm (cz (1)) (a)) (cm (b) (cp d 2)))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (d) (k)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (e) (k)))))) (ca (ca (cm (cm (cz (1)) (a)) (cm (b) (cp k 2))) (cm (cm (cz (2)) (a)) (cm (b) (cm (k) (i))))) (ca (cm (cm (cz (-1)) (a)) (cm (b) (cp i 2))) (cm (cz (2)) (cm (a) (cp d 3)))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (cp d 2) (e))) (cm (cm (cz (1)) (a)) (cm (cp d 2) (k)))) (ca (cm (cm (cz (2)) (a)) (cm (cp d 2) (i))) (cm (cm (cz (-2)) (a)) (cm (d) (cm (e) (i)))))) (ca (ca (cm (cm (cz (-1)) (a)) (cm (cp e 2) (k))) (cm (cm (cz (2)) (cp b 2)) (cm (c) (k)))) (ca (cm (cm (cz (2)) (cp b 2)) (cm (f) (k))) (cm (cm (cz (1)) (cp b 2)) (cm (g) (k))))))) (ca (ca (ca (ca (cm (cm (cz (2)) (cp b 2)) (cm (k) (j))) (cm (cm (cz (2)) (b)) (cm (c) (cp d 2)))) (ca (cm (cm (cz (4)) (b)) (cm (c) (cm (d) (k)))) (cm (cm (cz (4)) (b)) (cm (c) (cm (e) (k)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (c) (cp k 2))) (cm (cm (cz (4)) (b)) (cm (c) (cm (k) (i))))) (ca (cm (cm (cz (-2)) (b)) (cm (c) (cp i 2))) (cm (cm (cz (2)) (b)) (cm (cp d 2) (f)))))) (ca (ca (ca (cm (cm (cz (1)) (b)) (cm (cp d 2) (g))) (cm (cm (cz (2)) (b)) (cm (cp d 2) (j)))) (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (f) (k)))) (cm (cm (cz (2)) (b)) (cm (d) (cm (g) (k)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (k) (j)))) (cm (cm (cz (4)) (b)) (cm (e) (cm (f) (k))))) (ca (cm (cm (cz (2)) (b)) (cm (e) (cm (g) (k)))) (cm (cm (cz (4)) (b)) (cm (e) (cm (k) (j))))))))) (ca (ca (ca (ca (ca (cm (cm (cz (2)) (b)) (cm (f) (cp k 2))) (cm (cm (cz (4)) (b)) (cm (f) (cm (k) (i))))) (ca (cm (cm (cz (-2)) (b)) (cm (f) (cp i 2))) (cm (cm (cz (1)) (b)) (cm (g) (cp k 2))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (g) (cm (k) (i)))) (cm (cm (cz (-1)) (b)) (cm (g) (cp i 2)))) (ca (cm (cm (cz (2)) (b)) (cm (cp k 2) (j))) (cm (cm (cz (4)) (b)) (cm (k) (cm (i) (j))))))) (ca (ca (ca (cm (cm (cz (-2)) (b)) (cm (cp i 2) (j))) (cm (cz (4)) (cm (c) (cp d 3)))) (ca (cm (cm (cz (4)) (c)) (cm (cp d 2) (e))) (cm (cm (cz (2)) (c)) (cm (cp d 2) (k))))) (ca (ca (cm (cm (cz (4)) (c)) (cm (cp d 2) (i))) (cm (cm (cz (-4)) (c)) (cm (d) (cm (e) (i))))) (ca (cm (cm (cz (-2)) (c)) (cm (cp e 2) (k))) (cm (cz (4)) (cm (cp d 3) (f))))))) (ca (ca (ca (ca (cm (cz (2)) (cm (cp d 3) (g))) (cm (cz (4)) (cm (cp d 3) (j)))) (ca (cm (cm (cz (4)) (cp d 2)) (cm (e) (f))) (cm (cm (cz (2)) (cp d 2)) (cm (e) (g))))) (ca (ca (cm (cm (cz (4)) (cp d 2)) (cm (e) (j))) (cm (cm (cz (2)) (cp d 2)) (cm (f) (k)))) (ca (cm (cm (cz (4)) (cp d 2)) (cm (f) (i))) (cm (cm (cz (1)) (cp d 2)) (cm (g) (k)))))) (ca (ca (ca (cm (cm (cz (2)) (cp d 2)) (cm (g) (i))) (cm (cm (cz (2)) (cp d 2)) (cm (k) (j)))) (ca (cm (cm (cz (4)) (cp d 2)) (cm (i) (j))) (cm (cm (cz (-4)) (d)) (cm (e) (cm (f) (i)))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (e) (cm (g) (i)))) (cm (cm (cz (-4)) (d)) (cm (e) (cm (i) (j))))) (ca (cm (cm (cz (-2)) (cp e 2)) (cm (f) (k))) (ca (cm (cm (cz (-1)) (cp e 2)) (cm (g) (k))) (cm (cm (cz (-2)) (cp e 2)) (cm (k) (j))))))))),
    ca (ca (ca (ca (ca (cm (cz (1)) (cm (a) (cp b 2))) (ca (cm (cm (cz (4)) (a)) (cm (b) (d))) (cm (cm (cz (2)) (a)) (cm (b) (e))))) (ca (cm (cz (3)) (cm (a) (cp d 2))) (ca (cm (cm (cz (2)) (a)) (cm (d) (e))) (cm (cm (cz (2)) (a)) (cm (d) (k)))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (d) (i))) (ca (cm (cz (-1)) (cm (a) (cp e 2))) (cm (cm (cz (-2)) (a)) (cm (e) (k))))) (ca (cm (cm (cz (-2)) (a)) (cm (e) (i))) (ca (cm (cz (2)) (cm (cp b 2) (c))) (cm (cz (2)) (cm (cp b 2) (f))))))) (ca (ca (ca (cm (cm (cz (6)) (b)) (cm (c) (d))) (ca (cm (cm (cz (4)) (b)) (cm (c) (e))) (cm (cm (cz (2)) (b)) (cm (c) (k))))) (ca (cm (cm (cz (6)) (b)) (cm (d) (f))) (ca (cm (cm (cz (2)) (b)) (cm (d) (g))) (cm (cm (cz (2)) (b)) (cm (d) (j)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (e) (f))) (ca (cm (cm (cz (-2)) (b)) (cm (g) (i))) (cm (cm (cz (-2)) (b)) (cm (i) (j))))) (ca (cm (cz (2)) (cm (c) (cp d 2))) (ca (cm (cm (cz (6)) (c)) (cm (d) (k))) (cm (cz (-2)) (cm (c) (cp e 2)))))))) (ca (ca (ca (ca (cm (cm (cz (-2)) (c)) (cm (e) (i))) (ca (cm (cz (2)) (cm (c) (cp k 2))) (cm (cm (cz (4)) (c)) (cm (k) (i))))) (ca (cm (cz (-2)) (cm (c) (cp i 2))) (ca (cm (cz (2)) (cm (cp d 2) (f))) (cm (cz (3)) (cm (cp d 2) (g)))))) (ca (ca (cm (cz (2)) (cm (cp d 2) (j))) (ca (cm (cm (cz (2)) (d)) (cm (e) (g))) (cm (cm (cz (2)) (d)) (cm (e) (j))))) (ca (cm (cm (cz (2)) (d)) (cm (f) (k))) (ca (cm (cm (cz (2)) (d)) (cm (f) (i))) (cm (cm (cz (4)) (d)) (cm (g) (k))))))) (ca (ca (ca (cm (cm (cz (2)) (d)) (cm (g) (i))) (ca (cm (cm (cz (6)) (d)) (cm (k) (j))) (cm (cz (-2)) (cm (cp e 2) (f))))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (k))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (i))) (cm (cm (cz (-2)) (e)) (cm (g) (i)))))) (ca (ca (cm (cm (cz (-2)) (e)) (cm (i) (j))) (ca (cm (cz (1)) (cm (g) (cp k 2))) (cm (cm (cz (2)) (g)) (cm (k) (i))))) (ca (ca (cm (cz (-1)) (cm (g) (cp i 2))) (cm (cz (2)) (cm (cp k 2) (j)))) (ca (cm (cm (cz (4)) (k)) (cm (i) (j))) (cm (cz (-2)) (cm (cp i 2) (j)))))))),
    ca (ca (ca (ca (cm (cz (-2)) (cm (a) (b))) (cm (cz (-4)) (cm (a) (d)))) (ca (cm (cz (-4)) (cm (a) (e))) (cm (cz (-4)) (cm (b) (c))))) (ca (ca (cm (cz (-4)) (cm (b) (f))) (cm (cz (-4)) (cm (c) (d)))) (ca (cm (cz (-4)) (cm (c) (e))) (cm (cz (-4)) (cm (c) (k)))))) (ca (ca (ca (cm (cz (-4)) (cm (c) (i))) (cm (cz (-4)) (cm (d) (f)))) (ca (cm (cz (-4)) (cm (d) (g))) (cm (cz (-4)) (cm (d) (j))))) (ca (ca (cm (cz (-4)) (cm (e) (f))) (cm (cz (-2)) (cm (g) (k)))) (ca (cm (cz (-4)) (cm (g) (i))) (ca (cm (cz (-4)) (cm (k) (j))) (cm (cz (-4)) (cm (i) (j))))))),
    ca (ca (ca (cm (cz (-1)) (cm (cp b 2) (k))) (ca (cm (cz (-1)) (cm (b) (cp d 2))) (cm (cm (cz (-2)) (b)) (cm (d) (k))))) (ca (cm (cm (cz (-2)) (b)) (cm (e) (k))) (ca (cm (cz (-1)) (cm (b) (cp k 2))) (cm (cm (cz (-2)) (b)) (cm (k) (i)))))) (ca (ca (cm (cz (1)) (cm (b) (cp i 2))) (ca (cm (cz (-2)) (cp d 3)) (cm (cz (-2)) (cm (cp d 2) (e))))) (ca (ca (cm (cz (-1)) (cm (cp d 2) (k))) (cm (cz (-2)) (cm (cp d 2) (i)))) (ca (cm (cm (cz (2)) (d)) (cm (e) (i))) (cm (cz (1)) (cm (cp e 2) (k)))))),
    ca (ca (ca (cm (cz (-2)) (cp b 2)) (ca (cm (cz (-8)) (cm (b) (d))) (cm (cz (-4)) (cm (b) (e))))) (ca (cm (cz (-2)) (cm (b) (k))) (ca (cm (cz (-6)) (cp d 2)) (cm (cz (-4)) (cm (d) (e)))))) (ca (ca (cm (cz (-8)) (cm (d) (k))) (ca (cm (cz (-4)) (cm (d) (i))) (cm (cz (2)) (cp e 2)))) (ca (ca (cm (cz (4)) (cm (e) (i))) (cm (cz (-2)) (cp k 2))) (ca (cm (cz (-4)) (cm (k) (i))) (cm (cz (2)) (cp i 2)))))]

def polynomial (p : Fin 19 → ℂ) (x y z : ℂ) : ℂ :=
  ca (ca (ca (ca (cm (p 0) (cm (x) (cp y 3))) (cm (cm (p 1) (x)) (cm (cp y 2) (z)))) (ca (cm (p 2) (cm (x) (cp y 2))) (cm (cm (p 3) (x)) (cm (y) (cp z 2))))) (ca (ca (cm (cm (p 4) (x)) (cm (y) (z))) (cm (p 5) (cm (x) (y)))) (ca (cm (p 6) (cm (x) (cp z 3))) (ca (cm (p 7) (cm (x) (cp z 2))) (cm (p 8) (cm (x) (z))))))) (ca (ca (ca (cm (p 9) (cm (cp y 3) (z))) (cm (p 10) (cp y 3))) (ca (cm (p 11) (cm (cp y 2) (cp z 2))) (ca (cm (p 12) (cm (cp y 2) (z))) (cm (p 13) (cp y 2))))) (ca (ca (cm (p 14) (cm (y) (cp z 3))) (cm (p 15) (cm (y) (cp z 2)))) (ca (cm (p 16) (cm (y) (z))) (ca (cm (p 17) (cp z 3)) (cm (p 18) (cp z 2))))))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
lemma extract_coefficients (p : Fin 19 → ℂ)
    (hp : ∀ x y z, polynomial p x y z = 0) : ∀ n, p n = 0 := by
  have h0 := hp 0 0 1
  have h1 := hp 0 0 (-1)
  have h2 := hp 0 1 0
  have h3 := hp 0 1 1
  have h4 := hp 0 1 (-1)
  have h5 := hp 0 1 2
  have h6 := hp 0 (-1) 0
  have h7 := hp 0 (-1) 1
  have h8 := hp 0 (-1) (-1)
  have h9 := hp 0 2 1
  have h10 := hp 1 0 1
  have h11 := hp 1 0 (-1)
  have h12 := hp 1 0 2
  have h13 := hp 1 1 0
  have h14 := hp 1 1 1
  have h15 := hp 1 1 (-1)
  have h16 := hp 1 (-1) 0
  have h17 := hp 1 (-1) 1
  have h18 := hp 1 2 0
  simp only [polynomial, ca, cm, cp, cz] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  intro n
  fin_cases n
  · change p 0 = 0
    linear_combination (-1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h6 + (-1 / 2 : ℂ) * h13 + (-1 / 6 : ℂ) * h16 + (1 / 6 : ℂ) * h18
  · change p 1 = 0
    linear_combination (1 : ℂ) * h0 + (1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (1 / 2 : ℂ) * h6 + (-1 / 2 : ℂ) * h7 + (-1 : ℂ) * h10 + (-1 / 2 : ℂ) * h13 + (1 / 2 : ℂ) * h14 + (-1 / 2 : ℂ) * h16 + (1 / 2 : ℂ) * h17
  · change p 2 = 0
    linear_combination (-1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h6 + (1 / 2 : ℂ) * h13 + (1 / 2 : ℂ) * h16
  · change p 3 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (1 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (-1 / 2 : ℂ) * h4 + (-1 / 2 : ℂ) * h10 + (-1 / 2 : ℂ) * h11 + (-1 : ℂ) * h13 + (1 / 2 : ℂ) * h14 + (1 / 2 : ℂ) * h15
  · change p 4 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h4 + (-1 / 2 : ℂ) * h6 + (1 / 2 : ℂ) * h7 + (1 / 2 : ℂ) * h10 + (1 / 2 : ℂ) * h11 + (1 / 2 : ℂ) * h13 + (-1 / 2 : ℂ) * h15 + (1 / 2 : ℂ) * h16 + (-1 / 2 : ℂ) * h17
  · change p 5 = 0
    linear_combination (1 : ℂ) * h13 + (-1 / 3 : ℂ) * h16 + (-1 / 6 : ℂ) * h18
  · change p 6 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h10 + (-1 / 6 : ℂ) * h11 + (1 / 6 : ℂ) * h12
  · change p 7 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h10 + (1 / 2 : ℂ) * h11
  · change p 8 = 0
    linear_combination (1 : ℂ) * h10 + (-1 / 3 : ℂ) * h11 + (-1 / 6 : ℂ) * h12
  · change p 9 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (1 / 2 : ℂ) * h6 + (-1 / 6 : ℂ) * h7 + (1 / 6 : ℂ) * h9
  · change p 10 = 0
    linear_combination (1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h6
  · change p 11 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2 + (1 / 4 : ℂ) * h3 + (1 / 4 : ℂ) * h4 + (-1 / 2 : ℂ) * h6 + (1 / 4 : ℂ) * h7 + (1 / 4 : ℂ) * h8
  · change p 12 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (1 / 4 : ℂ) * h3 + (-1 / 4 : ℂ) * h4 + (1 / 4 : ℂ) * h7 + (-1 / 4 : ℂ) * h8
  · change p 13 = 0
    linear_combination (1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h6
  · change p 14 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (-1 / 6 : ℂ) * h4 + (1 / 6 : ℂ) * h5
  · change p 15 = 0
    linear_combination (-1 / 2 : ℂ) * h2 + (1 / 4 : ℂ) * h3 + (1 / 4 : ℂ) * h4 + (1 / 2 : ℂ) * h6 + (-1 / 4 : ℂ) * h7 + (-1 / 4 : ℂ) * h8
  · change p 16 = 0
    linear_combination (-1 / 2 : ℂ) * h1 + (5 / 4 : ℂ) * h3 + (-1 / 12 : ℂ) * h4 + (-1 / 6 : ℂ) * h5 + (-1 / 2 : ℂ) * h6 + (-1 / 12 : ℂ) * h7 + (1 / 4 : ℂ) * h8 + (-1 / 6 : ℂ) * h9
  · change p 17 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1
  · change p 18 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma permanent_expansion (a b c d e f g k i j rr x y z : ℂ) (hr : rr ^ 2 = 2) :
    Matrix.permanent (Matrix.of fun r s => (1 : ℂ) + model a b c d e f g k i j rr x y z r s) - 24 =
      polynomial (coefficients a b c d e f g k i j rr) x y z := by
  simp [perm4, Matrix.of_apply, model, polynomial, coefficients, ca, cm, cp, cz,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (norm := skip) (ca (ca (ca (cm (cm (cz (-1)) (a)) (cm (g) (cm (cp x 2) (cp y 2)))) (ca (cm (cm (cz (-1)) (cm (a) (k))) (cm (cp x 2) (cm (y) (z)))) (cm (cm (cz (-1)) (a)) (cm (cp x 2) (y))))) (ca (ca (cm (cm (cz (-1)) (cm (b) (g))) (cm (cp x 2) (cm (y) (z)))) (cm (cm (cz (-1)) (b)) (cm (k) (cm (cp x 2) (cp z 2))))) (ca (cm (cm (cz (-1)) (b)) (cm (cp x 2) (z))) (cm (cm (cz (-1)) (cp c 2)) (cm (cp x 2) (cp y 2)))))) (ca (ca (cm (cm (cz (-2)) (cm (c) (d))) (cm (cp x 2) (cm (y) (z)))) (ca (cm (cm (cz (-2)) (c)) (cm (cp x 2) (y))) (cm (cm (cz (-1)) (cp d 2)) (cm (cp x 2) (cp z 2))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (cp x 2) (z))) (cm (cm (cz (-1)) (g)) (cm (cp x 2) (y)))) (ca (cm (cm (cz (-1)) (k)) (cm (cp x 2) (z))) (cm (cz (-2)) (cp x 2)))))) * hr
  simp only [ca, cm, cp, cz]
  ring

lemma coefficients_zero (a b c d e f g k i j rr : ℂ) (hr : rr ^ 2 = 2)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1 : ℂ) +
      model a b c d e f g k i j rr x y z r s) = 24) : ∀ n, coefficients a b c d e f g k i j rr n = 0 := by
  apply extract_coefficients
  intro x y z
  rw [← permanent_expansion a b c d e f g k i j rr x y z hr, hp x y z]
  ring

end PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

namespace PEqualNP.Outside.L_gct_231_aux.DoubleSingleGeometry

open PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

def base (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,0,0],![0,0,0,0],![0,0,h-1,1],![0,0,1,-h-1]]

def ModelImpossible : Prop := ∀ a b c d e f g k i j rr : ℂ,
  rr^2=2 → (f≠0 ∨ j≠0) → (e≠0 ∨ i≠0) →
  (∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
    model a b c d e f g k i j rr x y z r s)=24) → False

def DisjointMaximal : Prop := ∀ A B C : Matrix (Fin 4) (Fin 4) ℂ,
  (∀ r s, A r s=A s r) → (∀ r s, B r s=B s r) → (∀ r s, C r s=C s r) →
  (∀ j, A 2 j=0) → (∀ j, A 3 j=0) → (∀ j, B 0 j=0) → (∀ j, B 1 j=0) →
  A≠0 → B≠0 →
  (∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+x*A r s+y*B r s+z*C r s)=24) →
  ∃ p q : ℂ, C=Matrix.of fun r s => p*A r s+q*B r s

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma total_entries_zero (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hp : ∀ w, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+w*M r s)=24) :
    ∑ r, ∑ s, M r s=0 := by
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have hn2 := hp (-2)
  simp [perm4, Matrix.of_apply] at h1 hn1 h2 hn2
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero]
  linear_combination (1/9:ℂ)*h1-(1/9:ℂ)*hn1-(1/72:ℂ)*h2+(1/72:ℂ)*hn2

lemma normalized_block (a b c : ℂ) (hS : a+c+2*b=0) (hQ : a*c+b^2=0)
    (hne : a≠0 ∨ b≠0 ∨ c≠0) :
    b≠0 ∧ ∃ h : ℂ, h^2=2 ∧ a=b*(h-1) ∧ c=b*(-h-1) := by
  have hb : b≠0 := by
    intro hb
    have ha2 : a^2=0 := by linear_combination a*hS-hQ+(b-2*a)*hb
    have ha := eq_zero_of_pow_eq_zero ha2
    have hc : c=0 := by linear_combination hS-ha-2*hb
    exact hne.elim (fun hn => hn ha) (fun hn => hn.elim (fun hn => hn hb) (fun hn => hn hc))
  have hmul : (a/b)*b=a := div_mul_cancel₀ a hb
  have haq : a^2+2*a*b-b^2=0 := by linear_combination a*hS-hQ
  refine ⟨hb,a/b+1,?_,?_,?_⟩
  · apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination (a/b*b+a+2*b)*hmul+haq
  · linear_combination -hmul
  · linear_combination hS+hmul

lemma normalized_independent_impossible (hm : ModelImpossible) (hd : DisjointMaximal)
    (h : ℂ) (hh : h^2=2) (B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsB : ∀ r s, B r s=B s r) (hsC : ∀ r s, C r s=C s r)
    (hB2 : ∀ j, B 2 j=0) (hC3 : ∀ j, C 3 j=0)
    (hind : ∀ u v w : ℂ, (∀ r s, u*base h r s+v*B r s+w*C r s=0) →
      u=0 ∧ v=0 ∧ w=0)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s =>
      (1:ℂ)+x*base h r s+y*B r s+z*C r s)=24) : False := by
  have hsumB : ∑ r, ∑ s, B r s=0 := by
    apply total_entries_zero
    intro w
    simpa only [zero_mul,add_zero,zero_add] using hp 0 w 0
  have hsumC : ∑ r, ∑ s, C r s=0 := by
    apply total_entries_zero
    intro w
    simpa only [zero_mul,add_zero,zero_add] using hp 0 0 w
  have hB33 : B 3 3= -B 0 0-B 1 1-2*B 0 1-2*B 0 3-2*B 1 3 := by
    simp [Fin.sum_univ_succ,hB2,hsB 0 2,hsB 1 2,hsB 3 2,hsB 1 0,hsB 3 0,hsB 3 1] at hsumB
    linear_combination hsumB
  have hC22 : C 2 2= -C 0 0-C 1 1-2*C 0 1-2*C 0 2-2*C 1 2 := by
    simp [Fin.sum_univ_succ,hC3,hsC 0 3,hsC 1 3,hsC 2 3,hsC 1 0,hsC 2 0,hsC 2 1] at hsumC
    linear_combination hsumC
  have heq (x y z : ℂ) :
      model (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
        (B 1 1) (C 1 1) (C 1 2) (B 1 3) h x y z =
      Matrix.of (fun r s => x*base h r s+y*B r s+z*C r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [model,base,ca,cm,cp,cz,Matrix.of_apply,hB2,hC3,
        hsB 0 2,hsB 1 2,hsB 3 2,hsB 1 0,hsB 3 0,hsB 3 1,
        hsC 0 3,hsC 1 3,hsC 2 3,hsC 1 0,hsC 2 0,hsC 2 1,hB33,hC22] <;> ring
  have hpmodel (x y z : ℂ) : Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      model (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
        (B 1 1) (C 1 1) (C 1 2) (B 1 3) h x y z r s)=24 := by
    rw [heq]
    simpa only [Matrix.of_apply,add_assoc] using hp x y z
  have hz := coefficients_zero (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
    (B 1 1) (C 1 1) (C 1 2) (B 1 3) h hh hpmodel
  have hsA (r s : Fin 4) : base h r s=base h s r := by
    fin_cases r <;> fin_cases s <;> simp [base]
  have hA0 (j : Fin 4) : base h 0 j=0 := by fin_cases j <;> simp [base]
  have hA1 (j : Fin 4) : base h 1 j=0 := by fin_cases j <;> simp [base]
  have hAne : base h≠0 := by
    intro he
    have ht := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 3) he
    norm_num [base] at ht
  have hBne : B≠0 := by
    intro he
    have hc := (hind 0 1 0 (by intro r s; simp [he])).2.1
    norm_num at hc
  have hCne : C≠0 := by
    intro he
    have hc := (hind 0 0 1 (by intro r s; simp [he])).2.2
    norm_num at hc
  have hcrossB : B 0 3≠0 ∨ B 1 3≠0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨hb03,hb13⟩ := hn
    have hp5 := hz 5
    simp [coefficients,ca,cm,cp,cz,hb03,hb13] at hp5
    have hdiag : B 0 0+B 1 1+2*B 0 1=0 := by
      linear_combination (-(h+1)/2)*hp5-(B 0 0+B 1 1+2*B 0 1)*hh
    have hB3 (j : Fin 4) : B 3 j=0 := by
      fin_cases j <;> simp [hsB 3 0,hsB 3 1,hB2,hsB 3 2,hb03,hb13,hB33]
      linear_combination -hdiag
    obtain ⟨p,q,hC⟩ := hd B (base h) C hsB hsA hsC hB2 hB3 hA0 hA1 hBne hAne
      (by intro x y z; simpa only [add_assoc,add_left_comm,add_comm] using hp y x z)
    have hrel (r s : Fin 4) : (-q)*base h r s+(-p)*B r s+1*C r s=0 := by
      rw [hC]
      simp only [Matrix.of_apply]
      ring
    have hc := (hind (-q) (-p) 1 hrel).2.2
    norm_num at hc
  have hcrossC : C 0 2≠0 ∨ C 1 2≠0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨hc02,hc12⟩ := hn
    have hp8 := hz 8
    simp [coefficients,ca,cm,cp,cz,hc02,hc12] at hp8
    have hdiag : C 0 0+C 1 1+2*C 0 1=0 := by
      linear_combination ((h-1)/2)*hp8-(C 0 0+C 1 1+2*C 0 1)*hh
    have hC2 (j : Fin 4) : C 2 j=0 := by
      fin_cases j <;> simp [hsC 2 0,hsC 2 1,hC3,hsC 2 3,hc02,hc12,hC22]
      linear_combination -hdiag
    obtain ⟨p,q,hB⟩ := hd C (base h) B hsC hsA hsB hC2 hC3 hA0 hA1 hCne hAne
      (by intro x y z; simpa only [add_assoc,add_left_comm,add_comm] using hp y z x)
    have hrel (r s : Fin 4) : (-q)*base h r s+1*B r s+(-p)*C r s=0 := by
      rw [hB]
      simp only [Matrix.of_apply]
      ring
    have hc := (hind (-q) 1 (-p) hrel).2.1
    norm_num at hc
  exact hm (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
    (B 1 1) (C 1 1) (C 1 2) (B 1 3) h hh hcrossB hcrossC hpmodel

end PEqualNP.Outside.L_gct_231_aux.DoubleSingleGeometry
