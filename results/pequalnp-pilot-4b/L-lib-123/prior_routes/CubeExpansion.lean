import Mathlib

namespace PriorRoutes

def cubeCount : ℕ → (List Bool → Bool) → ℕ
  | 0, f => if f [] then 1 else 0
  | k + 1, f => cubeCount k (fun x => f (false :: x)) +
      cubeCount k (fun x => f (true :: x))

def cubeDisagree (k : ℕ) (f g : List Bool → Bool) : ℕ :=
  cubeCount k (fun x => xor (f x) (g x))

def cubeBoundary : ℕ → (List Bool → Bool) → ℕ
  | 0, _ => 0
  | k + 1, f => cubeBoundary k (fun x => f (false :: x)) +
      cubeBoundary k (fun x => f (true :: x)) +
      cubeDisagree k (fun x => f (false :: x)) (fun x => f (true :: x))

lemma cubeCount_le (k : ℕ) (f : List Bool → Bool) : cubeCount k f ≤ 2 ^ k := by
  induction k generalizing f with
  | zero => simp only [cubeCount, pow_zero]; split <;> omega
  | succ k ih =>
    have h0 := ih (fun x => f (false :: x))
    have h1 := ih (fun x => f (true :: x))
    simp only [cubeCount, pow_succ]
    omega

lemma cubeCount_compare (k : ℕ) (f g : List Bool → Bool) :
    cubeCount k f ≤ cubeCount k g + cubeDisagree k f g := by
  induction k generalizing f g with
  | zero =>
    simp only [cubeCount, cubeDisagree]
    by_cases hf : f [] = true <;> by_cases hg : g [] = true <;> simp_all
  | succ k ih =>
    have h0 := ih (fun x => f (false :: x)) (fun x => g (false :: x))
    have h1 := ih (fun x => f (true :: x)) (fun x => g (true :: x))
    simp only [cubeCount, cubeDisagree] at *
    omega

lemma cubeDisagree_comm (k : ℕ) (f g : List Bool → Bool) :
    cubeDisagree k f g = cubeDisagree k g f := by
  unfold cubeDisagree
  congr 1
  funext x
  exact Bool.xor_comm _ _

lemma cubeBoundary_lower (k : ℕ) (f : List Bool → Bool) :
    min (cubeCount k f) (2 ^ k - cubeCount k f) ≤ cubeBoundary k f := by
  induction k generalizing f with
  | zero =>
    simp only [cubeBoundary, cubeCount, pow_zero]
    cases f [] <;> decide
  | succ k ih =>
    have h0 := ih (fun x => f (false :: x))
    have h1 := ih (fun x => f (true :: x))
    have b0 := cubeCount_le k (fun x => f (false :: x))
    have b1 := cubeCount_le k (fun x => f (true :: x))
    have d0 := cubeCount_compare k (fun x => f (false :: x)) (fun x => f (true :: x))
    have d1 := cubeCount_compare k (fun x => f (true :: x)) (fun x => f (false :: x))
    rw [cubeDisagree_comm k (fun x => f (true :: x)) (fun x => f (false :: x))] at d1
    simp only [cubeBoundary, cubeCount, pow_succ]
    omega

end PriorRoutes
