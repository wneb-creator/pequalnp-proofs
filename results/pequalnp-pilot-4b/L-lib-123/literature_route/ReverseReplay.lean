import Mathlib

namespace PEqualNP.Outside.LiteratureRoute

variable {σ β : Type*}

/-- State-only replay does not retain the emitted symbols. -/
def generatorAdvance (step : σ → σ × β) : ℕ → σ → σ
  | 0, s => s
  | n + 1, s => generatorAdvance step n (step s).1

def generatorTrace (step : σ → σ × β) : ℕ → σ → List β
  | 0, _ => []
  | n + 1, s => (step s).2 :: generatorTrace step n (step s).1

lemma generatorTrace_add (step : σ → σ × β) (n m : ℕ) (s : σ) :
    generatorTrace step (n + m) s =
      generatorTrace step n s ++
        generatorTrace step m (generatorAdvance step n s) := by
  induction n generalizing s with
  | zero => simp [generatorTrace, generatorAdvance]
  | succ n ih => simp [Nat.succ_add, generatorTrace, generatorAdvance, ih]

def generatorCheckpoints (jump : σ → σ) : ℕ → σ → List σ
  | 0, _ => []
  | n + 1, s => s :: generatorCheckpoints jump n (jump s)

lemma generatorCheckpoints_length (jump : σ → σ) (n : ℕ) (s : σ) :
    (generatorCheckpoints jump n s).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [generatorCheckpoints, ih]

lemma generatorTrace_chunks (step : σ → σ × β) (n L : ℕ) (s : σ) :
    (generatorCheckpoints (generatorAdvance step L) n s).flatMap
      (generatorTrace step L) = generatorTrace step (n * L) s := by
  induction n generalizing s with
  | zero => simp [generatorCheckpoints, generatorTrace]
  | succ n ih =>
    rw [generatorCheckpoints, List.flatMap_cons, ih]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (generatorTrace_add step L (n * L) s).symm

lemma reverse_flatMap_eq {α γ : Type*} (xs : List α) (f : α → List γ) :
    (xs.flatMap f).reverse = xs.reverse.flatMap (fun a => (f a).reverse) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons, List.flatMap_append, ih]

/-- The semantic output of a fixed-depth reverse-output schedule. A streaming
implementation can store B checkpoints per level and emit a child interval
before visiting the next one. Materializing this Lean list itself is not a
small-space implementation, and no such machine bound is asserted here. -/
def reverseReplay (step : σ → σ × β) (B L : ℕ) : ℕ → σ → List β
  | 0, s => (generatorTrace step L s).reverse
  | d + 1, s =>
      ((generatorCheckpoints (generatorAdvance step (B ^ d * L)) B s).reverse).flatMap
        (reverseReplay step B L d)

theorem reverseReplay_correct (step : σ → σ × β) (B L d : ℕ) (s : σ) :
    reverseReplay step B L d s = (generatorTrace step (B ^ d * L) s).reverse := by
  induction d generalizing s with
  | zero => simp [reverseReplay]
  | succ d ih =>
    have hfun : reverseReplay step B L d =
        fun s => (generatorTrace step (B ^ d * L) s).reverse := funext ih
    rw [reverseReplay, hfun, ← reverse_flatMap_eq, generatorTrace_chunks]
    congr 2
    simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- Steps that do not emit a symbol are represented by none. Removing them
commutes with reversing the generated stream. -/
theorem reverseReplay_optional (step : σ → σ × Option β)
    (B L d : ℕ) (s : σ) :
    (reverseReplay step B L d s).filterMap id =
      ((generatorTrace step (B ^ d * L) s).filterMap id).reverse := by
  rw [reverseReplay_correct]
  simp

/-- An abstract replay budget, allowing a full pass to form checkpoints at
each non-base interval. The theorem below solves this recurrence; connecting
it to operational cost, copying and a concrete machine is a separate task. -/
def reverseReplaySteps (B L : ℕ) : ℕ → ℕ
  | 0 => L
  | d + 1 => B * (B ^ d * L) + B * reverseReplaySteps B L d

theorem reverseReplaySteps_exact (B L d : ℕ) :
    reverseReplaySteps B L d = (d + 1) * (B ^ d * L) := by
  induction d with
  | zero => simp [reverseReplaySteps]
  | succ d ih =>
    rw [reverseReplaySteps, ih, Nat.pow_succ]
    ring

end PEqualNP.Outside.LiteratureRoute
