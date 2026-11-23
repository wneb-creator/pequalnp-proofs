import Mathlib

namespace PEqualNP.Outside.FP3Strategy

variable {S I : Type*}

def replay (step : S → I → S) (initial : S) (stream : ℕ → I) : ℕ → S
  | 0 => initial
  | t + 1 => step (replay step initial stream t) (stream t)

lemma replay_split (step : S → I → S) (initial : S) (stream : ℕ → I) (a b : ℕ) :
    replay step initial stream (a + b) =
      replay step (replay step initial stream a) (fun j => stream (a + j)) b := by
  induction b with
  | zero => simp [replay]
  | succ b ih => simp [replay, ih]

def CheckpointReplay (step : S → I → S) (initial : S) (stream : ℕ → I)
    (checkpoint : ℕ → S) (B R : ℕ) : Prop :=
  checkpoint 0 = initial ∧ ∀ r : ℕ, r < R →
    checkpoint (r + 1) = replay step (checkpoint r) (fun j => stream (r * B + j)) B

lemma checkpoints_exact (step : S → I → S) (initial : S) (stream : ℕ → I)
    (checkpoint : ℕ → S) (B R : ℕ)
    (h : CheckpointReplay step initial stream checkpoint B R) :
    ∀ r : ℕ, r ≤ R → checkpoint r = replay step initial stream (r * B) := by
  intro r
  induction r with
  | zero => intro _; simpa [replay] using h.1
  | succ r ih =>
    intro hr
    rw [h.2 r (by omega), ih (by omega), Nat.add_mul, one_mul, replay_split]

lemma checkpoint_query_exact (step : S → I → S) (initial : S) (stream : ℕ → I)
    (checkpoint : ℕ → S) (B R : ℕ) (hB : 0 < B)
    (h : CheckpointReplay step initial stream checkpoint B R) (t : ℕ) (ht : t ≤ R * B) :
    replay step (checkpoint (t / B)) (fun j => stream (t / B * B + j)) (t % B) =
      replay step initial stream t := by
  have hq : t / B ≤ R := by
    apply Nat.le_of_mul_le_mul_right _ hB
    exact (Nat.div_mul_le_self t B).trans ht
  rw [checkpoints_exact step initial stream checkpoint B R h (t / B) hq, ← replay_split]
  congr 1
  simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div t B

lemma block_checks_glue (step : S → I → S) (initial : S) (stream : ℕ → I)
    (checkpoint : ℕ → S) (B R : ℕ) (hB : 0 < B)
    (h : CheckpointReplay step initial stream checkpoint B R)
    (valid : S → I → Prop)
    (hblocks : ∀ r : ℕ, r < R → ∀ j : ℕ, j < B →
      valid (replay step (checkpoint r) (fun k => stream (r * B + k)) j)
        (stream (r * B + j))) :
    ∀ t : ℕ, t < R * B → valid (replay step initial stream t) (stream t) := by
  intro t ht
  have hq : t / B < R := by
    by_contra hn
    have hmul := Nat.mul_le_mul_right B (show R ≤ t / B by omega)
    have hdiv := Nat.div_mul_le_self t B
    omega
  have hrem : t % B < B := Nat.mod_lt t hB
  have hlocal := hblocks (t / B) hq (t % B) hrem
  rw [checkpoint_query_exact step initial stream checkpoint B R hB h t ht.le] at hlocal
  have hsplit : t / B * B + t % B = t := by
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div t B
  simpa [hsplit] using hlocal

lemma replay_preserves_validity_by_blocks (step : S → I → S) (initial : S)
    (stream : ℕ → I) (B R : ℕ) (hB : 0 < B) (valid : S → I → Prop) :
    (∀ t : ℕ, t < R * B → valid (replay step initial stream t) (stream t)) ↔
      ∃ checkpoint : ℕ → S,
        CheckpointReplay step initial stream checkpoint B R ∧
        (∀ r : ℕ, r < R → ∀ j : ℕ, j < B →
          valid (replay step (checkpoint r) (fun k => stream (r * B + k)) j)
            (stream (r * B + j))) := by
  constructor
  · intro hall
    refine ⟨fun r => replay step initial stream (r * B), ?_, ?_⟩
    · refine ⟨by simp [replay], ?_⟩
      intro r _
      dsimp only
      rw [Nat.add_mul, one_mul, replay_split]
    · intro r hr j hj
      rw [← replay_split]
      apply hall
      nlinarith
  · rintro ⟨checkpoint, h, hblocks⟩
    exact block_checks_glue step initial stream checkpoint B R hB h valid hblocks

end PEqualNP.Outside.FP3Strategy
