import Mathlib

namespace PEqualNP.Outside.PrefixReplay

variable {Q K A : Type*} [DecidableEq K]

abbrev Primitive (Q K A : Type*) := Q ⊕ (((K × A) × Q) ⊕ (K × (Option A → Q)))

def step (code : Q → Option (Primitive Q K A))
    (cfg : Q × (K → List A)) : Q × (K → List A) :=
  match code cfg.1 with
  | none => cfg
  | some (.inl q) => (q, cfg.2)
  | some (.inr (.inl ((k, a), q))) => (q, Function.update cfg.2 k (a :: cfg.2 k))
  | some (.inr (.inr (k, next))) =>
      (next ((cfg.2 k).head?), Function.update cfg.2 k ((cfg.2 k).tail))

def PrefixEq (n : ℕ) (a b : Q × (K → List A)) : Prop :=
  a.1 = b.1 ∧ ∀ k, (a.2 k).take n = (b.2 k).take n

lemma take_weaken {a b : List A} {n m : ℕ} (hnm : n ≤ m)
    (h : a.take m = b.take m) : a.take n = b.take n := by
  have ht := congrArg (List.take n) h
  simpa [List.take_take, Nat.min_eq_left hnm] using ht

lemma take_head {a b : List A} {n : ℕ}
    (h : a.take (n + 1) = b.take (n + 1)) : a.head? = b.head? := by
  cases a <;> cases b <;> simp_all

lemma take_tail {a b : List A} {n : ℕ}
    (h : a.take (n + 1) = b.take (n + 1)) : a.tail.take n = b.tail.take n := by
  cases a <;> cases b <;> simp_all

lemma take_push {a b : List A} {n : ℕ} (symbol : A)
    (h : a.take (n + 1) = b.take (n + 1)) :
    (symbol :: a).take n = (symbol :: b).take n := by
  cases n with
  | zero => simp
  | succ n =>
      have ht : a.take n = b.take n := take_weaken (by omega) h
      simpa using congrArg (List.cons symbol) ht

lemma step_prefix (code : Q → Option (Primitive Q K A)) (n : ℕ)
    (a b : Q × (K → List A)) (h : PrefixEq (n + 1) a b) :
    PrefixEq n (step code a) (step code b) := by
  rcases a with ⟨q, s⟩
  rcases b with ⟨q', s'⟩
  obtain ⟨hq, hs⟩ := h
  change q = q' at hq
  subst q'
  cases hc : code q with
  | none =>
      exact ⟨by simp [step, hc], fun k => by
        simpa [step, hc] using take_weaken (by omega : n ≤ n + 1) (hs k)⟩
  | some op =>
      rcases op with next | op
      · exact ⟨by simp [step, hc], fun k => by
          simpa [step, hc] using take_weaken (by omega : n ≤ n + 1) (hs k)⟩
      rcases op with ⟨⟨k, symbol⟩, next⟩ | ⟨k, next⟩
      · refine ⟨by simp [step, hc], ?_⟩
        intro j
        by_cases hj : j = k
        · subst j
          simpa [step, hc] using take_push symbol (hs k)
        · simpa [step, hc, hj] using take_weaken (by omega : n ≤ n + 1) (hs j)
      · refine ⟨?_, ?_⟩
        · simpa [step, hc] using congrArg next (take_head (hs k))
        · intro j
          by_cases hj : j = k
          · subst j
            simpa [step, hc] using take_tail (hs k)
          · simpa [step, hc, hj] using take_weaken (by omega : n ≤ n + 1) (hs j)

lemma iterate_prefix (code : Q → Option (Primitive Q K A)) (n m : ℕ)
    (a b : Q × (K → List A)) (h : PrefixEq (n + m) a b) :
    PrefixEq m ((step code)^[n] a) ((step code)^[n] b) := by
  induction n generalizing a b with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      apply ih
      apply step_prefix
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma truncated_initial_control (code : Q → Option (Primitive Q K A)) (n : ℕ)
    (q : Q) (initialStacks : K → List A) :
    ((step code)^[n] (q, initialStacks)).1 =
      ((step code)^[n] (q, fun k => (initialStacks k).take n)).1 := by
  exact (iterate_prefix code n 0 (q, initialStacks) (q, fun k => (initialStacks k).take n)
    ⟨rfl, fun k => by simp⟩).1

lemma truncated_initial_observations (code : Q → Option (Primitive Q K A))
    (n t : ℕ) (ht : t < n) (q : Q) (initialStacks : K → List A) :
    ((step code)^[t] (q, initialStacks)).1 =
        ((step code)^[t] (q, fun k => (initialStacks k).take n)).1 ∧
      ∀ k, (((step code)^[t] (q, initialStacks)).2 k).head? =
        (((step code)^[t] (q, fun k => (initialStacks k).take n)).2 k).head? := by
  have hinit : PrefixEq (t + 1) (q, initialStacks)
      (q, fun k => (initialStacks k).take n) := by
    refine ⟨rfl, fun k => ?_⟩
    simp [List.take_take, Nat.min_eq_left (show t + 1 ≤ n by omega)]
  have hrun := iterate_prefix code t 1 _ _ hinit
  exact ⟨hrun.1, fun k => take_head (n := 0) (hrun.2 k)⟩

end PEqualNP.Outside.PrefixReplay
