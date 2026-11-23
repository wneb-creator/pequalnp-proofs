import Mathlib

namespace PEqualNP.Outside.FP3Strategy

variable {α : Type*}

def nextStack (op : Option (Bool × α)) (s : List α) : List α :=
  match op with
  | none => s
  | some (true, b) => b :: s
  | some (false, _) => s.tail

def traceStack (ops : ℕ → Option (Bool × α)) : ℕ → List α
  | 0 => []
  | t + 1 => nextStack (ops t) (traceStack ops t)

lemma traceStack_length_le (ops : ℕ → Option (Bool × α)) (t : ℕ) :
    (traceStack ops t).length ≤ t := by
  induction t with
  | zero => simp [traceStack]
  | succ t ih =>
    cases hop : ops t with
    | none => simp [traceStack, nextStack, hop]; omega
    | some pair =>
      rcases pair with ⟨flag, b⟩
      cases flag <;> simp [traceStack, nextStack, hop] <;> omega

def StackStep (op : Option (Bool × α)) (s s' : List α) : Prop :=
  match op with
  | none => s' = s
  | some (true, b) => s' = b :: s
  | some (false, b) => s = b :: s'

def LocalStackTrace (ops : ℕ → Option (Bool × α)) (height mate : ℕ → ℕ)
    (T : ℕ) : Prop :=
  height 0 = 0 ∧ ∀ t : ℕ, t < T →
    match ops t with
    | none => height (t + 1) = height t
    | some (true, _) => height (t + 1) = height t + 1
    | some (false, b) =>
      height t = height (t + 1) + 1 ∧
      mate t < t ∧ ops (mate t) = some (true, b) ∧
      height (mate t) = height (t + 1) ∧
      ∀ k : ℕ, mate t < k → k ≤ t → height (mate t) < height k

def LegalStackTrace (ops : ℕ → Option (Bool × α)) (T : ℕ) : Prop :=
  ∀ t : ℕ, t < T → StackStep (ops t) (traceStack ops t) (traceStack ops (t + 1))

lemma suffix_nextStack {base s : List α} (op : Option (Bool × α))
    (hs : base <:+ s) (hlen : base.length ≤ (nextStack op s).length) :
    base <:+ nextStack op s := by
  obtain ⟨p, rfl⟩ := hs
  cases op with
  | none => exact ⟨p, rfl⟩
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag with
    | false =>
      cases p with
      | nil =>
        cases base with
        | nil => simp [nextStack]
        | cons a base => simp [nextStack] at hlen
      | cons a p => exact ⟨p, rfl⟩
    | true => exact ⟨b :: p, rfl⟩

lemma suffix_traceStack_later (ops : ℕ → Option (Bool × α))
    (base : List α) (i j : ℕ) (hij : i ≤ j)
    (hstart : base <:+ traceStack ops i)
    (hfloor : ∀ k : ℕ, i ≤ k → k ≤ j → base.length ≤ (traceStack ops k).length) :
    base <:+ traceStack ops j := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    simpa [hi] using hstart
  | succ j ih =>
    by_cases hle : i ≤ j
    · apply suffix_nextStack
      · exact ih i hle hstart (fun k hk hkj => hfloor k hk (by omega))
      · exact hfloor (j + 1) hij (by omega)
    · have hi : i = j + 1 := by omega
      simpa [hi] using hstart

lemma local_trace_height (ops : ℕ → Option (Bool × α)) (height mate : ℕ → ℕ)
    (T : ℕ) (hlocal : LocalStackTrace ops height mate T) :
    ∀ t : ℕ, t ≤ T → (traceStack ops t).length = height t := by
  obtain ⟨hzero, hstep⟩ := hlocal
  intro t
  induction t with
  | zero => intro _; simpa [traceStack] using hzero.symm
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hnow := hstep t (by omega)
    cases hop : ops t with
    | none =>
      simp only [hop] at hnow
      simpa [hop, traceStack, nextStack, hprev] using hnow.symm
    | some pair =>
      rcases pair with ⟨flag, b⟩
      cases flag with
      | false =>
        simp only [hop] at hnow
        simp only [traceStack, hop, nextStack, List.length_tail, hprev]
        omega
      | true =>
        simp only [hop] at hnow
        simpa [hop, traceStack, nextStack, hprev] using hnow.symm

lemma local_stack_trace_sound (ops : ℕ → Option (Bool × α)) (height mate : ℕ → ℕ)
    (T : ℕ) (hlocal : LocalStackTrace ops height mate T) : LegalStackTrace ops T := by
  intro t ht
  have hlen := local_trace_height ops height mate T hlocal
  have hnow := hlocal.2 t ht
  cases hop : ops t with
  | none => simp [StackStep, traceStack, nextStack, hop]
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag with
    | true => simp [StackStep, traceStack, nextStack, hop]
    | false =>
      simp only [hop] at hnow
      obtain ⟨hpop, hmate, hpush, hdepth, hbetween⟩ := hnow
      have hstart : b :: traceStack ops (mate t) <:+ traceStack ops (mate t + 1) := by
        simp [traceStack, nextStack, hpush]
      have hfloor : ∀ k : ℕ, mate t + 1 ≤ k → k ≤ t →
          (b :: traceStack ops (mate t)).length ≤ (traceStack ops k).length := by
        intro k hk hkt
        have hstrict := hbetween k (by omega) hkt
        rw [List.length_cons, hlen (mate t) (by omega), hlen k (by omega)]
        omega
      have hsuffix := suffix_traceStack_later ops (b :: traceStack ops (mate t))
        (mate t + 1) t (by omega) hstart hfloor
      have heqlen : (b :: traceStack ops (mate t)).length = (traceStack ops t).length := by
        rw [List.length_cons, hlen (mate t) (by omega), hlen t (by omega)]
        omega
      have heq : traceStack ops t = b :: traceStack ops (mate t) :=
        (hsuffix.eq_of_length heqlen).symm
      simp [StackStep, traceStack, nextStack, hop, heq]

lemma traceStack_matching_push (ops : ℕ → Option (Bool × α)) (t : ℕ)
    (b : α) (tail : List α) (hhead : traceStack ops t = b :: tail) :
    let j := Nat.findGreatest (fun k => (traceStack ops k).length ≤ tail.length) t
    j < t ∧ ops j = some (true, b) ∧ (traceStack ops j).length = tail.length ∧
      ∀ k : ℕ, j < k → k ≤ t → (traceStack ops j).length < (traceStack ops k).length := by
  let j := Nat.findGreatest (fun k => (traceStack ops k).length ≤ tail.length) t
  change j < t ∧ _
  have hjle : j ≤ t := Nat.findGreatest_le t
  have hjlen : (traceStack ops j).length ≤ tail.length :=
    Nat.findGreatest_spec (P := fun k => (traceStack ops k).length ≤ tail.length)
      (m := 0) (Nat.zero_le t) (by simp [traceStack])
  have htlen : (traceStack ops t).length = tail.length + 1 := by simp [hhead]
  have hjt : j < t := by
    by_contra hn
    have hj : j = t := by omega
    rw [hj] at hjlen
    omega
  have hafter : ∀ k : ℕ, j < k → k ≤ t → tail.length < (traceStack ops k).length := by
    intro k hjk hkt
    exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
      (P := fun k => (traceStack ops k).length ≤ tail.length) hjk hkt)
  have hjnext := hafter (j + 1) (by omega) (by omega)
  cases hop : ops j with
  | none =>
    simp [traceStack, nextStack, hop] at hjnext
    omega
  | some pair =>
    rcases pair with ⟨flag, c⟩
    cases flag with
    | false =>
      simp [traceStack, nextStack, hop] at hjnext
      omega
    | true =>
      have hjdepth : (traceStack ops j).length = tail.length := by
        simp [traceStack, nextStack, hop] at hjnext
        omega
      have hstart : c :: traceStack ops j <:+ traceStack ops (j + 1) := by
        simp [traceStack, nextStack, hop]
      have hsuffix := suffix_traceStack_later ops (c :: traceStack ops j) (j + 1) t
        (by omega) hstart (by
          intro k hjk hkt
          have hklen := hafter k (by omega) hkt
          simp only [List.length_cons, hjdepth]
          omega)
      have heqlen : (c :: traceStack ops j).length = (traceStack ops t).length := by
        simp [hjdepth, htlen]
      have heq : c :: traceStack ops j = traceStack ops t := hsuffix.eq_of_length heqlen
      have hcb : c = b := (List.cons.inj (heq.trans hhead)).1
      subst c
      refine ⟨hjt, rfl, hjdepth, ?_⟩
      intro k hjk hkt
      rw [hjdepth]
      exact hafter k hjk hkt

lemma local_stack_trace_complete (ops : ℕ → Option (Bool × α)) (T : ℕ)
    (hlegal : LegalStackTrace ops T) :
    ∃ height mate : ℕ → ℕ, LocalStackTrace ops height mate T := by
  refine ⟨fun t => (traceStack ops t).length,
    fun t => Nat.findGreatest
      (fun k => (traceStack ops k).length ≤ (traceStack ops (t + 1)).length) t, ?_⟩
  refine ⟨rfl, ?_⟩
  intro t ht
  cases hop : ops t with
  | none => simp [traceStack, nextStack, hop]
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag with
    | true => simp [traceStack, nextStack, hop]
    | false =>
      have hstep := hlegal t ht
      simp only [StackStep, hop] at hstep
      have hmatch := traceStack_matching_push ops t b (traceStack ops (t + 1)) hstep
      refine ⟨?_, hmatch⟩
      simpa using congrArg List.length hstep

lemma local_stack_trace_iff (ops : ℕ → Option (Bool × α)) (T : ℕ) :
    LegalStackTrace ops T ↔ ∃ height mate : ℕ → ℕ, LocalStackTrace ops height mate T := by
  constructor
  · exact local_stack_trace_complete ops T
  · rintro ⟨height, mate, h⟩
    exact local_stack_trace_sound ops height mate T h

lemma local_trace_height_le (ops : ℕ → Option (Bool × α)) (height mate : ℕ → ℕ)
    (T : ℕ) (hlocal : LocalStackTrace ops height mate T) (t : ℕ) (ht : t ≤ T) :
    height t ≤ t := by
  rw [← local_trace_height ops height mate T hlocal t ht]
  exact traceStack_length_le ops t

lemma local_multistack_trace_iff {ι : Type*} {Γ : ι → Type*}
    (ops : (i : ι) → ℕ → Option (Bool × Γ i)) (T : ℕ) :
    (∀ i : ι, LegalStackTrace (ops i) T) ↔
      ∃ height mate : ι → ℕ → ℕ, ∀ i : ι, LocalStackTrace (ops i) (height i) (mate i) T := by
  constructor
  · intro h
    choose height mate hlocal using fun i => local_stack_trace_complete (ops i) T (h i)
    exact ⟨height, mate, hlocal⟩
  · rintro ⟨height, mate, hlocal⟩ i
    exact local_stack_trace_sound (ops i) (height i) (mate i) T (hlocal i)

def traceStackFrom (initial : List α) (ops : ℕ → Option (Bool × α)) : ℕ → List α
  | 0 => initial
  | t + 1 => nextStack (ops t) (traceStackFrom initial ops t)

def prependStack (initial : List α) (ops : ℕ → Option (Bool × α)) (t : ℕ) :
    Option (Bool × α) :=
  if ht : t < initial.length then
    some (true, initial.reverse.get ⟨t, by simpa using ht⟩)
  else ops (t - initial.length)

lemma traceStack_prepend_prefix (initial : List α) (ops : ℕ → Option (Bool × α)) :
    traceStack (prependStack initial ops) initial.length = initial := by
  have hprefix : ∀ t : ℕ, t ≤ initial.length →
      traceStack (prependStack initial ops) t = (initial.reverse.take t).reverse := by
    intro t
    induction t with
    | zero => intro _; simp [traceStack]
    | succ t ih =>
      intro ht
      have hlt : t < initial.length := by omega
      have htake := List.take_concat_get' initial.reverse t (by simpa using hlt)
      simpa [traceStack, prependStack, hlt, nextStack, ih (by omega)] using
        congrArg List.reverse htake
  have htake : initial.reverse.length ≤ initial.length := by simp
  simpa [List.take_of_length_le htake] using hprefix initial.length le_rfl

lemma traceStack_after_prepend (initial : List α) (ops : ℕ → Option (Bool × α)) (t : ℕ) :
    traceStack (prependStack initial ops) (initial.length + t) = traceStackFrom initial ops t := by
  induction t with
  | zero => simpa [traceStackFrom] using traceStack_prepend_prefix initial ops
  | succ t ih =>
    have hn : ¬ initial.length + t < initial.length := by omega
    simp [traceStack, traceStackFrom, prependStack, hn, ih]

def LegalStackTraceFrom (initial : List α) (ops : ℕ → Option (Bool × α)) (T : ℕ) : Prop :=
  ∀ t : ℕ, t < T →
    StackStep (ops t) (traceStackFrom initial ops t) (traceStackFrom initial ops (t + 1))

lemma legal_stack_prepend_iff (initial : List α) (ops : ℕ → Option (Bool × α)) (T : ℕ) :
    LegalStackTrace (prependStack initial ops) (initial.length + T) ↔
      LegalStackTraceFrom initial ops T := by
  constructor
  · intro h t ht
    have hh := h (initial.length + t) (by omega)
    have hn : ¬ initial.length + t < initial.length := by omega
    simpa [Nat.add_assoc, prependStack, hn, traceStack_after_prepend] using hh
  · intro h t ht
    by_cases hpre : t < initial.length
    · simp [StackStep, traceStack, prependStack, hpre, nextStack]
    · let j := t - initial.length
      have hteq : t = initial.length + j := by omega
      have hj : j < T := by omega
      have hn : ¬ initial.length + j < initial.length := by omega
      rw [hteq]
      simpa [Nat.add_assoc, prependStack, hn, traceStack_after_prepend] using h j hj

lemma local_stack_trace_from_iff (initial : List α) (ops : ℕ → Option (Bool × α)) (T : ℕ) :
    LegalStackTraceFrom initial ops T ↔
      ∃ height mate : ℕ → ℕ,
        LocalStackTrace (prependStack initial ops) height mate (initial.length + T) := by
  rw [← legal_stack_prepend_iff, local_stack_trace_iff]

def StackPointCheck (ops : ℕ → Option (Bool × α)) (height mate : ℕ → ℕ) (t k : ℕ) : Prop :=
  match ops t with
  | none => height (t + 1) = height t
  | some (true, _) => height (t + 1) = height t + 1
  | some (false, b) =>
    height t = height (t + 1) + 1 ∧
    mate t < t ∧ ops (mate t) = some (true, b) ∧
    height (mate t) = height (t + 1) ∧
    (mate t < k → k ≤ t → height (mate t) < height k)

lemma local_stack_trace_pointwise_iff (ops : ℕ → Option (Bool × α))
    (height mate : ℕ → ℕ) (T : ℕ) :
    LocalStackTrace ops height mate T ↔
      height 0 = 0 ∧ ∀ t : ℕ, t < T → ∀ k : ℕ, k ≤ T → StackPointCheck ops height mate t k := by
  constructor
  · rintro ⟨hzero, hlocal⟩
    refine ⟨hzero, ?_⟩
    intro t ht k _
    have h := hlocal t ht
    cases hop : ops t with
    | none => simpa [StackPointCheck, hop] using h
    | some pair =>
      rcases pair with ⟨flag, b⟩
      cases flag with
      | true => simpa [StackPointCheck, hop] using h
      | false =>
        simp only [hop] at h
        simp only [StackPointCheck, hop]
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2 k⟩
  · rintro ⟨hzero, hpoint⟩
    refine ⟨hzero, ?_⟩
    intro t ht
    have h := hpoint t ht 0 (Nat.zero_le T)
    cases hop : ops t with
    | none => simpa [StackPointCheck, hop] using h
    | some pair =>
      rcases pair with ⟨flag, b⟩
      cases flag with
      | true => simpa [StackPointCheck, hop] using h
      | false =>
        simp only [StackPointCheck, hop] at h
        refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
        intro k hjk hkt
        have hk := hpoint t ht k (by omega)
        simp only [StackPointCheck, hop] at hk
        exact hk.2.2.2.2 hjk hkt

lemma local_multistack_trace_from_iff {ι : Type*} {Γ : ι → Type*}
    (initial : (i : ι) → List (Γ i)) (ops : (i : ι) → ℕ → Option (Bool × Γ i)) (T : ℕ) :
    (∀ i : ι, LegalStackTraceFrom (initial i) (ops i) T) ↔
      ∃ height mate : ι → ℕ → ℕ, ∀ i : ι,
        LocalStackTrace (prependStack (initial i) (ops i)) (height i) (mate i)
          ((initial i).length + T) := by
  constructor
  · intro h
    choose height mate hlocal using fun i =>
      (local_stack_trace_from_iff (initial i) (ops i) T).mp (h i)
    exact ⟨height, mate, hlocal⟩
  · rintro ⟨height, mate, hlocal⟩ i
    exact (local_stack_trace_from_iff (initial i) (ops i) T).mpr
      ⟨height i, mate i, hlocal i⟩

lemma traceStackFrom_length_le (initial : List α) (ops : ℕ → Option (Bool × α)) (t : ℕ) :
    (traceStackFrom initial ops t).length ≤ initial.length + t := by
  rw [← traceStack_after_prepend]
  exact traceStack_length_le _ _

def normalizeMate (ops : ℕ → Option (Bool × α)) (mate : ℕ → ℕ) (t : ℕ) : ℕ :=
  match ops t with
  | some (false, _) => mate t
  | _ => 0

lemma local_stack_trace_normalizeMate (ops : ℕ → Option (Bool × α))
    (height mate : ℕ → ℕ) (T : ℕ) (hlocal : LocalStackTrace ops height mate T) :
    LocalStackTrace ops height (normalizeMate ops mate) T := by
  refine ⟨hlocal.1, ?_⟩
  intro t ht
  have h := hlocal.2 t ht
  cases hop : ops t with
  | none => simpa [hop] using h
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag <;> simpa [normalizeMate, hop] using h

lemma normalized_mate_le (ops : ℕ → Option (Bool × α)) (height mate : ℕ → ℕ)
    (T : ℕ) (hlocal : LocalStackTrace ops height mate T) (t : ℕ) (ht : t < T) :
    normalizeMate ops mate t ≤ t := by
  have h := hlocal.2 t ht
  cases hop : ops t with
  | none => simp [normalizeMate, hop]
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag with
    | true => simp [normalizeMate, hop]
    | false =>
      simp only [hop] at h
      simpa [normalizeMate, hop] using h.2.1.le

lemma local_stack_trace_complete_bounded (ops : ℕ → Option (Bool × α)) (T : ℕ)
    (hlegal : LegalStackTrace ops T) :
    ∃ height mate : ℕ → ℕ, LocalStackTrace ops height mate T ∧
      (∀ t : ℕ, t ≤ T → height t ≤ t) ∧ (∀ t : ℕ, t < T → mate t ≤ t) := by
  obtain ⟨height, mate, hlocal⟩ := local_stack_trace_complete ops T hlegal
  refine ⟨height, normalizeMate ops mate, local_stack_trace_normalizeMate ops height mate T hlocal,
    ?_, ?_⟩
  · exact fun t ht => local_trace_height_le ops height mate T hlocal t ht
  · exact fun t ht => normalized_mate_le ops height mate T hlocal t ht

end PEqualNP.Outside.FP3Strategy
namespace PEqualNP.Outside.FP3Strategy

variable {α : Type*}

def StackChallenge (ops : ℕ → Option (Bool × α)) (height : ℕ → ℕ) (t j k : ℕ) : Prop :=
  match ops t with
  | none => height (t + 1) = height t
  | some (true, _) => height (t + 1) = height t + 1
  | some (false, b) =>
    height t = height (t + 1) + 1 ∧
      (t ≤ j ∨ height j ≠ height (t + 1) ∨ ops j = some (true, b) ∨
        (j < k ∧ k ≤ t ∧ height k ≤ height j))

def ChallengeStackTrace (ops : ℕ → Option (Bool × α)) (height : ℕ → ℕ) (T : ℕ) : Prop :=
  height 0 = 0 ∧ ∀ t : ℕ, t < T → ∀ j : ℕ, j ≤ T →
    ∃ k : ℕ, k ≤ T ∧ StackChallenge ops height t j k

lemma local_to_challenge_stack_trace (ops : ℕ → Option (Bool × α))
    (height mate : ℕ → ℕ) (T : ℕ) (hlocal : LocalStackTrace ops height mate T) :
    ChallengeStackTrace ops height T := by
  refine ⟨hlocal.1, ?_⟩
  intro t ht j _
  have h := hlocal.2 t ht
  cases hop : ops t with
  | none =>
    refine ⟨0, Nat.zero_le T, ?_⟩
    simpa [StackChallenge, hop] using h
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag with
    | true =>
      refine ⟨0, Nat.zero_le T, ?_⟩
      simpa [StackChallenge, hop] using h
    | false =>
      simp only [hop] at h
      obtain ⟨hpop, hmate, hpush, hdepth, hbetween⟩ := h
      by_cases hjt : t ≤ j
      · refine ⟨0, Nat.zero_le T, ?_⟩
        simp only [StackChallenge, hop]
        exact ⟨hpop, Or.inl hjt⟩
      · by_cases hjdepth : height j = height (t + 1)
        · have hjmate : j ≤ mate t := by
            by_contra hn
            have hstrict := hbetween j (by omega) (by omega)
            omega
          rcases lt_or_eq_of_le hjmate with hjm | hjm
          · refine ⟨mate t, by omega, ?_⟩
            simp only [StackChallenge, hop]
            exact ⟨hpop, Or.inr (Or.inr (Or.inr ⟨hjm, hmate.le, by omega⟩))⟩
          · refine ⟨0, Nat.zero_le T, ?_⟩
            simp only [StackChallenge, hop]
            exact ⟨hpop, Or.inr (Or.inr (Or.inl (by simpa [hjm] using hpush)))⟩
        · refine ⟨0, Nat.zero_le T, ?_⟩
          simp only [StackChallenge, hop]
          exact ⟨hpop, Or.inr (Or.inl hjdepth)⟩

lemma challenge_to_local_stack_trace (ops : ℕ → Option (Bool × α))
    (height : ℕ → ℕ) (T : ℕ) (hchallenge : ChallengeStackTrace ops height T) :
    ∃ mate : ℕ → ℕ, LocalStackTrace ops height mate T := by
  have hinc : ∀ t : ℕ, t < T → height (t + 1) ≤ height t + 1 := by
    intro t ht
    obtain ⟨k, _, h⟩ := hchallenge.2 t ht 0 (Nat.zero_le T)
    cases hop : ops t with
    | none => simp only [StackChallenge, hop] at h; omega
    | some pair =>
      rcases pair with ⟨flag, b⟩
      cases flag <;> simp only [StackChallenge, hop] at h <;> omega
  let mate := fun t => Nat.findGreatest (fun k => height k ≤ height (t + 1)) t
  refine ⟨mate, hchallenge.1, ?_⟩
  intro t ht
  obtain ⟨k₀, _, hbase⟩ := hchallenge.2 t ht 0 (Nat.zero_le T)
  cases hop : ops t with
  | none => simpa [StackChallenge, hop] using hbase
  | some pair =>
    rcases pair with ⟨flag, b⟩
    cases flag with
    | true => simpa [StackChallenge, hop] using hbase
    | false =>
      simp only [StackChallenge, hop] at hbase
      have hpop := hbase.1
      let j := mate t
      have hjle : j ≤ t := Nat.findGreatest_le t
      have hjheight : height j ≤ height (t + 1) :=
        Nat.findGreatest_spec (P := fun k => height k ≤ height (t + 1))
          (m := 0) (Nat.zero_le t) (by rw [hchallenge.1]; omega)
      have hjt : j < t := by
        by_contra hn
        have heq : j = t := by omega
        rw [heq] at hjheight
        omega
      have hafter : ∀ k : ℕ, j < k → k ≤ t → height (t + 1) < height k := by
        intro k hjk hkt
        exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
          (P := fun k => height k ≤ height (t + 1)) hjk hkt)
      have hjnext := hafter (j + 1) (by omega) (by omega)
      have hjinc := hinc j (by omega)
      have hjdepth : height j = height (t + 1) := by omega
      obtain ⟨k, _, hcheck⟩ := hchallenge.2 t ht j (by omega)
      simp only [StackChallenge, hop] at hcheck
      have hpush : ops j = some (true, b) := by
        rcases hcheck.2 with hlate | hwrong | hpush | ⟨hjk, hkt, hlow⟩
        · omega
        · exact False.elim (hwrong hjdepth)
        · exact hpush
        · have hstrict := hafter k hjk hkt
          omega
      change height t = height (t + 1) + 1 ∧ j < t ∧ ops j = some (true, b) ∧
        height j = height (t + 1) ∧ ∀ k : ℕ, j < k → k ≤ t → height j < height k
      refine ⟨hpop, hjt, hpush, hjdepth, ?_⟩
      intro k hjk hkt
      rw [hjdepth]
      exact hafter k hjk hkt

lemma local_challenge_stack_trace_iff (ops : ℕ → Option (Bool × α))
    (height : ℕ → ℕ) (T : ℕ) :
    (∃ mate : ℕ → ℕ, LocalStackTrace ops height mate T) ↔
      ChallengeStackTrace ops height T := by
  constructor
  · rintro ⟨mate, hlocal⟩
    exact local_to_challenge_stack_trace ops height mate T hlocal
  · exact challenge_to_local_stack_trace ops height T

lemma legal_challenge_stack_trace_iff (ops : ℕ → Option (Bool × α)) (T : ℕ) :
    LegalStackTrace ops T ↔ ∃ height : ℕ → ℕ, ChallengeStackTrace ops height T := by
  rw [local_stack_trace_iff]
  constructor
  · rintro ⟨height, mate, hlocal⟩
    exact ⟨height, local_to_challenge_stack_trace ops height mate T hlocal⟩
  · rintro ⟨height, hchallenge⟩
    obtain ⟨mate, hlocal⟩ := challenge_to_local_stack_trace ops height T hchallenge
    exact ⟨height, mate, hlocal⟩

lemma legal_challenge_stack_from_iff (initial : List α)
    (ops : ℕ → Option (Bool × α)) (T : ℕ) :
    LegalStackTraceFrom initial ops T ↔ ∃ height : ℕ → ℕ,
      ChallengeStackTrace (prependStack initial ops) height (initial.length + T) := by
  rw [← legal_stack_prepend_iff, legal_challenge_stack_trace_iff]

lemma legal_challenge_multistack_from_iff {ι : Type*} {Γ : ι → Type*}
    (initial : (i : ι) → List (Γ i)) (ops : (i : ι) → ℕ → Option (Bool × Γ i)) (T : ℕ) :
    (∀ i : ι, LegalStackTraceFrom (initial i) (ops i) T) ↔
      ∃ height : ι → ℕ → ℕ, ∀ i : ι,
        ChallengeStackTrace (prependStack (initial i) (ops i)) (height i)
          ((initial i).length + T) := by
  constructor
  · intro h
    choose height hcert using fun i =>
      (legal_challenge_stack_from_iff (initial i) (ops i) T).mp (h i)
    exact ⟨height, hcert⟩
  · rintro ⟨height, hcert⟩ i
    exact (legal_challenge_stack_from_iff (initial i) (ops i) T).mpr ⟨height i, hcert i⟩

lemma challenge_stack_height_from (initial : List α) (ops : ℕ → Option (Bool × α))
    (height : ℕ → ℕ) (T : ℕ)
    (hchallenge : ChallengeStackTrace (prependStack initial ops) height (initial.length + T))
    (t : ℕ) (ht : t ≤ T) :
    (traceStackFrom initial ops t).length = height (initial.length + t) := by
  obtain ⟨mate, hlocal⟩ := challenge_to_local_stack_trace
    (prependStack initial ops) height (initial.length + T) hchallenge
  have hlen := local_trace_height (prependStack initial ops) height mate
    (initial.length + T) hlocal (initial.length + t) (by omega)
  simpa [traceStack_after_prepend] using hlen

lemma challenge_stack_height_le (ops : ℕ → Option (Bool × α)) (height : ℕ → ℕ)
    (T : ℕ) (hchallenge : ChallengeStackTrace ops height T) (t : ℕ) (ht : t ≤ T) :
    height t ≤ t := by
  obtain ⟨mate, hlocal⟩ := challenge_to_local_stack_trace ops height T hchallenge
  exact local_trace_height_le ops height mate T hlocal t ht

end PEqualNP.Outside.FP3Strategy

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

abbrev Primitive (Q K A : Type*) :=
  Q ⊕ (((K × A) × Q) ⊕ (K × (Option A → Q)))

def singleOp (k : K) (op : Option (Bool × A)) : K → Option (Bool × A) :=
  Function.update (fun _ => none) k op

def primitiveStep (code : Q → Option (Primitive Q K A))
    (cfg : Q × (K → List A)) : Q × (K → List A) :=
  match code cfg.1 with
  | none => cfg
  | some (.inl q) => (q, cfg.2)
  | some (.inr (.inl ((k, a), q))) => (q, Function.update cfg.2 k (a :: cfg.2 k))
  | some (.inr (.inr (k, next))) =>
    (next ((cfg.2 k).head?), Function.update cfg.2 k ((cfg.2 k).tail))

def primitiveRun (code : Q → Option (Primitive Q K A))
    (initial : Q × (K → List A)) : ℕ → Q × (K → List A)
  | 0 => initial
  | t + 1 => primitiveStep code (primitiveRun code initial t)

def ControlCheck (code : Q → Option (Primitive Q K A)) (q q' : Q)
    (ops : K → Option (Bool × A)) (height : K → ℕ) : Prop :=
  match code q with
  | none => q' = q ∧ ops = fun _ => none
  | some (.inl next) => q' = next ∧ ops = fun _ => none
  | some (.inr (.inl ((k, a), next))) =>
    q' = next ∧ ops = singleOp k (some (true, a))
  | some (.inr (.inr (k, next))) =>
    (height k = 0 ∧ q' = next none ∧ ops = fun _ => none) ∨
      ∃ a : A, q' = next (some a) ∧ ops = singleOp k (some (false, a))

lemma stackStep_next {op : Option (Bool × A)} {s s' : List A}
    (h : StackStep op s s') : s' = nextStack op s := by
  cases op with
  | none => exact h
  | some pair =>
    obtain ⟨flag, a⟩ := pair
    cases flag with
    | true => exact h
    | false =>
      change s = a :: s' at h
      simp [nextStack, h]

omit [DecidableEq K] in
lemma stack_steps_none (s s' : K → List A)
    (h : ∀ k : K, StackStep none (s k) (s' k)) : s' = s := by
  funext k
  exact h k

lemma stack_steps_single (s s' : K → List A) (k : K) (op : Option (Bool × A))
    (h : ∀ i : K, StackStep (singleOp k op i) (s i) (s' i)) :
    s' = Function.update s k (nextStack op (s k)) := by
  funext i
  have hi := stackStep_next (h i)
  by_cases hik : i = k
  · subst i
    simpa [singleOp] using hi
  · simpa [singleOp, hik, nextStack] using hi

lemma primitive_transition_sound
    (code : Q → Option (Primitive Q K A)) (q q' : Q)
    (s s' : K → List A) (ops : K → Option (Bool × A)) (height : K → ℕ)
    (hlen : ∀ k : K, (s k).length = height k)
    (hstack : ∀ k : K, StackStep (ops k) (s k) (s' k))
    (hcontrol : ControlCheck code q q' ops height) :
    primitiveStep code (q, s) = (q', s') := by
  cases hc : code q with
  | none =>
    simp only [ControlCheck, hc] at hcontrol
    obtain ⟨rfl, rfl⟩ := hcontrol
    have hs := stack_steps_none s s' hstack
    simp [primitiveStep, hc, hs]
  | some instruction =>
    cases instruction with
    | inl next =>
      simp only [ControlCheck, hc] at hcontrol
      obtain ⟨rfl, rfl⟩ := hcontrol
      have hs := stack_steps_none s s' hstack
      simp [primitiveStep, hc, hs]
    | inr instruction =>
      cases instruction with
      | inl push =>
        obtain ⟨⟨k, a⟩, next⟩ := push
        simp only [ControlCheck, hc] at hcontrol
        obtain ⟨rfl, rfl⟩ := hcontrol
        have hs := stack_steps_single s s' k (some (true, a)) hstack
        simp [primitiveStep, hc, hs, nextStack]
      | inr pop =>
        obtain ⟨k, next⟩ := pop
        simp only [ControlCheck, hc] at hcontrol
        rcases hcontrol with ⟨hempty, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
        · have hs := stack_steps_none s s' hstack
          have hk : s k = [] := List.length_eq_zero_iff.mp ((hlen k).trans hempty)
          simp [primitiveStep, hc, hs, hk]
        · have hs := stack_steps_single s s' k (some (false, a)) hstack
          have hk := hstack k
          simp only [singleOp, Function.update_self] at hk
          change s k = a :: s' k at hk
          have hhead : (s k).head? = some a := by simp [hk]
          simp [primitiveStep, hc, hs, nextStack, hhead]

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

def primitiveOps (code : Q → Option (Primitive Q K A))
    (cfg : Q × (K → List A)) : K → Option (Bool × A) :=
  match code cfg.1 with
  | none => fun _ => none
  | some (.inl _) => fun _ => none
  | some (.inr (.inl ((k, a), _))) => singleOp k (some (true, a))
  | some (.inr (.inr (k, _))) =>
    match cfg.2 k with
    | [] => fun _ => none
    | a :: _ => singleOp k (some (false, a))

lemma primitive_step_records (code : Q → Option (Primitive Q K A))
    (cfg : Q × (K → List A)) :
    ControlCheck code cfg.1 (primitiveStep code cfg).1 (primitiveOps code cfg)
      (fun k => (cfg.2 k).length) ∧
    ∀ k : K, StackStep (primitiveOps code cfg k) (cfg.2 k) ((primitiveStep code cfg).2 k) := by
  obtain ⟨q, s⟩ := cfg
  cases hc : code q with
  | none => simp [primitiveStep, primitiveOps, ControlCheck, hc, StackStep]
  | some instruction =>
    cases instruction with
    | inl next => simp [primitiveStep, primitiveOps, ControlCheck, hc, StackStep]
    | inr instruction =>
      cases instruction with
      | inl push =>
        obtain ⟨⟨k, a⟩, next⟩ := push
        constructor
        · simp [primitiveStep, primitiveOps, ControlCheck, hc]
        · intro i
          by_cases hi : i = k
          · subst i; simp [primitiveStep, primitiveOps, hc, singleOp, StackStep]
          · simp [primitiveStep, primitiveOps, hc, singleOp, StackStep, hi]
      | inr pop =>
        obtain ⟨k, next⟩ := pop
        cases hs : s k with
        | nil =>
          constructor
          · simp [primitiveStep, primitiveOps, ControlCheck, hc, hs]
          · intro i
            by_cases hi : i = k
            · subst i; simp [primitiveStep, primitiveOps, hc, hs, StackStep]
            · simp [primitiveStep, primitiveOps, hc, hs, StackStep, hi]
        | cons a tail =>
          constructor
          · simp only [ControlCheck, hc]
            right
            refine ⟨a, ?_, ?_⟩ <;> simp [primitiveStep, primitiveOps, hc, hs]
          · intro i
            by_cases hi : i = k
            · subst i; simp [primitiveStep, primitiveOps, hc, hs, singleOp, StackStep]
            · simp [primitiveStep, primitiveOps, hc, hs, singleOp, StackStep, hi]

def traceStacks (initial : K → List A) (ops : K → ℕ → Option (Bool × A))
    (t : ℕ) : K → List A :=
  fun k => traceStackFrom (initial k) (ops k) t

def IndexedTraceCheck (code : Q → Option (Primitive Q K A))
    (q0 : Q) (initial : K → List A) (control : ℕ → Q)
    (ops : K → ℕ → Option (Bool × A)) (height mate : K → ℕ → ℕ) (T : ℕ) : Prop :=
  control 0 = q0 ∧
  (∀ k : K, LocalStackTrace (prependStack (initial k) (ops k))
    (height k) (mate k) ((initial k).length + T)) ∧
  ∀ t : ℕ, t < T → ControlCheck code (control t) (control (t + 1))
    (fun k => ops k t) (fun k => height k ((initial k).length + t))

lemma indexed_trace_heights
    (code : Q → Option (Primitive Q K A)) (q0 : Q) (initial : K → List A)
    (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height mate : K → ℕ → ℕ) (T : ℕ)
    (h : IndexedTraceCheck code q0 initial control ops height mate T)
    (t : ℕ) (ht : t ≤ T) (k : K) :
    (traceStacks initial ops t k).length = height k ((initial k).length + t) := by
  have hh := local_trace_height (prependStack (initial k) (ops k))
    (height k) (mate k) ((initial k).length + T) (h.2.1 k)
    ((initial k).length + t) (by omega)
  simpa [traceStack_after_prepend, traceStacks] using hh

lemma indexed_trace_sound
    (code : Q → Option (Primitive Q K A)) (q0 : Q) (initial : K → List A)
    (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height mate : K → ℕ → ℕ) (T : ℕ)
    (h : IndexedTraceCheck code q0 initial control ops height mate T) :
    ∀ t : ℕ, t ≤ T →
      primitiveRun code (q0, initial) t = (control t, traceStacks initial ops t) := by
  intro t
  induction t with
  | zero =>
    intro _
    change (q0, initial) = (control 0, initial)
    rw [h.1]
  | succ t ih =>
    intro ht
    rw [primitiveRun, ih (by omega)]
    apply primitive_transition_sound code (control t) (control (t + 1))
      (traceStacks initial ops t) (traceStacks initial ops (t + 1))
      (fun k => ops k t) (fun k => height k ((initial k).length + t))
    · exact indexed_trace_heights code q0 initial control ops height mate T h t (by omega)
    · intro k
      have hk := (local_stack_trace_from_iff (initial k) (ops k) T).mpr
        ⟨height k, mate k, h.2.1 k⟩
      exact hk t (by omega)
    · exact h.2.2 t (by omega)

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

def runOps (code : Q → Option (Primitive Q K A))
    (initial : Q × (K → List A)) (k : K) (t : ℕ) : Option (Bool × A) :=
  primitiveOps code (primitiveRun code initial t) k

lemma traceStacks_runOps (code : Q → Option (Primitive Q K A))
    (initial : Q × (K → List A)) (t : ℕ) :
    traceStacks initial.2 (runOps code initial) t = (primitiveRun code initial t).2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext k
    change nextStack (primitiveOps code (primitiveRun code initial t) k)
      (traceStacks initial.2 (runOps code initial) t k) =
        (primitiveStep code (primitiveRun code initial t)).2 k
    rw [ih]
    exact (stackStep_next ((primitive_step_records code (primitiveRun code initial t)).2 k)).symm

lemma indexed_trace_complete
    (code : Q → Option (Primitive Q K A)) (q0 : Q) (initial : K → List A) (T : ℕ) :
    ∃ height mate : K → ℕ → ℕ,
      IndexedTraceCheck code q0 initial
        (fun t => (primitiveRun code (q0, initial) t).1)
        (runOps code (q0, initial)) height mate T := by
  have hlegal : ∀ k : K,
      LegalStackTraceFrom (initial k) (runOps code (q0, initial) k) T := by
    intro k t ht
    change StackStep (primitiveOps code (primitiveRun code (q0, initial) t) k)
      (traceStacks initial (runOps code (q0, initial)) t k)
      (traceStacks initial (runOps code (q0, initial)) (t + 1) k)
    rw [traceStacks_runOps code (q0, initial) t,
      traceStacks_runOps code (q0, initial) (t + 1)]
    exact (primitive_step_records code (primitiveRun code (q0, initial) t)).2 k
  obtain ⟨height, mate, hlocal⟩ :=
    (local_multistack_trace_from_iff initial (runOps code (q0, initial)) T).mp hlegal
  refine ⟨height, mate, rfl, hlocal, ?_⟩
  intro t ht
  have hheights : (fun k : K => ((primitiveRun code (q0, initial) t).2 k).length) =
      (fun k : K => height k ((initial k).length + t)) := by
    funext k
    have hh := local_trace_height (prependStack (initial k) (runOps code (q0, initial) k))
      (height k) (mate k) ((initial k).length + T) (hlocal k)
      ((initial k).length + t) (by omega)
    rw [traceStack_after_prepend] at hh
    have hs := congrFun (traceStacks_runOps code (q0, initial) t) k
    change traceStackFrom (initial k) (runOps code (q0, initial) k) t = _ at hs
    rw [hs] at hh
    exact hh
  have hc := (primitive_step_records code (primitiveRun code (q0, initial) t)).1
  rw [hheights] at hc
  exact hc

lemma output_pop_clean_iff (s s' : K → List A) (output : K) (b : A) :
    ((∀ k : K, StackStep (singleOp output (some (false, b)) k) (s k) (s' k)) ∧
      s' = fun _ => []) ↔
    (s = Function.update (fun _ => []) output [b] ∧ s' = fun _ => []) := by
  constructor
  · rintro ⟨hstep, hs'⟩
    refine ⟨?_, hs'⟩
    funext k
    have hk := hstep k
    rw [hs'] at hk
    by_cases hko : k = output
    · subst k
      simpa [singleOp, StackStep] using hk
    · have hk0 : [] = s k := by
        simpa [singleOp, StackStep, hko] using hk
      simpa [hko] using hk0.symm
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, rfl⟩
    intro k
    by_cases hko : k = output
    · subst k; simp [singleOp, StackStep]
    · simp [singleOp, StackStep, hko]

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

def IndexedTerminalCheck (code : Q → Option (Primitive Q K A))
    (q0 qfinal : Q) (initial : K → List A) (output : K) (b : A)
    (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height mate : K → ℕ → ℕ) (T : ℕ) : Prop :=
  IndexedTraceCheck code q0 initial control ops height mate T ∧
  (∀ k : K, LocalStackTrace (prependStack (initial k) (ops k))
    (height k) (mate k) ((initial k).length + (T + 1))) ∧
  (∀ k : K, ops k T = singleOp output (some (false, b)) k) ∧
  (∀ k : K, height k ((initial k).length + (T + 1)) = 0) ∧
  control T = qfinal ∧ code qfinal = none

lemma indexed_terminal_sound
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height mate : K → ℕ → ℕ) (T : ℕ)
    (h : IndexedTerminalCheck code q0 qfinal initial output b control ops height mate T) :
    code qfinal = none ∧
      primitiveRun code (q0, initial) T =
        (qfinal, Function.update (fun _ => []) output [b]) := by
  obtain ⟨hbase, hlocal, hops, hzero, hq, hhalt⟩ := h
  refine ⟨hhalt, ?_⟩
  have hnext : traceStacks initial ops (T + 1) = fun _ => [] := by
    funext k
    apply List.length_eq_zero_iff.mp
    have hh := local_trace_height (prependStack (initial k) (ops k))
      (height k) (mate k) ((initial k).length + (T + 1)) (hlocal k)
      ((initial k).length + (T + 1)) le_rfl
    rw [traceStack_after_prepend, hzero k] at hh
    exact hh
  have hstep : ∀ k : K, StackStep (singleOp output (some (false, b)) k)
      (traceStacks initial ops T k) (traceStacks initial ops (T + 1) k) := by
    intro k
    have hlegal := (local_stack_trace_from_iff (initial k) (ops k) (T + 1)).mpr
      ⟨height k, mate k, hlocal k⟩
    have hh := hlegal T (by omega)
    rw [hops k] at hh
    exact hh
  have hstacks := ((output_pop_clean_iff (traceStacks initial ops T)
    (traceStacks initial ops (T + 1)) output b).mp ⟨hstep, hnext⟩).1
  rw [indexed_trace_sound code q0 initial control ops height mate T hbase T le_rfl,
    hq, hstacks]

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

omit [DecidableEq K] in
lemma traceStackFrom_congr_upto (initial : List A)
    (ops ops' : ℕ → Option (Bool × A)) (t : ℕ)
    (h : ∀ u : ℕ, u < t → ops u = ops' u) :
    traceStackFrom initial ops t = traceStackFrom initial ops' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [traceStackFrom, h t (by omega)]
    rw [ih (fun u hu => h u (by omega))]

def appendOutputPop (ops : K → ℕ → Option (Bool × A)) (output : K) (b : A)
    (T : ℕ) (k : K) (t : ℕ) : Option (Bool × A) :=
  if t = T then singleOp output (some (false, b)) k else ops k t

lemma traceStacks_appendOutput_before (initial : K → List A)
    (ops : K → ℕ → Option (Bool × A)) (output : K) (b : A) (T t : ℕ)
    (ht : t ≤ T) :
    traceStacks initial (appendOutputPop ops output b T) t = traceStacks initial ops t := by
  funext k
  apply traceStackFrom_congr_upto
  intro u hu
  simp [appendOutputPop, show u ≠ T by omega]

lemma traceStacks_appendOutput_final (initial : K → List A)
    (ops : K → ℕ → Option (Bool × A)) (output : K) (b : A) (T : ℕ)
    (hout : traceStacks initial ops T = Function.update (fun _ => []) output [b]) :
    traceStacks initial (appendOutputPop ops output b T) (T + 1) = fun _ => [] := by
  funext k
  change nextStack (appendOutputPop ops output b T k T)
    (traceStacks initial (appendOutputPop ops output b T) T k) = []
  rw [traceStacks_appendOutput_before initial ops output b T T le_rfl, hout]
  by_cases hko : k = output
  · subst k; simp [appendOutputPop, singleOp, nextStack]
  · simp [appendOutputPop, singleOp, nextStack, hko]

lemma appendOutputPop_legal (initial : K → List A)
    (ops : K → ℕ → Option (Bool × A)) (output : K) (b : A) (T : ℕ)
    (hlegal : ∀ k : K, LegalStackTraceFrom (initial k) (ops k) T)
    (hout : traceStacks initial ops T = Function.update (fun _ => []) output [b]) :
    ∀ k : K, LegalStackTraceFrom (initial k) (appendOutputPop ops output b T k) (T + 1) := by
  intro k t ht
  by_cases hbefore : t < T
  · change StackStep (appendOutputPop ops output b T k t)
      (traceStacks initial (appendOutputPop ops output b T) t k)
      (traceStacks initial (appendOutputPop ops output b T) (t + 1) k)
    rw [traceStacks_appendOutput_before initial ops output b T t (by omega),
      traceStacks_appendOutput_before initial ops output b T (t + 1) (by omega)]
    simpa [appendOutputPop, traceStacks, show t ≠ T by omega] using hlegal k t hbefore
  · have htT : t = T := by omega
    subst t
    change StackStep (appendOutputPop ops output b T k T)
      (traceStacks initial (appendOutputPop ops output b T) T k)
      (traceStacks initial (appendOutputPop ops output b T) (T + 1) k)
    rw [traceStacks_appendOutput_before initial ops output b T T le_rfl,
      traceStacks_appendOutput_final initial ops output b T hout, hout]
    by_cases hko : k = output
    · subst k; simp [appendOutputPop, singleOp, StackStep]
    · simp [appendOutputPop, singleOp, StackStep, hko]

lemma indexed_terminal_complete
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (T : ℕ) (hhalt : code qfinal = none)
    (hfinal : primitiveRun code (q0, initial) T =
      (qfinal, Function.update (fun _ => []) output [b])) :
    ∃ control : ℕ → Q, ∃ ops : K → ℕ → Option (Bool × A),
      ∃ height mate : K → ℕ → ℕ,
        IndexedTerminalCheck code q0 qfinal initial output b control ops height mate T := by
  let oldOps := runOps code (q0, initial)
  let ops := appendOutputPop oldOps output b T
  let control := fun t => (primitiveRun code (q0, initial) t).1
  have hold : ∀ k : K, LegalStackTraceFrom (initial k) (oldOps k) T := by
    intro k t ht
    change StackStep (primitiveOps code (primitiveRun code (q0, initial) t) k)
      (traceStacks initial (runOps code (q0, initial)) t k)
      (traceStacks initial (runOps code (q0, initial)) (t + 1) k)
    rw [traceStacks_runOps code (q0, initial) t,
      traceStacks_runOps code (q0, initial) (t + 1)]
    exact (primitive_step_records code (primitiveRun code (q0, initial) t)).2 k
  have hout : traceStacks initial oldOps T = Function.update (fun _ => []) output [b] := by
    rw [traceStacks_runOps code (q0, initial) T, hfinal]
  have hlegal := appendOutputPop_legal initial oldOps output b T hold hout
  obtain ⟨height, mate, hlocal⟩ :=
    (local_multistack_trace_from_iff initial ops (T + 1)).mp hlegal
  have hheights : ∀ t : ℕ, t ≤ T + 1 → ∀ k : K,
      (traceStacks initial ops t k).length = height k ((initial k).length + t) := by
    intro t ht k
    have hh := local_trace_height (prependStack (initial k) (ops k))
      (height k) (mate k) ((initial k).length + (T + 1)) (hlocal k)
      ((initial k).length + t) (by omega)
    simpa [traceStacks, traceStack_after_prepend] using hh
  have hbase : IndexedTraceCheck code q0 initial control ops height mate T := by
    refine ⟨rfl, ?_, ?_⟩
    · intro k
      exact ⟨(hlocal k).1, fun t ht => (hlocal k).2 t (by omega)⟩
    · intro t ht
      have hhfun : (fun k : K => ((primitiveRun code (q0, initial) t).2 k).length) =
          (fun k : K => height k ((initial k).length + t)) := by
        funext k
        have hh := hheights t (by omega) k
        rw [traceStacks_appendOutput_before initial oldOps output b T t (by omega),
          traceStacks_runOps code (q0, initial) t] at hh
        exact hh
      have hc := (primitive_step_records code (primitiveRun code (q0, initial) t)).1
      rw [hhfun] at hc
      simpa [control, ops, appendOutputPop, oldOps, runOps, primitiveRun, show t ≠ T by omega] using hc
  refine ⟨control, ops, height, mate, hbase, hlocal, ?_, ?_, ?_, hhalt⟩
  · intro k
    simp [ops, appendOutputPop]
  · intro k
    have hh := hheights (T + 1) le_rfl k
    rw [traceStacks_appendOutput_final initial oldOps output b T hout] at hh
    exact hh.symm
  · exact congrArg Prod.fst hfinal

lemma indexed_terminal_iff
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (T : ℕ) :
    (code qfinal = none ∧ primitiveRun code (q0, initial) T =
      (qfinal, Function.update (fun _ => []) output [b])) ↔
    ∃ control : ℕ → Q, ∃ ops : K → ℕ → Option (Bool × A),
      ∃ height mate : K → ℕ → ℕ,
        IndexedTerminalCheck code q0 qfinal initial output b control ops height mate T := by
  constructor
  · rintro ⟨hhalt, hfinal⟩
    exact indexed_terminal_complete code q0 qfinal initial output b T hhalt hfinal
  · rintro ⟨control, ops, height, mate, h⟩
    exact indexed_terminal_sound code q0 qfinal initial output b control ops height mate T h

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

def ChallengeTerminalCheck (code : Q → Option (Primitive Q K A))
    (q0 qfinal : Q) (initial : K → List A) (output : K) (b : A)
    (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height : K → ℕ → ℕ) (T : ℕ) : Prop :=
  control 0 = q0 ∧
  (∀ k : K, ChallengeStackTrace (prependStack (initial k) (ops k))
    (height k) ((initial k).length + (T + 1))) ∧
  (∀ t : ℕ, t < T → ControlCheck code (control t) (control (t + 1))
    (fun k => ops k t) (fun k => height k ((initial k).length + t))) ∧
  (∀ k : K, ops k T = singleOp output (some (false, b)) k) ∧
  (∀ k : K, height k ((initial k).length + (T + 1)) = 0) ∧
  control T = qfinal ∧ code qfinal = none

lemma challenge_terminal_iff_indexed
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height : K → ℕ → ℕ) (T : ℕ) :
    ChallengeTerminalCheck code q0 qfinal initial output b control ops height T ↔
      ∃ mate : K → ℕ → ℕ,
        IndexedTerminalCheck code q0 qfinal initial output b control ops height mate T := by
  constructor
  · rintro ⟨hzero, hstacks, hcontrol, hops, hclean, hq, hhalt⟩
    choose mate hlocal using fun k => challenge_to_local_stack_trace
      (prependStack (initial k) (ops k)) (height k) ((initial k).length + (T + 1))
      (hstacks k)
    have hbase : IndexedTraceCheck code q0 initial control ops height mate T := by
      refine ⟨hzero, ?_, hcontrol⟩
      intro k
      exact ⟨(hlocal k).1, fun t ht => (hlocal k).2 t (by omega)⟩
    exact ⟨mate, hbase, hlocal, hops, hclean, hq, hhalt⟩
  · rintro ⟨mate, hbase, hlocal, hops, hclean, hq, hhalt⟩
    refine ⟨hbase.1, ?_, hbase.2.2, hops, hclean, hq, hhalt⟩
    intro k
    exact local_to_challenge_stack_trace (prependStack (initial k) (ops k))
      (height k) (mate k) ((initial k).length + (T + 1)) (hlocal k)

lemma challenge_terminal_iff
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (T : ℕ) :
    (code qfinal = none ∧ primitiveRun code (q0, initial) T =
      (qfinal, Function.update (fun _ => []) output [b])) ↔
    ∃ control : ℕ → Q, ∃ ops : K → ℕ → Option (Bool × A),
      ∃ height : K → ℕ → ℕ,
        ChallengeTerminalCheck code q0 qfinal initial output b control ops height T := by
  rw [indexed_terminal_iff]
  constructor
  · rintro ⟨control, ops, height, mate, h⟩
    exact ⟨control, ops, height,
      (challenge_terminal_iff_indexed code q0 qfinal initial output b control ops height T).mpr
        ⟨mate, h⟩⟩
  · rintro ⟨control, ops, height, h⟩
    obtain ⟨mate, hlocal⟩ :=
      (challenge_terminal_iff_indexed code q0 qfinal initial output b control ops height T).mp h
    exact ⟨control, ops, height, mate, hlocal⟩

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

/-- One bounded universal query. The response is a potential dip in a stack height.
All other conditions are deterministic checks on the fixed record functions. -/
def TerminalQueryCheck (code : Q → Option (Primitive Q K A))
    (q0 qfinal : Q) (initial : K → List A) (output : K) (b : A)
    (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height : K → ℕ → ℕ) (T N : ℕ)
    (query : K × Fin (N + 1) × Fin (N + 1)) (response : Fin (N + 1)) : Prop :=
  let k := query.1
  let t := query.2.1.val
  let j := query.2.2.val
  let L := (initial k).length + (T + 1)
  control 0 = q0 ∧ height k 0 = 0 ∧
  (t < L → j ≤ L → response.val ≤ L ∧
    StackChallenge (prependStack (initial k) (ops k)) (height k) t j response.val) ∧
  (t < T → ControlCheck code (control t) (control (t + 1))
    (fun k => ops k t) (fun k => height k ((initial k).length + t))) ∧
  ops k T = singleOp output (some (false, b)) k ∧
  height k L = 0 ∧ control T = qfinal ∧ code qfinal = none

lemma challenge_terminal_bounded_query_iff
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height : K → ℕ → ℕ) (T N : ℕ)
    (hN : ∀ k, (initial k).length + (T + 1) ≤ N) :
    ChallengeTerminalCheck code q0 qfinal initial output b control ops height T ↔
      ∀ query : K × Fin (N + 1) × Fin (N + 1),
        ∃ response : Fin (N + 1),
          TerminalQueryCheck code q0 qfinal initial output b control ops height T N
            query response := by
  constructor
  · rintro ⟨hzero, hstacks, hcontrol, hops, hclean, hq, hhalt⟩ ⟨k, t, j⟩
    by_cases ht : t.val < (initial k).length + (T + 1)
    · by_cases hj : j.val ≤ (initial k).length + (T + 1)
      · obtain ⟨r, hr, hcheck⟩ := (hstacks k).2 t.val ht j.val hj
        have hrN := hN k
        refine ⟨⟨r, by omega⟩, hzero, (hstacks k).1, ?_, ?_, hops k, hclean k,
          hq, hhalt⟩
        · exact fun _ _ => ⟨hr, hcheck⟩
        · exact hcontrol t.val
      · refine ⟨⟨0, by omega⟩, hzero, (hstacks k).1, ?_, ?_, hops k, hclean k,
          hq, hhalt⟩
        · exact fun _ h => False.elim (hj h)
        · exact hcontrol t.val
    · refine ⟨⟨0, by omega⟩, hzero, (hstacks k).1, ?_, ?_, hops k, hclean k,
        hq, hhalt⟩
      · exact fun h _ => False.elim (ht h)
      · exact hcontrol t.val
  · intro h
    let z : Fin (N + 1) := ⟨0, by omega⟩
    obtain ⟨r₀, h₀⟩ := h (output, z, z)
    refine ⟨h₀.1, ?_, ?_, ?_, ?_, h₀.2.2.2.2.2.2.1, h₀.2.2.2.2.2.2.2⟩
    · intro k
      obtain ⟨r₁, h₁⟩ := h (k, z, z)
      refine ⟨h₁.2.1, ?_⟩
      intro t ht j hj
      have hk := hN k
      obtain ⟨r, hr⟩ := h (k, ⟨t, by omega⟩, ⟨j, by omega⟩)
      exact ⟨r.val, (hr.2.2.1 ht hj).1, (hr.2.2.1 ht hj).2⟩
    · intro t ht
      have hk := hN output
      obtain ⟨r, hr⟩ := h (output, ⟨t, by omega⟩, z)
      exact hr.2.2.2.1 ht
    · intro k
      obtain ⟨r, hr⟩ := h (k, z, z)
      exact hr.2.2.2.2.1
    · intro k
      obtain ⟨r, hr⟩ := h (k, z, z)
      exact hr.2.2.2.2.2.1

lemma terminal_three_block_iff
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (T N : ℕ)
    (hN : ∀ k, (initial k).length + (T + 1) ≤ N) :
    (code qfinal = none ∧ primitiveRun code (q0, initial) T =
      (qfinal, Function.update (fun _ => []) output [b])) ↔
    ∃ control : ℕ → Q, ∃ ops : K → ℕ → Option (Bool × A),
      ∃ height : K → ℕ → ℕ,
        ∀ query : K × Fin (N + 1) × Fin (N + 1),
          ∃ response : Fin (N + 1),
            TerminalQueryCheck code q0 qfinal initial output b control ops height T N
              query response := by
  rw [challenge_terminal_iff]
  simp_rw [challenge_terminal_bounded_query_iff code q0 qfinal initial output b
    _ _ _ T N hN]

end PEqualNP.Outside.L_lib_123_Audit

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Outside.FP3Strategy

variable {Q K A : Type*} [DecidableEq K]

lemma stack_challenge_height_congr (ops : ℕ → Option (Bool × A))
    (height height' : ℕ → ℕ) (L t j r : ℕ)
    (hh : ∀ s ≤ L, height' s = height s)
    (ht : t < L) (hj : j ≤ L) (hr : r ≤ L) :
    StackChallenge ops height' t j r ↔ StackChallenge ops height t j r := by
  unfold StackChallenge
  rw [hh t (by omega), hh (t + 1) (by omega), hh j hj, hh r hr]

lemma challenge_stack_height_congr (ops : ℕ → Option (Bool × A))
    (height height' : ℕ → ℕ) (L : ℕ)
    (hh : ∀ s ≤ L, height' s = height s) :
    ChallengeStackTrace ops height' L ↔ ChallengeStackTrace ops height L := by
  unfold ChallengeStackTrace
  rw [hh 0 (Nat.zero_le L)]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro ht
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro hj
  apply exists_congr
  intro r
  apply and_congr_right
  intro hr
  exact stack_challenge_height_congr ops height height' L t j r hh ht hj hr

lemma challenge_terminal_height_congr
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height height' : K → ℕ → ℕ) (T : ℕ)
    (hh : ∀ k s, s ≤ (initial k).length + (T + 1) → height' k s = height k s) :
    ChallengeTerminalCheck code q0 qfinal initial output b control ops height' T ↔
      ChallengeTerminalCheck code q0 qfinal initial output b control ops height T := by
  have hstack : (∀ k, ChallengeStackTrace (prependStack (initial k) (ops k))
      (height' k) ((initial k).length + (T + 1))) ↔
      (∀ k, ChallengeStackTrace (prependStack (initial k) (ops k))
        (height k) ((initial k).length + (T + 1))) := by
    apply forall_congr'
    intro k
    exact challenge_stack_height_congr _ _ _ _ (hh k)
  have hcontrol : (∀ t, t < T → ControlCheck code (control t) (control (t + 1))
      (fun k => ops k t) (fun k => height' k ((initial k).length + t))) ↔
      (∀ t, t < T → ControlCheck code (control t) (control (t + 1))
        (fun k => ops k t) (fun k => height k ((initial k).length + t))) := by
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro ht
    have heq : (fun k => height' k ((initial k).length + t)) =
        (fun k => height k ((initial k).length + t)) := by
      funext k
      exact hh k _ (by omega)
    rw [heq]
  have hclean : (∀ k, height' k ((initial k).length + (T + 1)) = 0) ↔
      (∀ k, height k ((initial k).length + (T + 1)) = 0) := by
    apply forall_congr'
    intro k
    rw [hh k _ (by omega)]
  unfold ChallengeTerminalCheck
  rw [hstack, hcontrol, hclean]

lemma challenge_terminal_clamp_height
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (control : ℕ → Q) (ops : K → ℕ → Option (Bool × A))
    (height : K → ℕ → ℕ) (T N : ℕ)
    (hN : ∀ k, (initial k).length + (T + 1) ≤ N)
    (hcheck : ChallengeTerminalCheck code q0 qfinal initial output b control ops height T) :
    ChallengeTerminalCheck code q0 qfinal initial output b control ops
      (fun k t => min (height k t) N) T := by
  apply (challenge_terminal_height_congr code q0 qfinal initial output b control ops
    height (fun k t => min (height k t) N) T ?_).mpr hcheck
  intro k t ht
  apply Nat.min_eq_left
  exact (challenge_stack_height_le _ _ _ (hcheck.2.1 k) t ht).trans (ht.trans (hN k))

lemma terminal_three_block_bounded_heights_iff
    (code : Q → Option (Primitive Q K A)) (q0 qfinal : Q) (initial : K → List A)
    (output : K) (b : A) (T N : ℕ)
    (hN : ∀ k, (initial k).length + (T + 1) ≤ N) :
    (code qfinal = none ∧ primitiveRun code (q0, initial) T =
      (qfinal, Function.update (fun _ => []) output [b])) ↔
    ∃ control : ℕ → Q, ∃ ops : K → ℕ → Option (Bool × A),
      ∃ height : K → ℕ → Fin (N + 1),
        ∀ query : K × Fin (N + 1) × Fin (N + 1),
          ∃ response : Fin (N + 1),
            TerminalQueryCheck code q0 qfinal initial output b control ops
              (fun k t => (height k t).val) T N query response := by
  constructor
  · intro hrun
    obtain ⟨control, ops, height, hcheck⟩ :=
      (challenge_terminal_iff code q0 qfinal initial output b T).mp hrun
    refine ⟨control, ops, fun k t => ⟨min (height k t) N, by
      have := Nat.min_le_right (height k t) N
      omega⟩, ?_⟩
    apply (challenge_terminal_bounded_query_iff code q0 qfinal initial output b
      control ops _ T N hN).mp
    exact challenge_terminal_clamp_height code q0 qfinal initial output b control ops
      height T N hN hcheck
  · rintro ⟨control, ops, height, hcheck⟩
    exact (terminal_three_block_iff code q0 qfinal initial output b T N hN).mpr
      ⟨control, ops, fun k t => (height k t).val, hcheck⟩

end PEqualNP.Outside.L_lib_123_Audit
