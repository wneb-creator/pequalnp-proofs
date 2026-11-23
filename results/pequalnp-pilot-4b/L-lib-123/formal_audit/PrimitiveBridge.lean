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


namespace PEqualNP.Outside.AlphabetBound

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

def pushed : TM2.Stmt Γ Λ σ → Set (Sigma Γ)
  | .push k f q => by
      classical
      exact (Set.range fun v : σ => (⟨k, f v⟩ : Sigma Γ)) ∪ pushed q
  | .peek _ _ q => pushed q
  | .pop _ _ q => pushed q
  | .load _ q => pushed q
  | .branch _ q₁ q₂ => by
      classical
      exact pushed q₁ ∪ pushed q₂
  | .goto _ => ∅
  | .halt => ∅

def supported (S : Set (Sigma Γ)) (stk : ∀ k, List (Γ k)) : Prop :=
  ∀ k a, a ∈ stk k → (⟨k, a⟩ : Sigma Γ) ∈ S

lemma stepAux_supported [Fintype σ] [DecidableEq K]
    (q : TM2.Stmt Γ Λ σ) (v : σ) (stk : ∀ k, List (Γ k))
    (S : Set (Sigma Γ)) (hp : pushed q ⊆ S) (hs : supported S stk) :
    supported S (TM2.stepAux q v stk).stk := by
  classical
  induction q generalizing v stk with
  | push k f q ih =>
      apply ih v (Function.update stk k (f v :: stk k))
      · exact fun x hx => hp (Or.inr hx)
      · intro j a ha
        by_cases h : j = k
        · subst j
          simp only [Function.update_self, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hp (Or.inl ⟨v, rfl⟩)
          · exact hs k a ha
        · exact hs j a (by simpa [Function.update_of_ne h] using ha)
  | peek k f q ih => exact ih _ _ hp hs
  | pop k f q ih =>
      apply ih (f v (stk k).head?) (Function.update stk k (stk k).tail) hp
      intro j a ha
      by_cases h : j = k
      · subst j
        apply hs k a
        exact List.mem_of_mem_tail (by simpa only [Function.update_self] using ha)
      · exact hs j a (by simpa [Function.update_of_ne h] using ha)
  | load f q ih => exact ih _ _ hp hs
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux]
      cases h : f v
      · exact ih₂ _ _ (fun x hx => hp (Or.inr hx)) hs
      · exact ih₁ _ _ (fun x hx => hp (Or.inl hx)) hs
  | goto f => exact hs
  | halt => exact hs

def machineAlphabet (tm : FinTM2) : Set (Sigma tm.Γ) :=
  (Set.range fun a : tm.Γ tm.k₀ => (⟨tm.k₀, a⟩ : Sigma tm.Γ)) ∪
    ⋃ l : tm.Λ, pushed (tm.m l)

lemma pushed_finite [Fintype σ] (q : TM2.Stmt Γ Λ σ) : (pushed q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih | pop k f q ih | load f q ih => exact ih
  | branch f q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto f | halt => exact Set.finite_empty

lemma machineAlphabet_finite (tm : FinTM2) : (machineAlphabet tm).Finite := by
  let := tm.σFin
  let := tm.ΛFin
  let := tm.Γk₀Fin
  exact (Set.finite_range _).union (Set.finite_iUnion fun l => pushed_finite (tm.m l))

lemma init_supported (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    supported (machineAlphabet tm) (Turing.initList tm input).stk := by
  classical
  intro k a ha
  by_cases h : k = tm.k₀
  · subst k
    exact Or.inl ⟨a, rfl⟩
  · simp [Turing.initList, h] at ha

lemma step_supported (tm : FinTM2) (a b : tm.Cfg) (hb : b ∈ tm.step a)
    (ha : supported (machineAlphabet tm) a.stk) :
    supported (machineAlphabet tm) b.stk := by
  classical
  let := tm.σFin
  let := tm.ΛFin
  cases a with
  | mk label v stk =>
    cases label with
    | none => exact False.elim (Option.not_mem_none b hb)
    | some label =>
      have heq := Option.mem_some.mp hb
      subst b
      apply stepAux_supported _ _ _ _ ?_ ha
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨label, hx⟩)

lemma reachable_supported (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (cfg : tm.Cfg)
    (h : Relation.ReflTransGen (fun a b => b ∈ tm.step a) (Turing.initList tm input) cfg) :
    supported (machineAlphabet tm) cfg.stk := by
  induction h with
  | refl => exact init_supported tm input
  | @tail b c hab hbc ih => exact step_supported tm b c hbc ih

end PEqualNP.Outside.AlphabetBound

namespace PEqualNP.Outside.Normalization

open Turing

noncomputable def allStmts (tm : FinTM2) : Finset tm.Stmt := by
  classical
  let := tm.ΛFin
  exact Finset.univ.biUnion fun l : tm.Λ => TM2.stmts₁ (tm.m l)

def Node (tm : FinTM2) := {q : tm.Stmt // q ∈ allStmts tm}

lemma root_mem (tm : FinTM2) (l : tm.Λ) : tm.m l ∈ allStmts tm := by
  classical
  let := tm.ΛFin
  change tm.m l ∈ Finset.univ.biUnion (fun z : tm.Λ => TM2.stmts₁ (tm.m z))
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, TM2.stmts₁_self⟩

lemma child_mem (tm : FinTM2) (q : Node tm) (r : tm.Stmt)
    (hr : r ∈ TM2.stmts₁ q.val) : r ∈ allStmts tm := by
  classical
  let := tm.ΛFin
  have hq := q.property
  change q.val ∈ Finset.univ.biUnion (fun z : tm.Λ => TM2.stmts₁ (tm.m z)) at hq
  change r ∈ Finset.univ.biUnion (fun z : tm.Λ => TM2.stmts₁ (tm.m z))
  rcases Finset.mem_biUnion.mp hq with ⟨l, hl, hq⟩
  exact Finset.mem_biUnion.mpr ⟨l, hl, TM2.stmts₁_trans hq hr⟩

noncomputable def root (tm : FinTM2) (l : tm.Λ) : Node tm := ⟨tm.m l, root_mem tm l⟩

noncomputable def child (tm : FinTM2) (q : Node tm) (r : tm.Stmt)
    (hr : r ∈ TM2.stmts₁ q.val) : Node tm := ⟨r, child_mem tm q r hr⟩

noncomputable def code (tm : FinTM2) (q : Node tm) : TM2.Stmt tm.Γ (Node tm) tm.σ := by
  classical
  cases h : q.val with
  | push k f r =>
      exact .push k f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | peek k f r =>
      exact .peek k f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | pop k f r =>
      exact .pop k f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | load f r =>
      exact .load f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | branch f r s =>
      exact .goto fun v => if f v then
        child tm q r (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
        else child tm q s (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
  | goto f => exact .goto fun v => root tm (f v)
  | halt => exact .halt

noncomputable def normalized (tm : FinTM2) : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := tm.Γ
  Λ := Node tm
  main := root tm tm.main
  ΛFin := by unfold Node; infer_instance
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := tm.Γk₀Fin
  m := code tm

noncomputable def liftCfg (tm : FinTM2) (cfg : tm.Cfg) : (normalized tm).Cfg :=
  ⟨cfg.l.map (root tm), cfg.var, cfg.stk⟩

lemma liftCfg_init (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    liftCfg tm (Turing.initList tm input) = Turing.initList (normalized tm) input := by
  rfl

lemma liftCfg_halt (tm : FinTM2) (output : List (tm.Γ tm.k₁)) :
    liftCfg tm (Turing.haltList tm output) = Turing.haltList (normalized tm) output := by
  rfl

def depth {K : Type*} {Γ : K → Type*} {Λ σ : Type*} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => depth q + 1
  | .peek _ _ q => depth q + 1
  | .pop _ _ q => depth q + 1
  | .load _ q => depth q + 1
  | .branch _ q r => depth q + depth r + 1
  | .goto _ => 1
  | .halt => 1

def oneStep {α : Type*} (f : α → Option α) (a b : α) (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  ⟨⟨1, by change f a = some b; exact h⟩, le_rfl⟩

def widenTime {α : Type*} {f : α → Option α} {a : α} {b : Option α} {m n : ℕ}
    (h : StateTransition.EvalsToInTime f a b m) (hmn : m ≤ n) :
    StateTransition.EvalsToInTime f a b n :=
  { h with steps_le_m := h.steps_le_m.trans hmn }

lemma simulate_statement (tm : FinTM2) (q : tm.Stmt) (hq : q ∈ allStmts tm)
    (v : tm.σ) (stk : ∀ k, List (tm.Γ k)) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      ⟨some ⟨q, hq⟩, v, stk⟩ (some (liftCfg tm (TM2.stepAux q v stk))) (depth q)) := by
  classical
  induction q generalizing v stk with
  | push k f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.push k f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr v (Function.update stk k (f v :: stk k))
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | peek k f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.peek k f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr (f v (stk k).head?) stk
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | pop k f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.pop k f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr (f v (stk k).head?) (Function.update stk k (stk k).tail)
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | load f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.load f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr (f v) stk
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | branch f r s ihr ihs =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.branch f r s, hq⟩ r
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
      have hs : s ∈ allStmts tm := child_mem tm ⟨.branch f r s, hq⟩ s
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
      cases hv : f v
      · obtain ⟨rest⟩ := ihs hs v stk
        have first : (normalized tm).step ⟨some ⟨.branch f r s, hq⟩, v, stk⟩ =
            some ⟨some ⟨s, hs⟩, v, stk⟩ := by
          simp [normalized, FinTM2.step, TM2.step, code, TM2.stepAux, hv, child]
          rfl
        have total := StateTransition.EvalsToInTime.trans _ 1 (depth s) _ _ _
          (oneStep _ _ _ first) rest
        simp only [TM2.stepAux, hv, Bool.cond_false]
        exact ⟨widenTime total (by dsimp [depth]; omega)⟩
      · obtain ⟨rest⟩ := ihr hr v stk
        have first : (normalized tm).step ⟨some ⟨.branch f r s, hq⟩, v, stk⟩ =
            some ⟨some ⟨r, hr⟩, v, stk⟩ := by
          simp [normalized, FinTM2.step, TM2.step, code, TM2.stepAux, hv, child]
          rfl
        have total := StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
          (oneStep _ _ _ first) rest
        simp only [TM2.stepAux, hv, Bool.cond_true]
        exact ⟨widenTime total (by dsimp [depth]; omega)⟩
  | goto f => exact ⟨oneStep _ _ _ (by rfl)⟩
  | halt => exact ⟨oneStep _ _ _ (by rfl)⟩

noncomputable def bound (tm : FinTM2) : ℕ := by
  let := tm.ΛFin
  exact 1 + ∑ l : tm.Λ, depth (tm.m l)

lemma depth_le_bound (tm : FinTM2) (l : tm.Λ) : depth (tm.m l) ≤ bound tm := by
  let := tm.ΛFin
  have h : depth (tm.m l) ≤ ∑ z : tm.Λ, depth (tm.m z) :=
    Finset.single_le_sum (f := fun z : tm.Λ => depth (tm.m z))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  unfold bound
  dsimp only
  omega

lemma simulate_step (tm : FinTM2) (a b : tm.Cfg) (h : tm.step a = some b) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      (liftCfg tm a) (some (liftCfg tm b)) (bound tm)) := by
  cases a with
  | mk label v stk =>
    cases label with
    | none => cases h
    | some l =>
      have hb : TM2.stepAux (tm.m l) v stk = b := Option.some.inj h
      subst b
      obtain ⟨run⟩ := simulate_statement tm (tm.m l) (root_mem tm l) v stk
      exact ⟨widenTime run (depth_le_bound tm l)⟩

lemma iterate_none {α : Type*} (f : α → Option α) (n : ℕ) :
    (fun x : Option α => x.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma simulate_steps (tm : FinTM2) (n : ℕ) (a b : tm.Cfg)
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) = some b) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      (liftCfg tm a) (some (liftCfg tm b)) (bound tm * n)) := by
  induction n generalizing a with
  | zero =>
      have hab : a = b := Option.some.inj h
      subst a
      exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      change (fun x : Option tm.Cfg => x.bind tm.step)^[n] (tm.step a) = some b at h
      cases ha : tm.step a with
      | none =>
          rw [ha, iterate_none] at h
          cases h
      | some c =>
          rw [ha] at h
          obtain ⟨rest⟩ := ih c h
          obtain ⟨first⟩ := simulate_step tm a c ha
          have total := StateTransition.EvalsToInTime.trans _ (bound tm) (bound tm * n)
            _ _ _ first rest
          rw [Nat.mul_succ]
          exact ⟨total⟩

lemma simulate_time (tm : FinTM2) (a b : tm.Cfg) (t : ℕ)
    (h : StateTransition.EvalsToInTime tm.step a (some b) t) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      (liftCfg tm a) (some (liftCfg tm b)) (bound tm * t)) := by
  obtain ⟨run⟩ := simulate_steps tm h.steps a b h.evals_in_steps
  exact ⟨widenTime run (Nat.mul_le_mul_left _ h.steps_le_m)⟩

noncomputable def normalizedComputation {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (c : Turing.TM2ComputableInTime ea eb f) : Turing.TM2ComputableInTime ea eb f where
  tm := normalized c.tm
  inputAlphabet := c.inputAlphabet
  outputAlphabet := c.outputAlphabet
  time n := bound c.tm * c.time n
  outputsFun a := Classical.choice (simulate_time c.tm _ _ _ (c.outputsFun a))

lemma normalized_code_depth (tm : FinTM2) (q : Node tm) : depth (code tm q) ≤ 2 := by
  classical
  rcases q with ⟨q, hq⟩
  cases q <;> simp [code, depth]

end PEqualNP.Outside.Normalization

namespace PEqualNP.Outside.PrimitiveBridge

open Turing
open PEqualNP.Outside.L_lib_123_Audit

abbrev Symbol (tm : FinTM2) (S : Set (Sigma tm.Γ)) := {a : Sigma tm.Γ // a ∈ S}
abbrev BaseState (tm : FinTM2) := Option (Normalization.Node tm) × tm.σ
abbrev State (tm : FinTM2) (S : Set (Sigma tm.Γ)) :=
  BaseState tm ⊕ (tm.K × Symbol tm S × BaseState tm)

noncomputable def encodeSymbol (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (k : tm.K) (a : tm.Γ k) : Symbol tm S := by
  classical
  exact if h : (⟨k, a⟩ : Sigma tm.Γ) ∈ S then ⟨⟨k, a⟩, h⟩ else default

noncomputable def decodeSymbol (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (k : tm.K) (a : Symbol tm S) : Option (tm.Γ k) := by
  classical
  exact if h : a.val.fst = k then some (h ▸ a.val.snd) else none

lemma decode_encode (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (k : tm.K) (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ S) :
    decodeSymbol tm S k (encodeSymbol tm S default k a) = some a := by
  classical
  simp only [encodeSymbol, dite_eq_left ha]
  simp [decodeSymbol]

noncomputable def encodeStacks (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (stk : ∀ k, List (tm.Γ k)) : tm.K → List (Symbol tm S) :=
  fun k => (stk k).map (encodeSymbol tm S default k)

lemma encodeStacks_update (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (stk : ∀ k, List (tm.Γ k)) (k : tm.K) (l : List (tm.Γ k)) :
    encodeStacks tm S default (Function.update stk k l) =
      Function.update (encodeStacks tm S default stk) k (l.map (encodeSymbol tm S default k)) := by
  classical
  funext j
  by_cases h : j = k
  · subst j
    simp [encodeStacks]
  · simp [encodeStacks, h]

lemma decode_head (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (stk : ∀ k, List (tm.Γ k)) (k : tm.K)
    (hs : AlphabetBound.supported S stk) :
    ((encodeStacks tm S default stk k).head?).bind (decodeSymbol tm S k) = (stk k).head? := by
  cases h : stk k with
  | nil => simp [encodeStacks, h]
  | cons a l =>
      have ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ S := hs k a (by simp [h])
      simp [encodeStacks, h, decode_encode tm S default k a ha]

noncomputable def encodeCfg (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (cfg : TM2.Cfg tm.Γ (Normalization.Node tm) tm.σ) :
    State tm S × (tm.K → List (Symbol tm S)) :=
  (.inl (cfg.l, cfg.var), encodeStacks tm S default cfg.stk)

noncomputable def code (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S) :
    State tm S → Option (Primitive (State tm S) tm.K (Symbol tm S)) := by
  classical
  intro state
  rcases state with ⟨label, v⟩ | ⟨k, a, next⟩
  · cases label with
    | none => exact none
    | some q =>
        cases h : q.val with
        | push k f r =>
            exact some (.inr (.inl ((k, encodeSymbol tm S default k (f v)),
              .inl (some (Normalization.child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)), v))))
        | peek k f r =>
            let child := Normalization.child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)
            exact some (.inr (.inr (k, fun symbol => match symbol with
              | none => .inl (some child, f v none)
              | some a => .inr (k, a, (some child, f v (decodeSymbol tm S k a))))))
        | pop k f r =>
            let child := Normalization.child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)
            exact some (.inr (.inr (k, fun symbol =>
              .inl (some child, f v (symbol.bind (decodeSymbol tm S k))))))
        | load f r =>
            exact some (.inl (.inl (some (Normalization.child tm q r
              (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self)), f v)))
        | branch f r s =>
            exact some (.inl (.inl (some (if f v then
              Normalization.child tm q r (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
              else Normalization.child tm q s (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))), v)))
        | goto f => exact some (.inl (.inl (some (Normalization.root tm (f v)), v)))
        | halt => exact some (.inl (.inl (none, v)))
  · exact some (.inr (.inl ((k, a), .inl next)))

lemma state_finite (tm : FinTM2) (S : Set (Sigma tm.Γ)) (hS : S.Finite) :
    Finite (State tm S) := by
  let := tm.kFin
  let := tm.σFin
  let := hS.fintype
  unfold State BaseState Symbol Normalization.Node
  infer_instance

lemma code_halted (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S) (v : tm.σ) :
    code tm S default (.inl (none, v)) = none := by
  rfl

end PEqualNP.Outside.PrimitiveBridge

namespace PEqualNP.Outside.PrimitiveBridge

open Turing
open PEqualNP.Outside.L_lib_123_Audit

lemma encodeStacks_tail_update (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (default : Symbol tm S) (stk : ∀ k, List (tm.Γ k)) (k : tm.K) :
    encodeStacks tm S default (Function.update stk k (stk k).tail) =
      Function.update (encodeStacks tm S default stk) k
        ((encodeStacks tm S default stk k).tail) := by
  rw [encodeStacks_update]
  simp [encodeStacks]

lemma simulate_one (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S)
    (a b : TM2.Cfg tm.Γ (Normalization.Node tm) tm.σ)
    (hab : (Normalization.normalized tm).step a = some b)
    (hs : AlphabetBound.supported S a.stk) :
    ∃ n : ℕ, n ≤ 2 ∧ primitiveRun (code tm S default) (encodeCfg tm S default a) n =
      encodeCfg tm S default b := by
  classical
  cases a with
  | mk label v stk =>
    cases label with
    | none => cases hab
    | some q =>
      have hb : TM2.stepAux (Normalization.code tm q) v stk = b := Option.some.inj hab
      subst b
      rcases q with ⟨q, hq⟩
      dsimp only [FinTM2.Stmt] at q hq
      cases q with
      | push k f r =>
        refine ⟨1, by omega, ?_⟩
        simp [primitiveRun, primitiveStep, code, encodeCfg,
          Normalization.code, TM2.stepAux, encodeStacks]
        simpa only [encodeStacks, List.map_cons] using
          (encodeStacks_update tm S default stk k (f v :: stk k)).symm
      | pop k f r =>
        refine ⟨1, by omega, ?_⟩
        have hdecode := decode_head tm S default stk k hs
        simp only [primitiveRun, primitiveStep, code, encodeCfg,
          Normalization.code, TM2.stepAux]
        rw [hdecode]
        apply Prod.ext
        · rfl
        · exact (encodeStacks_tail_update tm S default stk k).symm
      | peek k f r =>
        cases hk : stk k with
        | nil =>
          refine ⟨1, by omega, ?_⟩
          simp [primitiveRun, primitiveStep, code, encodeCfg,
            Normalization.code, TM2.stepAux, encodeStacks, hk]
        | cons a l =>
          refine ⟨2, by omega, ?_⟩
          have ha : (⟨k, a⟩ : Sigma tm.Γ) ∈ S := hs k a (by
            change a ∈ stk k
            rw [hk]
            exact List.mem_cons_self)
          simp [primitiveRun, primitiveStep, code, encodeCfg,
            Normalization.code, TM2.stepAux, encodeStacks, hk,
            decode_encode tm S default k a ha, List.head?_cons, List.map_cons, List.tail_cons]
      | load f r =>
        refine ⟨1, by omega, ?_⟩
        simp [primitiveRun, primitiveStep, code, encodeCfg,
          Normalization.code, TM2.stepAux]
      | branch f r s =>
        refine ⟨1, by omega, ?_⟩
        cases h : f v <;>
          simp [primitiveRun, primitiveStep, code, encodeCfg,
            Normalization.code, TM2.stepAux, h]
      | goto f =>
        refine ⟨1, by omega, ?_⟩
        simp [primitiveRun, primitiveStep, code, encodeCfg,
          Normalization.code, TM2.stepAux]
      | halt =>
        refine ⟨1, by omega, ?_⟩
        simp [primitiveRun, primitiveStep, code, encodeCfg,
          Normalization.code, TM2.stepAux]

end PEqualNP.Outside.PrimitiveBridge

namespace PEqualNP.Outside.PrimitiveBridge

open Turing
open PEqualNP.Outside.L_lib_123_Audit

lemma run_add {Q K A : Type*} [DecidableEq K]
    (code : Q → Option (Primitive Q K A)) (cfg : Q × (K → List A)) (m n : ℕ) :
    primitiveRun code cfg (m + n) = primitiveRun code (primitiveRun code cfg m) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (primitiveStep code) ih

lemma run_halted {Q K A : Type*} [DecidableEq K]
    (code : Q → Option (Primitive Q K A)) (cfg : Q × (K → List A))
    (h : code cfg.1 = none) (n : ℕ) : primitiveRun code cfg n = cfg := by
  induction n with
  | zero => rfl
  | succ n ih => simp [primitiveRun, ih, primitiveStep, h]

lemma step_supports_subset (tm : FinTM2) (S : Set (Sigma tm.Γ))
    (hS : AlphabetBound.machineAlphabet tm ⊆ S)
    (a b : tm.Cfg) (hab : tm.step a = some b) (hs : AlphabetBound.supported S a.stk) :
    AlphabetBound.supported S b.stk := by
  classical
  let := tm.σFin
  cases a with
  | mk label v stk =>
    cases label with
    | none => cases hab
    | some l =>
      have hb : TM2.stepAux (tm.m l) v stk = b := Option.some.inj hab
      subst b
      apply AlphabetBound.stepAux_supported _ _ _ _ ?_ hs
      intro x hx
      apply hS
      exact Or.inr (Set.mem_iUnion.mpr ⟨l, hx⟩)

lemma simulate_steps (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S)
    (hS : AlphabetBound.machineAlphabet (Normalization.normalized tm) ⊆ S)
    (n : ℕ) (a b : TM2.Cfg tm.Γ (Normalization.Node tm) tm.σ)
    (hs : AlphabetBound.supported S a.stk)
    (h : (fun x : Option (Normalization.normalized tm).Cfg =>
      x.bind (Normalization.normalized tm).step)^[n] (some a) = some b) :
    ∃ m : ℕ, m ≤ 2 * n ∧ primitiveRun (code tm S default) (encodeCfg tm S default a) m =
      encodeCfg tm S default b := by
  induction n generalizing a with
  | zero =>
    have hab : a = b := Option.some.inj h
    subst a
    exact ⟨0, by omega, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    change (fun x : Option (Normalization.normalized tm).Cfg =>
      x.bind (Normalization.normalized tm).step)^[n]
      ((Normalization.normalized tm).step a) = some b at h
    cases ha : (Normalization.normalized tm).step a with
    | none =>
      rw [ha, Normalization.iterate_none] at h
      cases h
    | some c =>
      rw [ha] at h
      have hc := step_supports_subset (Normalization.normalized tm) S hS a c ha hs
      obtain ⟨m₁, hm₁, hr₁⟩ := simulate_one tm S default a c ha hs
      obtain ⟨m₂, hm₂, hr₂⟩ := ih c hc h
      refine ⟨m₁ + m₂, by omega, ?_⟩
      rw [run_add, hr₁]
      exact hr₂

lemma simulate_time (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S)
    (hS : AlphabetBound.machineAlphabet (Normalization.normalized tm) ⊆ S)
    (a b : TM2.Cfg tm.Γ (Normalization.Node tm) tm.σ) (t : ℕ)
    (hs : AlphabetBound.supported S a.stk)
    (h : StateTransition.EvalsToInTime (Normalization.normalized tm).step a (some b) t) :
    ∃ m : ℕ, m ≤ 2 * t ∧ primitiveRun (code tm S default) (encodeCfg tm S default a) m =
      encodeCfg tm S default b := by
  obtain ⟨m, hm, hr⟩ := simulate_steps tm S default hS h.steps a b hs h.evals_in_steps
  exact ⟨m, hm.trans (Nat.mul_le_mul_left 2 h.steps_le_m), hr⟩

lemma simulate_halted_at (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S)
    (hS : AlphabetBound.machineAlphabet (Normalization.normalized tm) ⊆ S)
    (a b : TM2.Cfg tm.Γ (Normalization.Node tm) tm.σ) (t : ℕ)
    (hs : AlphabetBound.supported S a.stk) (hb : b.l = none)
    (h : StateTransition.EvalsToInTime (Normalization.normalized tm).step a (some b) t) :
    primitiveRun (code tm S default) (encodeCfg tm S default a) (2 * t) =
      encodeCfg tm S default b := by
  obtain ⟨m, hm, hr⟩ := simulate_time tm S default hS a b t hs h
  have hhalt : code tm S default (encodeCfg tm S default b).1 = none := by
    simp only [encodeCfg, hb]
    exact code_halted tm S default b.var
  calc
    primitiveRun (code tm S default) (encodeCfg tm S default a) (2 * t) =
        primitiveRun (code tm S default) (encodeCfg tm S default a) (m + (2 * t - m)) := by
      congr 1
      omega
    _ = primitiveRun (code tm S default) (encodeCfg tm S default b) (2 * t - m) := by
      rw [run_add, hr]
    _ = encodeCfg tm S default b := run_halted _ _ hhalt _

lemma simulate_original_output (tm : FinTM2) (S : Set (Sigma tm.Γ)) (default : Symbol tm S)
    (hS : AlphabetBound.machineAlphabet (Normalization.normalized tm) ⊆ S)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (t : ℕ)
    (h : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some (Turing.haltList tm output)) t) :
    primitiveRun (code tm S default)
      (encodeCfg tm S default (Turing.initList (Normalization.normalized tm) input))
      (2 * (Normalization.bound tm * t)) =
        encodeCfg tm S default (Turing.haltList (Normalization.normalized tm) output) := by
  obtain ⟨hnormal⟩ := Normalization.simulate_time tm _ _ t h
  rw [Normalization.liftCfg_init, Normalization.liftCfg_halt] at hnormal
  apply simulate_halted_at tm S default hS _ _ _ ?_ rfl hnormal
  intro k a ha
  exact hS (AlphabetBound.init_supported (Normalization.normalized tm) input k a ha)

end PEqualNP.Outside.PrimitiveBridge

namespace PEqualNP.Outside.PrimitiveBridge

open Turing
open PEqualNP.Outside.L_lib_123_Audit


noncomputable def binarySupport (c : TM2ComputableAux Bool Bool) : Set (Sigma c.tm.Γ) :=
  AlphabetBound.machineAlphabet (Normalization.normalized c.tm) ∪
    Set.range (fun b : Bool => (⟨c.tm.k₁, c.outputAlphabet.symm b⟩ : Sigma c.tm.Γ))

lemma binarySupport_finite (c : TM2ComputableAux Bool Bool) : (binarySupport c).Finite :=
  (AlphabetBound.machineAlphabet_finite (Normalization.normalized c.tm)).union (Set.finite_range _)

def binaryDefault (c : TM2ComputableAux Bool Bool) : Symbol c.tm (binarySupport c) :=
  ⟨⟨c.tm.k₀, c.inputAlphabet.symm false⟩, Or.inl (Or.inl ⟨c.inputAlphabet.symm false, rfl⟩)⟩

noncomputable def binaryCode (c : TM2ComputableAux Bool Bool) :
    State c.tm (binarySupport c) →
      Option (Primitive (State c.tm (binarySupport c)) c.tm.K (Symbol c.tm (binarySupport c))) :=
  code c.tm (binarySupport c) (binaryDefault c)

noncomputable def initialState (c : TM2ComputableAux Bool Bool) : State c.tm (binarySupport c) :=
  .inl (some (Normalization.root c.tm c.tm.main), c.tm.initialState)

def finalState (c : TM2ComputableAux Bool Bool) : State c.tm (binarySupport c) :=
  .inl (none, c.tm.initialState)

noncomputable def initialStacks (c : TM2ComputableAux Bool Bool) (x : List Bool) :
    c.tm.K → List (Symbol c.tm (binarySupport c)) :=
  encodeStacks c.tm (binarySupport c) (binaryDefault c)
    (Turing.initList (Normalization.normalized c.tm) (x.map c.inputAlphabet.symm)).stk

noncomputable def outputSymbol (c : TM2ComputableAux Bool Bool) (b : Bool) :
    Symbol c.tm (binarySupport c) :=
  encodeSymbol c.tm (binarySupport c) (binaryDefault c) c.tm.k₁ (c.outputAlphabet.symm b)

lemma outputSymbol_decode (c : TM2ComputableAux Bool Bool) (b : Bool) :
    decodeSymbol c.tm (binarySupport c) c.tm.k₁ (outputSymbol c b) =
      some (c.outputAlphabet.symm b) :=
  decode_encode c.tm (binarySupport c) (binaryDefault c) c.tm.k₁ _ (Or.inr ⟨b, rfl⟩)

lemma outputSymbol_injective (c : TM2ComputableAux Bool Bool) : Function.Injective (outputSymbol c) := by
  intro a b hab
  have h := congrArg (decodeSymbol c.tm (binarySupport c) c.tm.k₁) hab
  rw [outputSymbol_decode, outputSymbol_decode] at h
  exact c.outputAlphabet.symm.injective (Option.some.inj h)

lemma initialStacks_length (c : TM2ComputableAux Bool Bool) (x : List Bool) (k : c.tm.K) :
    (initialStacks c x k).length ≤ x.length := by
  classical
  by_cases hk : k = c.tm.k₀
  · subst k
    simp [initialStacks, encodeStacks, Turing.initList, Normalization.normalized]
    change (x.map c.inputAlphabet.symm).length ≤ x.length
    simp
  · simp [initialStacks, encodeStacks, Turing.initList, Normalization.normalized, hk]

lemma encode_init (c : TM2ComputableAux Bool Bool) (x : List Bool) :
    encodeCfg c.tm (binarySupport c) (binaryDefault c)
      (Turing.initList (Normalization.normalized c.tm) (x.map c.inputAlphabet.symm)) =
      (initialState c, initialStacks c x) := by
  rfl

lemma encode_halt_single (c : TM2ComputableAux Bool Bool) (b : Bool) :
    encodeCfg c.tm (binarySupport c) (binaryDefault c)
      (Turing.haltList (Normalization.normalized c.tm) [c.outputAlphabet.symm b]) =
      (finalState c, Function.update (fun _ => []) c.tm.k₁ [outputSymbol c b]) := by
  classical
  apply Prod.ext
  · rfl
  · funext k
    by_cases hk : k = c.tm.k₁
    · subst k
      simp [encodeCfg, encodeStacks, Turing.haltList, Normalization.normalized, outputSymbol]
      exact ⟨c.outputAlphabet.symm b, rfl, rfl⟩
    · simp [encodeCfg, encodeStacks, Turing.haltList, Normalization.normalized, outputSymbol, hk]

lemma binary_run_output (c : TM2ComputableAux Bool Bool) (x : List Bool) (b : Bool) (t : ℕ)
    (h : StateTransition.EvalsToInTime c.tm.step
      (Turing.initList c.tm (x.map c.inputAlphabet.symm))
      (some (Turing.haltList c.tm [c.outputAlphabet.symm b])) t) :
    primitiveRun (binaryCode c) (initialState c, initialStacks c x)
      (2 * (Normalization.bound c.tm * t)) =
        (finalState c, Function.update (fun _ => []) c.tm.k₁ [outputSymbol c b]) := by
  have hr := simulate_original_output c.tm (binarySupport c) (binaryDefault c)
    (fun _ hx => Or.inl hx) (x.map c.inputAlphabet.symm) [c.outputAlphabet.symm b] t h
  erw [encode_init c x, encode_halt_single c b] at hr
  exact hr

lemma binary_state_finite (c : TM2ComputableAux Bool Bool) : Finite (State c.tm (binarySupport c)) :=
  state_finite c.tm (binarySupport c) (binarySupport_finite c)

lemma binary_symbol_finite (c : TM2ComputableAux Bool Bool) : Finite (Symbol c.tm (binarySupport c)) :=
  (binarySupport_finite c).to_subtype

end PEqualNP.Outside.PrimitiveBridge

namespace PEqualNP.Outside.PrimitiveBridge

open Turing
open PEqualNP.Outside.L_lib_123_Audit

def BinaryGame (c : TM2ComputableAux Bool Bool) (x : List Bool) (T : ℕ) : Prop :=
  ∃ control : ℕ → State c.tm (binarySupport c),
    ∃ ops : c.tm.K → ℕ → Option (Bool × Symbol c.tm (binarySupport c)),
      ∃ height : c.tm.K → ℕ → Fin (x.length + T + 2),
        ∀ query : c.tm.K × Fin (x.length + T + 2) × Fin (x.length + T + 2),
          ∃ response : Fin (x.length + T + 2),
            TerminalQueryCheck (binaryCode c) (initialState c) (finalState c)
              (initialStacks c x) c.tm.k₁ (outputSymbol c true) control ops
              (fun k t => (height k t).val) T (x.length + T + 1) query response

lemma binaryGame_iff (c : TM2ComputableAux Bool Bool) (x : List Bool) (T : ℕ) :
    BinaryGame c x T ↔
    (binaryCode c (finalState c) = none ∧
      primitiveRun (binaryCode c) (initialState c, initialStacks c x) T =
        (finalState c, Function.update (fun _ => []) c.tm.k₁ [outputSymbol c true])) := by
  exact (terminal_three_block_bounded_heights_iff (binaryCode c) (initialState c)
    (finalState c) (initialStacks c x) c.tm.k₁ (outputSymbol c true) T (x.length + T + 1)
    (fun k => by have h := initialStacks_length c x k; omega)).symm

lemma binaryGame_of_output (c : TM2ComputableAux Bool Bool) (x : List Bool) (b : Bool) (t : ℕ)
    (h : StateTransition.EvalsToInTime c.tm.step
      (Turing.initList c.tm (x.map c.inputAlphabet.symm))
      (some (Turing.haltList c.tm [c.outputAlphabet.symm b])) t) :
    BinaryGame c x (2 * (Normalization.bound c.tm * t)) ↔ b = true := by
  rw [binaryGame_iff]
  have hrun := binary_run_output c x b t h
  constructor
  · rintro ⟨_, htrue⟩
    have hcfg := hrun.symm.trans htrue
    have hlist : [outputSymbol c b] = [outputSymbol c true] := by
      simpa only [Function.update_self] using
        congrArg (fun cfg : State c.tm (binarySupport c) ×
          (c.tm.K → List (Symbol c.tm (binarySupport c))) => cfg.2 c.tm.k₁) hcfg
    exact outputSymbol_injective c (List.cons.inj hlist).1
  · intro hb
    subst b
    exact ⟨rfl, hrun⟩

lemma binaryGame_computes {f : List Bool → Bool}
    (c : TM2ComputableInTime (fun x : List Bool => x) Computability.encodeBool f)
    (x : List Bool) (t : ℕ) (ht : c.time x.length ≤ t) :
    BinaryGame c.toTM2ComputableAux x (2 * (Normalization.bound c.tm * t)) ↔ f x = true := by
  apply binaryGame_of_output
  apply Normalization.widenTime (c.outputsFun x) ht

end PEqualNP.Outside.PrimitiveBridge
