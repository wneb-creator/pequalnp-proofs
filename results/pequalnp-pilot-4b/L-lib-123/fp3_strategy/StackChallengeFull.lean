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
