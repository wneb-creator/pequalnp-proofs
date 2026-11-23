import Mathlib

namespace BlockReplay

variable {Index State : Type} [DecidableEq Index]

abbrev Event (Index State : Type) := Index × (State → Option State)

def localRun (index : Index) : List (Event Index State) → State → Option State
  | [], state => some state
  | (selected, transition) :: rest, state =>
    if selected = index then (transition state).bind (localRun index rest)
    else localRun index rest state

def globalRun : List (Event Index State) → (Index → State) → Option (Index → State)
  | [], state => some state
  | (selected, transition) :: rest, state =>
    (transition (state selected)).bind fun value => globalRun rest (Function.update state selected value)

def localSuccess (events : List (Event Index State)) (initial : Index → State) : Prop :=
  ∀ index, (localRun index events (initial index)).isSome = true

lemma localSuccess_cons (selected : Index) (transition : State → Option State)
    (rest : List (Event Index State)) (initial : Index → State) :
    localSuccess ((selected, transition) :: rest) initial ↔
      ∃ value, transition (initial selected) = some value ∧
        localSuccess rest (Function.update initial selected value) := by
  constructor
  · intro hall
    have hselected := hall selected
    simp only [localRun, ite_true] at hselected
    cases hvalue : transition (initial selected) with
    | none => simp [hvalue] at hselected
    | some value =>
      refine ⟨value, rfl, ?_⟩
      intro index
      have h := hall index
      by_cases hi : selected = index
      · subst index
        simpa [localRun, hvalue] using h
      · simpa [localRun, hi, Function.update, Ne.symm hi] using h
  · rintro ⟨value, hvalue, hall⟩ index
    have h := hall index
    by_cases hi : selected = index
    · subst index
      simpa [localRun, hvalue] using h
    · simpa [localRun, hi, Function.update, Ne.symm hi] using h

theorem independent_replay_iff (events : List (Event Index State)) (initial : Index → State) :
    localSuccess events initial ↔ (globalRun events initial).isSome = true := by
  induction events generalizing initial with
  | nil => simp [localSuccess, localRun, globalRun]
  | cons event rest ih =>
    obtain ⟨selected, transition⟩ := event
    rw [localSuccess_cons]
    cases hvalue : transition (initial selected) with
    | none => simp [globalRun, hvalue]
    | some value => simpa [globalRun, hvalue] using ih (Function.update initial selected value)

theorem independent_replay_sound (events : List (Event Index State)) (initial : Index → State)
    (h : localSuccess events initial) : ∃ final, globalRun events initial = some final := by
  have hs := (independent_replay_iff events initial).mp h
  cases hrun : globalRun events initial with
  | none => simp [hrun] at hs
  | some final => exact ⟨final, rfl⟩

/-- A controller fixing only finite control cannot separate a joint equality check. -/
theorem joint_rule_not_product :
    ¬ ∃ left right : Bool → Prop, ∀ a b, (a = b ↔ left a ∧ right b) := by
  rintro ⟨left, right, h⟩
  have hfalse := (h false false).mp rfl
  have htrue := (h true true).mp rfl
  have bad := (h false true).mpr ⟨hfalse.1, htrue.2⟩
  cases bad

end BlockReplay
