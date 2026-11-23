import DynamicMemoTest

namespace PEqualNP.Outside.L_meta_670_aux.MemoBatch

open LiveCheck MemoProtocol

variable (Context : List Sig → Type)
variable (cut : (k t : Nat) → (v : List Sig) → Context v → Bool)
variable (next : (k t : Nat) → (v : List Sig) → Context v → List (Child Context))
variable (retain : Nat → Nat → List Sig → Bool)

def run (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j)) :
    Nat → Nat → Memo → Bool × Memo
  | 0, _, m => (true,m)
  | n+1, start, m =>
    let result := solve Context cut next retain k t (state start) (context start) m
    if result.1 then (false,result.2)
    else run k t state context n (start+1) result.2

lemma run_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j))
    (n start : Nat) (m : Memo) (hm : Sound m) :
    Sound (run Context cut next retain k t state context n start m).2 ∧
      ((run Context cut next retain k t state context n start m).1 = true →
        ∀ j, start ≤ j → j < start+n → Impossible k t (state j)) := by
  induction n generalizing start m with
  | zero =>
    refine ⟨hm,?_⟩
    intro _ j hlow hhigh
    omega
  | succ n ih =>
    have hs := solve_sound Context cut next retain cutSound k t
      (state start) (context start) m hm
    simp only [run]
    split
    · exact ⟨hs.1,by simp⟩
    · rename_i hf
      have hd : (solve Context cut next retain k t (state start) (context start) m).1 = false := by
        cases h : (solve Context cut next retain k t (state start) (context start) m).1 <;> simp_all
      have hi := ih (start+1) _ hs.1
      refine ⟨hi.1,?_⟩
      intro hdone j hlow hhigh
      by_cases hj : j = start
      · subst j
        exact hs.2 hd
      · exact hi.2 hdone j (by omega) (by omega)

def check (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j))
    (n start : Nat) : Bool :=
  (run Context cut next retain k t state context n start .empty).1

lemma check_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    (k t : Nat) (state : Nat → List Sig) (context : ∀ j, Context (state j))
    {n start : Nat} (hc : check Context cut next retain k t state context n start = true) :
    ∀ j, start ≤ j → j < start+n → Impossible k t (state j) := by
  exact (run_sound Context cut next retain cutSound k t state context n start .empty trivial).2 hc

end PEqualNP.Outside.L_meta_670_aux.MemoBatch
