import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux

namespace PackingThree

structure Block where
  vertices : Nat
  active : Nat
  edges : Nat

structure State where
  used : Nat
  covered : Nat
  seen : Nat
  twice : Nat
  thrice : Nat
  count : Nat

def emptyState : State := ⟨0, 0, 0, 0, 0, 0⟩

def ok (s : State) (b : Block) : Bool :=
  (s.used &&& b.vertices == 0) && (s.thrice &&& b.active == 0)

def step (s : State) (b : Block) : State :=
  ⟨s.used ||| b.vertices, s.covered ||| b.edges,
   s.seen ||| b.active, s.twice ||| (s.seen &&& b.active),
   s.thrice ||| (s.twice &&& b.active), s.count + 1⟩

def flagCount (mask : Nat) : Nat :=
  (Finset.univ.filter fun a : Fin 52 => mask.testBit a.val).card

def good (s : State) : Bool := decide (flagCount s.covered ≤ 29 + s.count)

def upperEdges (s : State) (bs : List Block) : Nat :=
  bs.foldl (fun mask b => mask ||| b.edges) s.covered

def prune (s : State) (bs : List Block) : Bool :=
  decide (flagCount (upperEdges s bs) ≤ 29 + s.count)

end PackingThree

namespace PackingPrunedDFS

variable {α σ : Type}

def branches (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) : List α → Bool
  | [] => true
  | b :: bs =>
      (if ok s b then recur (step s b) (bs.filter (ok (step s b))) else true) &&
        branches ok step recur s bs

def check (ok : σ → α → Bool) (step : σ → α → σ)
    (good : σ → Bool) (prune : σ → List α → Bool) : Nat → σ → List α → Bool
  | 0, s, bs => good s && bs.isEmpty
  | fuel + 1, s, bs =>
      if prune s bs then true
      else good s && branches ok step (check ok step good prune fuel) s bs

def validTrace (ok : σ → α → Bool) (step : σ → α → σ) : σ → List α → Bool
  | _, [] => true
  | s, b :: bs => ok s b && validTrace ok step (step s b) bs

end PackingPrunedDFS


namespace PackingPrunedDFS

variable {α σ : Type}

lemma validTrace_ok (ok : σ → α → Bool) (step : σ → α → σ)
    (ok_antitone : ∀ s b c, ok (step s b) c = true → ok s c = true)
    (s : σ) (chosen : List α) (hvalid : validTrace ok step s chosen = true) :
    ∀ c ∈ chosen, ok s c = true := by
  induction chosen generalizing s with
  | nil => simp
  | cons b bs ih =>
    simp only [validTrace, Bool.and_eq_true] at hvalid
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hvalid.1
    · exact ok_antitone s b c (ih (step s b) hvalid.2 c hc)

lemma branches_sound (ok : σ → α → Bool) (step : σ → α → σ)
    (good : σ → Bool) (recur : σ → List α → Bool)
    (ok_antitone : ∀ s b c, ok (step s b) c = true → ok s c = true)
    (recur_sound : ∀ s candidates chosen,
      recur s candidates = true → chosen.Sublist candidates →
        validTrace ok step s chosen = true → good (chosen.foldl step s) = true)
    (s : σ) (candidates chosen : List α)
    (hbranches : branches ok step recur s candidates = true)
    (hsub : chosen.Sublist candidates) (hne : chosen ≠ [])
    (hvalid : validTrace ok step s chosen = true) :
    good (chosen.foldl step s) = true := by
  induction candidates generalizing chosen with
  | nil => exact False.elim (hne (List.eq_nil_of_sublist_nil hsub))
  | cons b bs ih =>
    simp only [branches, Bool.and_eq_true] at hbranches
    cases hsub with
    | cons _ hsub => exact ih chosen hbranches.2 hsub hne hvalid
    | cons_cons _ hsub =>
      rename_i chosen
      simp only [validTrace, Bool.and_eq_true] at hvalid
      have hi : recur (step s b) (bs.filter (ok (step s b))) = true := by
        simpa [hvalid.1] using hbranches.1
      have hf : chosen.filter (ok (step s b)) = chosen := by
        apply List.filter_eq_self.2
        exact validTrace_ok ok step ok_antitone (step s b) chosen hvalid.2
      have hs : chosen.Sublist (bs.filter (ok (step s b))) := by
        rw [← hf]
        exact hsub.filter (ok (step s b))
      exact recur_sound (step s b) (bs.filter (ok (step s b))) chosen hi hs hvalid.2

lemma check_sound (ok : σ → α → Bool) (step : σ → α → σ)
    (good : σ → Bool) (prune : σ → List α → Bool)
    (ok_antitone : ∀ s b c, ok (step s b) c = true → ok s c = true)
    (prune_sound : ∀ s candidates chosen,
      prune s candidates = true → chosen.Sublist candidates →
        validTrace ok step s chosen = true → good (chosen.foldl step s) = true)
    (fuel : Nat) (s : σ) (candidates chosen : List α)
    (hcheck : check ok step good prune fuel s candidates = true)
    (hsub : chosen.Sublist candidates)
    (hvalid : validTrace ok step s chosen = true) :
    good (chosen.foldl step s) = true := by
  induction fuel generalizing s candidates chosen with
  | zero =>
    simp only [check, Bool.and_eq_true, List.isEmpty_iff] at hcheck
    rw [hcheck.2] at hsub
    have hc := List.eq_nil_of_sublist_nil hsub
    simpa [hc] using hcheck.1
  | succ fuel ih =>
    by_cases hp : prune s candidates = true
    · exact prune_sound s candidates chosen hp hsub hvalid
    · have hb : good s = true ∧
          branches ok step (check ok step good prune fuel) s candidates = true := by
        simpa [check, hp, Bool.and_eq_true] using hcheck
      by_cases hc : chosen = []
      · simpa [hc] using hb.1
      · exact branches_sound ok step good (check ok step good prune fuel)
          ok_antitone ih s candidates chosen hb.2 hsub hc hvalid

end PackingPrunedDFS

end PEqualNP.Outside.L_meta_1896_aux
