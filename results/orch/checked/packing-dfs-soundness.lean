import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingDFS

variable {α σ : Type}

def check (ok : σ → α → Bool) (step : σ → α → σ) (good : σ → Bool) :
    Nat → σ → List α → Bool
  | 0, s, bs => good s && bs.isEmpty
  | _ + 1, s, [] => good s
  | f + 1, s, b :: bs =>
      good s && check ok step good f s bs &&
        (if ok s b then check ok step good f (step s b) (bs.filter (ok (step s b))) else true)

def validTrace (ok : σ → α → Bool) (step : σ → α → σ) : σ → List α → Bool
  | _, [] => true
  | s, b :: bs => ok s b && validTrace ok step (step s b) bs

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

lemma check_sound (ok : σ → α → Bool) (step : σ → α → σ) (good : σ → Bool)
    (ok_antitone : ∀ s b c, ok (step s b) c = true → ok s c = true)
    (fuel : Nat) (s : σ) (candidates chosen : List α)
    (hcheck : check ok step good fuel s candidates = true)
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
    cases candidates with
    | nil =>
      have hc := List.eq_nil_of_sublist_nil hsub
      simpa [hc, check] using hcheck
    | cons b bs =>
      simp only [check, Bool.and_eq_true] at hcheck
      cases hsub with
      | cons _ hsub => exact ih s bs chosen hcheck.1.2 hsub hvalid
      | cons_cons _ hsub =>
        rename_i chosen
        simp only [validTrace, Bool.and_eq_true] at hvalid
        have hi : check ok step good fuel (step s b) (bs.filter (ok (step s b))) = true := by
          simpa [hvalid.1] using hcheck.2
        have hf : chosen.filter (ok (step s b)) = chosen := by
          apply List.filter_eq_self.2
          exact validTrace_ok ok step ok_antitone (step s b) chosen hvalid.2
        have hs : chosen.Sublist (bs.filter (ok (step s b))) := by
          rw [← hf]
          exact hsub.filter (ok (step s b))
        exact ih (step s b) (bs.filter (ok (step s b))) chosen hi hs hvalid.2

end PEqualNP.Outside.L_meta_1896_aux.PackingDFS
