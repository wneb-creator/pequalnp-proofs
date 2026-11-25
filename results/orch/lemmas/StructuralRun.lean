import FullExtension

namespace PEqualNP.Outside.L_meta_2592.Full

lemma kept_inputs_mem {R : Type} (ka kb : Bool) (a b w : Wire R)
    (rest : List (Wire R)) (hw : w ∈ kept ka a (kept kb b rest)) :
    w ∈ a :: b :: rest := by
  cases ka <;> cases kb <;> simp_all [kept] <;> tauto

lemma Run.rows_agree {R : Type} {u : Bool} {goal : Wire R} {k : Nat}
    {ws : List (Wire R)} (h : Run u goal k ws) (r s : R)
    (agree : ∀ w ∈ ws, w r = w s) : goal r = goal s := by
  induction h using Run.ind with
  | stop => exact agree goal (by simp)
  | perm hp h ih =>
    apply ih
    intro w hw
    exact agree w (hp.mem_iff.mp hw)
  | @two k a b rest op hd ka kb h ih =>
    apply ih
    intro w hw
    rcases List.mem_cons.mp hw with heq | hw
    · subst w
      have ha := agree a (by simp)
      have hb := agree b (by simp)
      unfold comb
      split_ifs <;> simp [combine, inv, ha, hb]
    · exact agree w (kept_inputs_mem ka kb a b w rest hw)

lemma Run.separates {R : Type} {u : Bool} {goal : Wire R} {k : Nat}
    {ws : List (Wire R)} (h : Run u goal k ws) (r s : R)
    (different : goal r ≠ goal s) : ∃ w ∈ ws, w r ≠ w s := by
  by_contra hn
  push_neg at hn
  exact different (Run.rows_agree h r s hn)

end PEqualNP.Outside.L_meta_2592.Full
