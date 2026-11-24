def barBudget (m y : Nat) (cover : Nat → List Nat → Bool) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s+1, i =>
    let ws := S (s+1) i
    !(next m (s+2-ws.length) ws fun zs => cover s zs && !(found S N idx s zs))

theorem barBudget_sound {m y cover S N idx} {s i : Nat}
    (hb : barBudget m y cover S N idx s i = true)
    (hc : ∀ {u ys}, NatRun m y u ys → cover u ys = true)
    (h : NatRun m y s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun m y q (S q j) := by
  cases s with
  | zero => simp [barBudget,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := cover s zs && !(found S N idx s zs)
    have hF (zs) (hz : NatRun m y s zs) : F zs = true := by
      simp only [F,hc hz,Bool.true_and,found]
      simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barBudget_all {m y cover S N idx} {cap : Nat}
    (hc : ∀ {u ys}, NatRun m y u ys → cover u ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, barBudget m y cover S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun m y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barBudget_sound (checked s hs i hi) hc hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_barBudget {m y cover S N idx cap xs}
    (hc : ∀ {u ys}, NatRun m y u ys → cover u ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, barBudget m y cover S N idx s i = true)
    (initial : ∀ s ≤ cap, xs.length ≤ s+1 → found S N idx s xs = true) :
    ∀ s ≤ cap, ¬ NatRun m y s xs := by
  intro s hs hr
  have hi := initial s hs (run_len hr)
  simp only [found,Bool.and_eq_true,decide_eq_true_eq] at hi
  exact barBudget_all hc checked s hs _ hi.1 (Run.perm (List.isPerm_iff.1 hi.2) hr)

