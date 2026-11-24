def pairCover (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all fun p => ws.any fun w => decide (w.testBit p.1 ≠ w.testBit p.2)

theorem pairCover_ok {m y s ws} (h : NatRun m y s ws)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, m.testBit p.1 = m.testBit p.2 ∧
      y.testBit p.1 ≠ y.testBit p.2) : pairCover pairs ws = true := by
  apply List.all_eq_true.2
  intro p hp
  apply List.any_eq_true.2
  have hex : ∃ w ∈ ws, w.testBit p.1 ≠ w.testBit p.2 := by
    by_contra! hn
    exact (hpairs p hp).2 (run_bits h p.1 p.2 (hpairs p hp).1 hn)
  obtain ⟨w,hw,hd⟩ := hex
  exact ⟨w,hw,decide_eq_true hd⟩

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def bar (m y : Nat) (cover : List Nat → Bool) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s+1, i =>
    let ws := S (s+1) i
    !(next m (s+2-ws.length) ws fun zs => cover zs && !(found S N idx s zs))

theorem bar_sound {m y cover S N idx} {s i : Nat}
    (hb : bar m y cover S N idx s i = true)
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (h : NatRun m y s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun m y q (S q j) := by
  cases s with
  | zero => simp [bar,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := cover zs && !(found S N idx s zs)
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

theorem bar_all {m y cover S N idx} {cap : Nat}
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, bar m y cover S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun m y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := bar_sound (checked s hs i hi) hc hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_bar {m y cover S N idx cap xs}
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, bar m y cover S N idx s i = true)
    (initial : ∀ s ≤ cap, xs.length ≤ s+1 → found S N idx s xs = true) :
    ∀ s ≤ cap, ¬ NatRun m y s xs := by
  intro s hs hr
  have hi := initial s hs (run_len hr)
  simp only [found,Bool.and_eq_true,decide_eq_true_eq] at hi
  exact bar_all hc checked s hs _ hi.1 (Run.perm (List.isPerm_iff.1 hi.2) hr)

theorem encoded_exclusion {n : Nat} (f : BFn n)
    (hnc : ∃ x x' : Fin n → Bool, f x ≠ f x') (cap : Nat)
    (rows xs : List Nat) (m y : Nat) (cover : List Nat → Bool)
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (hinputs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hmask : m = 2^rows.length-1) (hgoal : encL f rows = y)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → cover zs = false)
    (hno : ∀ s ≤ cap, ¬ NatRun m y s xs) : ¬ HasCircuitSize n f cap := by
  intro h
  obtain ⟨s,hs,ws,hsub,hrun⟩ := exists_run f hnc cap h
  have hr : NatRun m (encL f rows) s (ws.map (fun a => encL a rows)) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hz : (ws.map (fun a => encL a rows)).Sublist xs := by
    rw [← hinputs]
    exact hsub.map _
  by_cases he : ws.map (fun a => encL a rows) = xs
  · rw [he] at hr
    exact hno s hs hr
  · have hp := hproper _ (List.mem_sublists.2 hz) he
    rw [hc hr] at hp
    contradiction
