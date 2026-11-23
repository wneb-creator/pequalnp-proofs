theorem qInsert_perm (a : Nat) (xs : List Nat) : (a :: xs).Perm (qInsert a xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons b xs ih =>
    simp only [qInsert]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.swap _ _ _).trans (List.Perm.cons b ih)

theorem qNorm_perm (xs : List Nat) : xs.Perm (qNorm xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a xs ih =>
    exact (List.Perm.cons a ih).trans (qInsert_perm a (qNorm xs))

def orbitNormWalk (actions : List (Nat → Nat)) (current best : List Nat) : List Nat :=
  match actions with
  | [] => best
  | action :: rest =>
    let candidate := current.map action
    let normalized := qNorm candidate
    orbitNormWalk rest candidate (if qLex normalized best then normalized else best)

theorem orbitNormWalk_run {y : Nat} (actions : List (Nat → Nat))
    (preserved : ∀ action ∈ actions, ∀ {u zs},
      MonRun y u zs → MonRun y u (zs.map action)) :
    ∀ {s current best}, MonRun y s current → MonRun y s best →
      MonRun y s (orbitNormWalk actions current best) := by
  induction actions with
  | nil =>
    intro s current best hcurrent hbest
    exact hbest
  | cons action rest ih =>
    intro s current best hcurrent hbest
    have hnext := preserved action (by simp) hcurrent
    have hnorm := Run.perm (qNorm_perm (current.map action)) hnext
    have htail := ih (fun p hp => preserved p (by simp [hp]))
    change MonRun y s (orbitNormWalk rest (current.map action)
      (if qLex (qNorm (current.map action)) best then qNorm (current.map action) else best))
    split
    · exact htail hnext hnorm
    · exact htail hnext hbest

def qGrayNormOrbit (routes : List (List (Nat × Nat))) (ws : List Nat) : List Nat :=
  orbitNormWalk (routes.map routeStages) ws (qNorm ws)

theorem qGrayNormOrbit_run {y s : Nat} {ws : List Nat}
    {routes : List (List (Nat × Nat))}
    (h : MonRun y s ws) (hgood : qGrayGood y routes = true) :
    MonRun y s (qGrayNormOrbit routes ws) := by
  apply orbitNormWalk_run (routes.map routeStages) ?_ h (Run.perm (qNorm_perm ws) h)
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨ps,hps,rfl⟩
  have hp := List.all_eq_true.1 hgood ps hps
  have hv := (Bool.and_eq_true.1 hp).1
  have hy : routeStages ps y = y := by
    simpa only [beq_iff_eq] using (Bool.and_eq_true.1 hp).2
  exact routeStages_run hz ps hv hy
