def orbitWalk (prefer : List Nat → List Nat → Bool)
    (actions : List (Nat → Nat)) (current best : List Nat) : List Nat :=
  match actions with
  | [] => best
  | action :: rest =>
    let candidate := current.map action
    orbitWalk prefer rest candidate (if prefer candidate best then candidate else best)

theorem orbitWalk_run {y : Nat} (prefer : List Nat → List Nat → Bool)
    (actions : List (Nat → Nat))
    (preserved : ∀ action ∈ actions, ∀ {u zs},
      MonRun y u zs → MonRun y u (zs.map action)) :
    ∀ {s current best}, MonRun y s current → MonRun y s best →
      MonRun y s (orbitWalk prefer actions current best) := by
  induction actions with
  | nil =>
    intro s current best hcurrent hbest
    exact hbest
  | cons action rest ih =>
    intro s current best hcurrent hbest
    have hnext := preserved action (by simp) hcurrent
    have htail := ih (fun p hp => preserved p (by simp [hp]))
    change MonRun y s (orbitWalk prefer rest (current.map action)
      (if prefer (current.map action) best then current.map action else best))
    split
    · exact htail hnext hnext
    · exact htail hnext hbest

def qGrayOrbit (routes : List (List (Nat × Nat))) (ws : List Nat) : List Nat :=
  orbitWalk qPrefer (routes.map routeStages) ws ws

def qGrayGood (y : Nat) (routes : List (List (Nat × Nat))) : Bool :=
  routes.all fun ps => validStages ps && (routeStages ps y == y)

theorem qGrayOrbit_run {y s : Nat} {ws : List Nat}
    {routes : List (List (Nat × Nat))}
    (h : MonRun y s ws) (hgood : qGrayGood y routes = true) :
    MonRun y s (qGrayOrbit routes ws) := by
  apply orbitWalk_run qPrefer (routes.map routeStages) ?_ h h
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨ps,hps,rfl⟩
  have hp := List.all_eq_true.1 hgood ps hps
  have hv := (Bool.and_eq_true.1 hp).1
  have hy : routeStages ps y = y := by
    simpa only [beq_iff_eq] using (Bool.and_eq_true.1 hp).2
  exact routeStages_run hz ps hv hy
