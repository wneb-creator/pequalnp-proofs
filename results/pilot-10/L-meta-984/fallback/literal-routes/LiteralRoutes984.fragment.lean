def literalRoutesGood (y : Nat) (routes : List (List (Nat × Nat))) : Bool :=
  routes.all fun r => validStages r && (routeStages r y == y)

def literalRouteOrient (routes : List (List (Nat × Nat))) : List Nat → List Nat :=
  orbitActions qPrefer (routes.map routeStages)

theorem literalRouteOrient_run {y s : Nat} {ws : List Nat}
    (h : MonRun y s ws) (routes : List (List (Nat × Nat)))
    (hg : literalRoutesGood y routes = true) :
    MonRun y s (literalRouteOrient routes ws) := by
  unfold literalRouteOrient
  unfold literalRoutesGood at hg
  apply orbitActions_run h qPrefer
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨r,hr,rfl⟩
  have hrgood := (List.all_eq_true.1 hg) r hr
  simp only [Bool.and_eq_true,beq_iff_eq] at hrgood
  exact routeStages_run hz r hrgood.1 hrgood.2
