import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6210_2
    (supportBound :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        a < 26 + C.size → b < 26 + C.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
          { gates := C.gates, output := a } →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
          { gates := C.gates, output := b } →
        (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
          PEqualNP.LowMerge.wireVal C
            (PEqualNP.GenericRejection.incidenceInput Q
              (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) a = false ∨
          PEqualNP.LowMerge.wireVal C
            (PEqualNP.GenericRejection.incidenceInput Q
              (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) b = false) →
        50 ≤ max a b ∧ ∃ w ∈ [a, b], ∀ i : Fin 26, ∃ x : Fin 26 → Bool,
          PEqualNP.LowMerge.wireVal C (List.ofFn x) w = false ∧
          PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update x i true)) w = true)
    (lower :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        a < 26 + C.size → b < 26 + C.size →
        (let V := fun (w : ℕ) (Q : Finset (Fin 13)) =>
          PEqualNP.LowMerge.wireVal C
            (PEqualNP.GenericRejection.incidenceInput Q
              (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) w
         let E := fun (w : ℕ) => Finset.univ.filter (fun e : Fin 13 × Fin 13 =>
           e.1 ∉ PEqualNP.HeptadCover.singerLines3 e.2 ∧
           PEqualNP.LowMerge.wireVal C (PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}) w = true)
         (E a).card ≤ 12 →
         PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
           { gates := C.gates, output := a } →
         PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
           { gates := C.gates, output := b } →
         (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
           V a Q = false ∨ V b Q = false) →
         (∃ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q ∧
           V a Q = false ∧ V b Q = true) →
         (∃ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q ∧
           V b Q = false ∧ V a Q = true) →
         (50 ≤ max a b ∧ ∃ w ∈ [a, b], ∀ i : Fin 26, ∃ x : Fin 26 → Bool,
           PEqualNP.LowMerge.wireVal C (List.ofFn x) w = false ∧
           PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update x i true)) w = true) →
         63 ≤ C.size)) :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      (let V := fun (w : ℕ) (Q : Finset (Fin 13)) =>
        PEqualNP.LowMerge.wireVal C
          (PEqualNP.GenericRejection.incidenceInput Q
            (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) w
       let E := fun (w : ℕ) => Finset.univ.filter (fun e : Fin 13 × Fin 13 =>
         e.1 ∉ PEqualNP.HeptadCover.singerLines3 e.2 ∧
         PEqualNP.LowMerge.wireVal C (PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}) w = true)
       (E a).card ≤ 12 →
       PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
         { gates := C.gates, output := a } →
       PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
         { gates := C.gates, output := b } →
       (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
         V a Q = false ∨ V b Q = false) →
       (∃ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q ∧
         V a Q = false ∧ V b Q = true) →
       (∃ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q ∧
         V b Q = false ∧ V a Q = true) →
       63 ≤ C.size) := by
  intro C a b mono back ha hb
  dsimp only
  intro leak rightA rightB safe witnessA witnessB
  exact lower C a b mono back ha hb leak rightA rightB safe witnessA witnessB
    (supportBound C a b mono back ha hb rightA rightB safe)
