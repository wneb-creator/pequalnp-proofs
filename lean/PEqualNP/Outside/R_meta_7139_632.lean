import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover in
theorem PEqualNP.Outside.R_meta_7139_632
  (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ a b : Fin (n + C.size),
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size + 1 ∧
      ∀ w : List Bool, w.length = n →
        D.eval w = ((C.wires w).getD a.val false || (C.wires w).getD b.val false))
  (shape : let S := singerLines3
    let neg (X Y : Finset (Fin 13)) := IsFalseInput S X Y ∧
      ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l)
    let good (C : Circuit) := RightOnIncidentPairs S C ∧
      ∀ X Y, neg X Y → C.eval (incidenceInput X Y) = false
    let hard (C : Circuit) := 2 ≤ andPairs 26 C ∧
      ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → InCone 26 C i j →
        ∃ X Y, neg X Y ∧ (C.wires (incidenceInput X Y)).getD (26+i) false = true
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → C.size ≤ 63 → good C →
      ∃ D : Circuit, IsAO2 26 D ∧ D.size ≤ 63 ∧ good D ∧ hard D)
  (lower : let S := singerLines3
    let neg (X Y : Finset (Fin 13)) := IsFalseInput S X Y ∧
      ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l)
    let good (C : Circuit) := RightOnIncidentPairs S C ∧
      ∀ X Y, neg X Y → C.eval (incidenceInput X Y) = false
    let hard (C : Circuit) := 2 ≤ andPairs 26 C ∧
      ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → InCone 26 C i j →
        ∃ X Y, neg X Y ∧ (C.wires (incidenceInput X Y)).getD (26+i) false = true
    ∀ C : Circuit, IsAO2 26 C → good C → hard C → 64 ≤ C.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     (37 : ℕ) ≤ x3.size →       x3.size ≤ (62 : ℕ) →         ∀ (x7 x8 : Fin ((26 : ℕ) + x3.size)),           x7 ≠ x8 →             (∀ (x10 x11 : Finset (Fin (13 : ℕ))),                 ((∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x10, x2 x13 x12) ∨ ∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x2 x12 x13) →                   have x13 : Fin (26 : ℕ) → Bool := fun (x13 : Fin (26 : ℕ)) => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd (13 : ℕ) x14);                   have x14 : List Bool := x3.wires (List.ofFn x13);                   (x14.getD (↑x7) Bool.false || x14.getD (↑x8) Bool.false) = Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, x2 x15 x16)) →               False) := by
  dsimp only at shape lower ⊢
  intro C hm _ hsize a b _ query
  obtain ⟨D, md, rd, ds, deval⟩ := normalize 26 C hm a b
  let Inc (p l : Fin 13) := ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l + d
  have geom : ∀ p l, p ∈ singerLines3 l ↔ Inc p l := by
    intro p
    fin_cases p <;> decide +kernel
  let row (X Y : Finset (Fin 13)) (u : Fin 26) :=
    decide ((∃ p ∈ X, u = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, u = Fin.natAdd 13 l)
  have eq (X Y : Finset (Fin 13)) : incidenceInput X Y = List.ofFn (row X Y) := by
    change List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) = List.ofFn (row X Y)
    rw [← List.ofFn_fin_append]
    congr 1
    funext u
    refine Fin.addCases (fun p => ?_) (fun l => ?_) u
    · rw [Fin.append_left]
      apply decide_eq_decide.mpr
      constructor
      · intro hp
        exact Or.inl ⟨p,hp,rfl⟩
      · rintro (⟨q,hq,e⟩ | ⟨l,_,e⟩)
        · have pq : p = q := Fin.ext (congrArg (fun x : Fin 26 => x.val) e)
          exact pq.symm ▸ hq
        · have clash := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at clash
          omega
    · rw [Fin.append_right]
      apply decide_eq_decide.mpr
      constructor
      · intro hl
        exact Or.inr ⟨l,hl,rfl⟩
      · rintro (⟨p,_,e⟩ | ⟨q,hq,e⟩)
        · have clash := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at clash
          omega
        · have lq : l = q := by
            apply Fin.ext
            have z := congrArg Fin.val e
            simp only [Fin.val_natAdd] at z
            omega
          exact lq.symm ▸ hq
  have fit X Y
      (h : (∃ l, ∀ p ∈ X, Inc p l) ∨ ∃ p, ∀ l ∈ Y, Inc p l) :
      D.eval (incidenceInput X Y) = decide (∃ p ∈ X, ∃ l ∈ Y, Inc p l) := by
    rw [eq]
    exact (deval _ (by simp)).trans (query X Y h)
  obtain ⟨E, me, es, ef, eh⟩ := shape D md rd (by omega) (by
    constructor
    · intro l p hp
      have inc := (geom p l).mp hp
      rw [fit _ _ (Or.inl ⟨l, fun q hq => (Finset.mem_singleton.mp hq).symm ▸ inc⟩)]
      exact decide_eq_true ⟨p, by simp, l, by simp, inc⟩
    · rintro X Y ⟨off, support⟩
      have tested : (∃ l, ∀ p ∈ X, Inc p l) ∨ ∃ p, ∀ l ∈ Y, Inc p l := by
        rcases support with ⟨l, hl⟩ | ⟨p, hp⟩
        · exact Or.inl ⟨l, fun p h => (geom p l).mp (hl h)⟩
        · exact Or.inr ⟨p, fun l h => (geom p l).mp (hp l h)⟩
      rw [fit X Y tested]
      apply decide_eq_false
      rintro ⟨p, hp, l, hl, inc⟩
      exact (Finset.disjoint_left.mp (off l hl)) ((geom p l).mpr inc) hp)
  have large := lower E me ef eh
  omega
