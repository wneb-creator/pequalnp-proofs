import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_6068_487
    (crossing : ∀ (n : ℕ) (C : Circuit), TopForm.IsAO2 n C →
      ∀ (x y : Fin n → Bool) (start : ℕ),
      let V := ReadTwo.wval C x
      let Y := ReadTwo.wval C y
      let E := fun a b => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧
        b = n+j ∧ a ∈ g.inputs ∧ V a = true ∧ V b = true
      Relation.ReflTransGen E start C.output → Y start = true → Y C.output = false →
      ∃ j, start < n+j ∧ Relation.ReflTransGen E start (n+j) ∧ Relation.ReflTransGen E (n+j) C.output ∧
        ReadTwo.isAnd C j ∧ V (n+j) = true ∧
        (∃ a ∈ (NestedCover.gateAt C j).inputs, Y a = true) ∧
        (∃ b ∈ (NestedCover.gateAt C j).inputs, Y b = false))
    (exclude : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      ReadK.lineSingle C 26 (fun i => decide (i=13)) 0 13 = false →
      ReadK.lineSingle C 26 (fun i => decide (i=0)) 13 0 = false →
      let V := fun S : Finset ℕ => ReadTwo.wval C (ReadTwo.indW 26 S)
      let I := fun j => (NestedCover.gateAt C j).inputs
      let P := Relation.ReflTransGen (fun a b : ℕ => ∃ i : ℕ, b=26+i ∧ a ∈ I i)
      let A := ReadTwo.isAnd C
      ∀ s t : ℕ, (s=0 ∧ t=13 ∨ s=13 ∧ t=0) →
        ¬ ∃ j k m : ℕ, j ≠ k ∧ j < m ∧ k ≠ m ∧ P (26+j) (26+m) ∧ P (26+m) C.output ∧ P (26+k) C.output ∧ A j ∧ A k ∧ A m ∧
          V {s} (26+j) = true ∧ V {t} (26+k) = false ∧
          (∀ a ∈ I j, V {0,13} a = true ∧ V {t} a = false) ∧
          (∀ a ∈ I k, V {0,13} a = true ∧ V {s} a = false) ∧
          V {0,13} (26+m) = true ∧ (∃ a ∈ I m, V {s} a = true) ∧ (∃ b ∈ I m, V {s} b = false)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) ≠ x9 {(0 : ℕ)} ((26 : ℕ) + x13)) → False := by
  intro C lo hi model distinct exactC singleL singleP V T K witness
  obtain ⟨j,k,jk,hj,hk,ne⟩ := witness
  let E := fun a b => ∃ (i : ℕ) (g : Gate), C.gates[i]? = some g ∧ b=26+i ∧
    a ∈ g.inputs ∧ V {0,13} a = true ∧ V {0,13} b = true
  have edge (a b : ℕ) (h : T a b) : E a b := by
    obtain ⟨i,g,u,v,gi,bi,ins,op,ha,hb⟩ := h
    refine ⟨i,g,gi,bi,?_,ha,hb⟩
    rw [ins]
    rcases op with ⟨_,hu | hv⟩ | ⟨_,he⟩
    · simp [hu]
    · simp [hv]
    · rw [he]
      split <;> simp
  have path {a b : ℕ} (h : Relation.ReflTransGen T a b) : Relation.ReflTransGen E a b := by
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (edge _ _ h)
  let F := fun a b : ℕ => ∃ i : ℕ, b=26+i ∧ a ∈ (NestedCover.gateAt C i).inputs
  have physical {a b : ℕ} (h : Relation.ReflTransGen E a b) : Relation.ReflTransGen F a b := by
    induction h with
    | refl => exact .refl
    | tail _ step ih =>
      obtain ⟨i,g,gi,eq,mem,_,_⟩ := step
      apply ih.tail
      refine ⟨i,eq,?_⟩
      change _ ∈ (C.gates.getD i ⟨.or,[]⟩).inputs
      rw [List.getD_eq_getElem?_getD,gi]
      exact mem
  have empty (s : ℕ) (hs : s=0 ∨ s=13) : V {s} C.output = false := by
    by_contra! nonzero
    have on : C.eval (List.ofFn (ReadTwo.indW 26 {s})) = true := by
      change V {s} C.output = true
      simpa only [Bool.not_eq_false] using nonzero
    have found := (exactC _).mp on
    rcases hs with rfl | rfl
    all_goals revert found; decide +kernel
  have oriented (s t d e : ℕ) (st : (s=0 ∧ t=13) ∨ (s=13 ∧ t=0))
      (de : d ≠ e) (hd : K t d) (he : K s e)
      (hot : V {s} (26+d) = true) (cold : V {t} (26+e) = false) : False := by
    have hs : s=0 ∨ s=13 := st.elim (fun q => Or.inl q.1) (fun q => Or.inr q.1)
    obtain ⟨m,later,down,up,hm,yes,above,below⟩ := crossing 26 C model (ReadTwo.indW 26 {0,13})
      (ReadTwo.indW 26 {s}) (26+d) (path hd.1) hot (empty s hs)
    have em : e ≠ m := by
      intro eq
      subst m
      obtain ⟨a,ha,va⟩ := above
      have zero := (he.2.2 a ha).2
      change V {s} a = true at va
      simp_all
    apply exclude C lo hi model distinct exactC singleL singleP s t st
    exact ⟨d,e,m,de,by omega,em,physical down,physical up,physical (path he.1),hd.2.1,he.2.1,hm,hot,cold,hd.2.2,he.2.2,yes,above,below⟩
  cases a : V {13} (26+j) <;> cases b : V {0} (26+k)
  · exact (ne (a.trans b.symm)).elim
  · exact oriented 0 13 k j (Or.inl ⟨rfl,rfl⟩) jk.symm hk hj b a
  · exact oriented 13 0 j k (Or.inr ⟨rfl,rfl⟩) jk hj hk a b
  · exact (ne (a.trans b.symm)).elim
