import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4622_314
    (erase : ∀ (n : ℕ) (d : Circuit) (f : (Fin n → Bool) → Bool), FanInTwo d →
      (∃ x y, f x ≠ f y) → (∀ x, d.eval (true :: List.ofFn x) = f x) →
      ∃ c : Circuit, FanInTwo c ∧ circuitFun n c = f ∧
        c.size + (d.gates.filter (fun (g : Gate) => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains 0)).length ≤ d.size)
    (faces : let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10));
    ∀ (k : Bool) (c : Circuit), FanInTwo c → circuitFun 7 c = (fun (x : Fin 7 → Bool) => F x || cond k (x 0 || x 3) (x 2)) →
      (cond k 7 9) ≤ c.size)
    (finite : let G := fun (k : Option Bool) (g : GateOp × List (ℕ × Bool × Bool)) => Gate.mk g.1 (g.2.map fun v => Option.elim k v.1 (fun b => cond (cond b v.2.2 v.2.1) 0 (v.1+1)));
    let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10));
    ∀ (p : List (GateOp × List (ℕ × Bool × Bool))) (o : ℕ) (a b : Bool → ℕ),
      let C := fun k => (⟨p.map (G k),o + (k.isSome.toNat)⟩ : Circuit);
      p.length = 11 → FanInTwo (C none) →
      (∀ k g, g ∈ p → ∀ v ∈ g.2, (cond k v.2.2 v.2.1) = true → v.1 = a k ∨ v.1 = b k) →
      circuitFun 7 (C none) = F →
      (∀ k : Bool, ((C (some k)).gates.filter (fun (g : Gate) => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains 0)).length ≤ cond k 4 2 ∧
        ∀ x, (C (some k)).eval (true :: List.ofFn x) = (F x || cond k (x 0 || x 3) (x 2))) → False) :
    have x1 : Option Bool → PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool) → PEqualNP.CircuitLowerBounds.Gate := fun (x1 : Option Bool) (x2 : PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool)) => { op := x2.1, inputs := List.map (fun (x3 : ℕ × Bool × Bool) => x1.elim x3.1 fun (x4 : Bool) => bif bif x4 then x3.2.2 else x3.2.1 then (0 : ℕ) else x3.1 + (1 : ℕ)) x2.2 : PEqualNP.CircuitLowerBounds.Gate }; have x2 : (Fin (7 : ℕ) → Bool) → Bool := fun (x2 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x3 : ℕ) => x2 (Fin.ofNat (7 : ℕ) (x3 / (10 : ℕ))) && x2 (Fin.ofNat (7 : ℕ) (x3 % (10 : ℕ))); ∀ (x3 : List (PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool))) (x4 : ℕ) (x5 x6 : Bool → ℕ), x3.length = (11 : ℕ) → x4 < (18 : ℕ) → PEqualNP.MetaComplexity.FanInTwo { gates := List.map (x1 Option.none) x3, output := x4 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x10 : Bool), ∀ x11 ∈ x3, ∀ x13 ∈ x11.2, x13.1 ≤ (18 : ℕ) ∧ ((bif x10 then x13.2.2 else x13.2.1) = Bool.true → x13.1 = x5 x10 ∨ x13.1 = x6 x10)) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) { gates := List.map (x1 Option.none) x3, output := x4 : PEqualNP.CircuitLowerBounds.Circuit } = x2 → (∀ (x12 : Bool) (x13 : Fin (7 : ℕ) → Bool), { gates := List.map (x1 (Option.some x12)) x3, output := x4 + (1 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (Bool.true :: List.ofFn x13) = (x2 x13 || bif x12 then x13 (0 : Fin (7 : ℕ)) || x13 (3 : Fin (7 : ℕ)) else x13 (2 : Fin (7 : ℕ)))) → False := by
  let G := fun (k : Option Bool) (g : GateOp × List (ℕ × Bool × Bool)) =>
      Gate.mk g.1 (g.2.map fun v => Option.elim k v.1 (fun b => cond (cond b v.2.2 v.2.1) 0 (v.1+1)))
  let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e =>
      x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  intro _ _ p o a b sz hout fan marks base restore
  apply finite p o a b sz fan (fun k g hg v hv h => (marks k g hg v hv).2 h) base
  intro k
  let d : Circuit := ⟨p.map (G (some k)),o+1⟩
  let f := fun (x : Fin 7 → Bool) => F x || cond k (x 0 || x 3) (x 2)
  have df : FanInTwo d := by
    intro g mem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp mem
    have h := fan (G none v) (List.mem_map.mpr ⟨v,hv,rfl⟩)
    simpa [G] using h
  have varying : ∃ x y, f x ≠ f y := by
    refine ⟨fun _ => false,fun _ => true,?_⟩
    cases k <;> decide +kernel
  obtain ⟨small,hfan,calcF,saving⟩ := erase 7 d f df varying (restore k)
  have lower := faces k small hfan calcF
  have length : d.size = 11 := by
    change (p.map (G (some k))).length = 11
    rw [List.length_map,sz]
  refine ⟨?_,restore k⟩
  change (d.gates.filter _).length ≤ cond k 4 2
  cases k <;> simp only [Bool.cond_false, Bool.cond_true] at lower ⊢ <;> omega
