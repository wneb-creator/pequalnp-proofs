import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The sixteen-input synthesis hypothesis is L-meta-4243.
-- Projecting the test rows forgets the two auxiliary inputs and reorders the line inputs.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4769_44
  (common : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 ∧       x1.size ≤ (22 : ℕ) ∧         (∀ x2 ∈ [(33 : ℕ), (34 : ℕ), (40 : ℕ), (66 : ℕ), (68 : ℕ), (80 : ℕ), (132 : ℕ), (136 : ℕ), (264 : ℕ), (272 : ℕ), (513 : ℕ), (528 : ℕ), (1026 : ℕ), (2052 : ℕ), (4104 : ℕ), (8208 : ℕ), (16385 : ℕ), (32769 : ℕ), (32772 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x4 : Fin (16 : ℕ)) => x2.testBit ↑x4) = Bool.true) ∧           ∀             x2 ∈               have x3 : List ℕ :=                 have x3 : List ℕ :=                   have x3 : List ℕ := [(56496 : ℕ), (59914 : ℕ), (61000 : ℕ), (64386 : ℕ), (65504 : ℕ)];                   (30500 : ℕ) :: (34842 : ℕ) :: (49178 : ℕ) :: (52248 : ℕ) :: (55442 : ℕ) :: x3;                 have x4 : List ℕ := (20502 : ℕ) :: (21556 : ℕ) :: (24590 : ℕ) :: (26124 : ℕ) :: (29446 : ℕ) :: x3;                 (15809 : ℕ) :: (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: x4;               have x4 : List ℕ :=                 have x4 : List ℕ := (10251 : ℕ) :: (11337 : ℕ) :: (12295 : ℕ) :: (13573 : ℕ) :: (14723 : ℕ) :: x3;                 (7313 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: (8718 : ℕ) :: (9229 : ℕ) :: x4;               have x5 : List ℕ := (4119 : ℕ) :: (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: x4;               (31 : ℕ) :: (1053 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: x5,             (PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x4 : Fin (16 : ℕ)) => x2.testBit ↑x4) = Bool.false)
  (lift : ∀ (n m : ℕ) (p : Fin n → Fin m) (C : Circuit), Monotone2 C →
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
      ∀ x : Fin m → Bool, circuitFun m D x = circuitFun n C (x ∘ p)) :
have x1 : List ℕ → ℕ → Fin (18 : ℕ) → Bool := fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (18 : ℕ)) => (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((18 : ℕ) * (x2 % (3 : ℕ)) + ↑x3); ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (22 : ℕ) ∧ (∀ (x3 : Fin (19 : ℕ)), PEqualNP.MetaComplexity.circuitFun (18 : ℕ) x2 (x1 [(2748787982369 : ℕ), (5497575964738 : ℕ), (35253127217284 : ℕ), (282575027307024 : ℕ), (2252083281805314 : ℕ), (13581476935368968 : ℕ), (204801 : ℕ)] ↑x3) = Bool.true) ∧ ∀ (x3 : Fin (40 : ℕ)), PEqualNP.MetaComplexity.circuitFun (18 : ℕ) x2 (x1 [(150839794335775 : ℕ), (422694713036815 : ℕ), (10135127528966407 : ℕ), (10573287142082581 : ℕ), (13723262631478299 : ℕ), (14075863940142091 : ℕ), (14216052114924046 : ℕ), (14708841020862478 : ℕ), (15160192239357073 : ℕ), (15517191257677852 : ℕ), (16327395760634660 : ℕ), (16879903704853650 : ℕ), (17843491875054616 : ℕ), (262112 : ℕ)] ↑x3) = Bool.false := by
  intro table
  obtain ⟨C, mono, _, size, yes, no⟩ := common
  let p (i : Fin 16) : Fin 18 :=
    Fin.ofNat 18 (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 10, 11, 12, 13, 15] : List ℕ).getD i.val 0)
  let P : List ℕ := [2748787982369, 5497575964738, 35253127217284, 282575027307024, 2252083281805314, 13581476935368968, 204801]
  let N : List ℕ := [150839794335775, 422694713036815, 10135127528966407, 10573287142082581, 13723262631478299, 14075863940142091, 14216052114924046, 14708841020862478, 15160192239357073, 15517191257677852, 16327395760634660, 16879903704853650, 17843491875054616, 262112]
  let ps : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772]
  let ns : List ℕ := [31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504]
  have positive : ∀ j : Fin 19, ∃ q ∈ ps, ∀ i : Fin 16,
      table P j.val (p i) = q.testBit i.val := by
    decide +kernel
  have negative : ∀ j : Fin 40, ∃ q ∈ ns, ∀ i : Fin 16,
      table N j.val (p i) = q.testBit i.val := by
    decide +kernel
  obtain ⟨D, monoD, sizeD, computes⟩ := lift 16 18 p C mono
  refine ⟨D, monoD, sizeD.le.trans size, ?_, ?_⟩
  · intro j
    obtain ⟨q, hq, bits⟩ := positive j
    change circuitFun 18 D (table P j.val) = true
    exact (computes _).trans
      ((congrArg (circuitFun 16 C) (funext bits)).trans (yes q hq))
  · intro j
    obtain ⟨q, hq, bits⟩ := negative j
    change circuitFun 18 D (table N j.val) = false
    exact (computes _).trans
      ((congrArg (circuitFun 16 C) (funext bits)).trans (no q hq))
