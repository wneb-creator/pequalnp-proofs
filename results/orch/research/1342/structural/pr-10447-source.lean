import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
theorem PEqualNP.Outside.R_meta_5230_619
   (filtered : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g h : Nat),
    NoFourCycle G → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    junk G C={g,h} → InCone n C g h →
    ∃ K : Finset (Fin n),K.card≤2 ∧ ∀u v : Fin n,s(u,v)∈Ustar G C →
      u∈K ∨ v∈K ∨ gateVal n C h (pairInput u v)=true ∧ (u∈wmax G C h ∨ v∈wmax G C h))
   (profile : ∀(G : SimpleGraph (Fin 11)) [DecidableRel G.Adj],
 G=edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e=>(e/11,e % 11))) →
 ∀(U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)),
 IsMinCover (G.deleteEdges ↑U) K → ([16,12,8,5,3,2,1] : List Nat).getD K.card 0≤U.card)
   (charge : ∀(G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h : Nat),
 G=edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e=>(e/11,e % 11))) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → junk G C={g,h} → InCone 11 C g h →
 (∃ K : Finset (Fin 11),K.card≤2 ∧ ∀u v : Fin 11,s(u,v)∈Ustar G C →
      u∈K ∨ v∈K ∨ gateVal 11 C h (pairInput u v)=true ∧ (u∈wmax G C h ∨ v∈wmax G C h)) →
 let U:=(Ustar G C).card
 let Z:=centreless G C
 let T:=(tops G C \ Z).card
 let p:=2*Z.card+(orN G C \ lam G C).card
 4≤U → ([16,12,8,5,3,2,1] : List Nat).getD T 0≤U → 0<p → T+p≤4+U → 22≤C.size) :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False := by
 intro G inst C g h graph least top pair reach
 dsimp only
 intro _ _ small many K covered _ below positive account
 let U:=(Ustar G C).card
 let Z:=centreless G C
 let T:=(tops G C \ Z).card
 let p:=2*Z.card+(orN G C \ lam G C).card
 change T+2*Z.card+(orN G C \ lam G C).card≤C.size+U-17 at account
 change K.card≤T at below
 have nf : NoFourCycle G := by
   subst G
   let es:=(([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e=>(e/11,e % 11)))
   let canonical : DecidableRel (edgeGraph 11 es).Adj := PEqualNP.EdgeOwnership.instDecidableRelFinAdjEdgeGraph 11 es
   have eq : inst=canonical := Subsingleton.elim _ _
   rw [eq]
   decide +kernel
 have bound:=profile G graph (Ustar G C) K covered
 let c:=([16,12,8,5,3,2,1] : List Nat)
 have monotone (i j : Nat) (le : i≤j) : c.getD j 0≤c.getD i 0 := by
   by_cases large : 7≤j
   · rw [List.getD_eq_default c 0 (show c.length≤j from large)]
     omega
   · interval_cases j <;> interval_cases i <;> decide
 have account' : T+p≤4+U := by dsimp only [p];omega
 have low:=charge G C g h graph least top pair reach (filtered 11 G C g h nf least top pair reach)
     many ((monotone K.card T below).trans bound) positive account'
 omega
