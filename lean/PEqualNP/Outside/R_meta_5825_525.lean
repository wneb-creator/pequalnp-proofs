import PEqualNP.Defs
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_5825_525
  (relabel : ∀ (n : ℕ) (p : Fin n → Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size ∧
      ∀ (x : Fin n → Bool) (b : Bool) (w : ℕ),
        (D.wires (List.ofFn x ++ [b])).getD (n+w) false =
        (C.wires (List.ofFn (x ∘ p) ++ [b])).getD (n+w) false)
  (canonical : ∀ (k : Fin 10), k = 1 ∨ k = 2 →
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s t : Fin 18), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
    let G : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (fun (i j : Fin 10) => (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val) i j = true);
    let W := fun (x : (Fin 10 → Bool)) (j : Fin 18) => (C.wires (List.ofFn x ++ [x 0 && x k])).getD (10+j.val) false;
    (∃ x, W x s = true ∧ W x t = false) →
    (∃ x, W x s = false ∧ W x t = true) →
    (∀ x, G x = false → W x s = false ∧ W x t = false) →
    ∃ x, G x = true ∧ W x s = false ∧ W x t = false) :
  ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), x11 x12 ((10 : ℕ) + ↑x4) = Bool.true ∧ x11 x12 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), x11 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x13 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → x11 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x14 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ x11 x15 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x15 ((10 : ℕ) + ↑x5) = Bool.false := by
  let adj : Fin 10 → Fin 10 → Bool := fun (i j : Fin 10) => (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val
  let G : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ adj i j = true)
  let F : (Fin 10 → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ))
  have fun_eq : ∀ x, F x = G x := by decide +kernel
  let table : Array (Array (Fin 10)) := #[#[0,1,2,3,4,5,6,7,8,9],
  #[0,1,2,3,4,5,6,7,8,9],
  #[0,1,2,3,4,5,6,7,8,9],
  #[0,4,3,2,1,5,9,8,7,6],
  #[0,4,3,2,1,5,9,8,7,6],
  #[0,4,3,8,5,1,9,2,6,7],
  #[0,1,6,8,5,4,2,9,3,7],
  #[0,4,3,8,5,1,9,2,6,7],
  #[0,4,9,7,5,1,3,6,2,8],
  #[0,4,9,6,1,5,3,7,8,2],
  #[1,0,4,3,2,6,5,9,8,7],
  #[0,1,2,3,4,5,6,7,8,9],
  #[4,0,1,2,3,9,5,6,7,8],
  #[4,0,1,2,3,9,5,6,7,8],
  #[1,0,4,3,2,6,5,9,8,7],
  #[1,0,4,9,6,2,5,3,7,8],
  #[4,0,5,7,9,3,1,8,2,6],
  #[4,0,1,6,9,3,5,2,8,7],
  #[4,0,5,7,9,3,1,8,2,6],
  #[4,0,5,8,3,9,1,7,6,2],
  #[2,1,0,4,3,7,6,5,9,8],
  #[2,1,0,4,3,7,6,5,9,8],
  #[0,1,2,3,4,5,6,7,8,9],
  #[3,4,0,1,2,8,9,5,6,7],
  #[3,4,0,1,2,8,9,5,6,7],
  #[3,4,0,5,8,2,9,1,7,6],
  #[6,1,0,4,9,8,2,5,3,7],
  #[3,4,0,5,8,2,9,1,7,6],
  #[8,5,0,1,6,3,7,4,2,9],
  #[8,5,0,4,3,6,7,1,9,2],
  #[2,3,4,0,1,7,8,9,5,6],
  #[3,2,1,0,4,8,7,6,5,9],
  #[3,2,1,0,4,8,7,6,5,9],
  #[0,1,2,3,4,5,6,7,8,9],
  #[2,3,4,0,1,7,8,9,5,6],
  #[3,8,5,0,4,2,6,7,1,9],
  #[8,3,4,0,5,6,2,9,1,7],
  #[8,6,1,0,5,3,9,2,4,7],
  #[3,8,5,0,4,2,6,7,1,9],
  #[6,8,5,0,1,9,3,7,4,2],
  #[1,2,3,4,0,6,7,8,9,5],
  #[1,2,3,4,0,6,7,8,9,5],
  #[4,3,2,1,0,9,8,7,6,5],
  #[4,3,2,1,0,9,8,7,6,5],
  #[0,1,2,3,4,5,6,7,8,9],
  #[1,6,8,5,0,2,9,3,7,4],
  #[4,3,8,5,0,9,2,6,7,1],
  #[4,9,7,5,0,3,6,2,8,1],
  #[4,9,6,1,0,3,7,8,2,5],
  #[4,3,8,5,0,9,2,6,7,1],
  #[1,2,3,8,6,0,7,4,5,9],
  #[1,2,3,8,6,0,7,4,5,9],
  #[4,3,2,7,9,0,8,1,5,6],
  #[4,9,7,2,3,0,6,5,1,8],
  #[1,6,8,3,2,0,9,5,4,7],
  #[0,1,2,3,4,5,6,7,8,9],
  #[4,3,8,6,9,0,2,5,1,7],
  #[4,3,2,7,9,0,8,1,5,6],
  #[4,3,8,6,9,0,2,5,1,7],
  #[4,9,6,8,3,0,7,1,5,2],
  #[2,1,6,8,3,7,0,9,5,4],
  #[2,1,6,8,3,7,0,9,5,4],
  #[6,1,2,3,8,9,0,7,4,5],
  #[8,5,7,2,3,6,0,9,1,4],
  #[3,4,9,7,2,8,0,6,5,1],
  #[3,4,9,6,8,2,0,7,1,5],
  #[0,1,2,3,4,5,6,7,8,9],
  #[8,5,7,9,6,3,0,2,4,1],
  #[3,4,9,6,8,2,0,7,1,5],
  #[3,4,9,7,2,8,0,6,5,1],
  #[2,3,4,9,7,1,8,0,6,5],
  #[3,2,1,6,8,4,7,0,9,5],
  #[3,2,1,6,8,4,7,0,9,5],
  #[8,6,1,2,3,5,9,0,7,4],
  #[3,8,5,7,2,4,6,0,9,1],
  #[2,3,4,9,7,1,8,0,6,5],
  #[8,3,4,9,6,5,2,0,7,1],
  #[0,1,2,3,4,5,6,7,8,9],
  #[6,8,5,7,9,1,3,0,2,4],
  #[3,8,5,7,2,4,6,0,9,1],
  #[2,3,8,5,7,1,4,6,0,9],
  #[3,2,7,5,8,4,1,9,0,6],
  #[8,3,2,1,6,5,4,7,0,9],
  #[3,8,6,1,2,4,5,9,0,7],
  #[3,8,6,1,2,4,5,9,0,7],
  #[2,3,8,5,7,1,4,6,0,9],
  #[3,2,7,5,8,4,1,9,0,6],
  #[6,8,3,4,9,1,5,2,0,7],
  #[0,1,2,3,4,5,6,7,8,9],
  #[8,6,9,4,3,5,1,7,0,2],
  #[2,3,8,6,1,7,4,5,9,0],
  #[3,2,7,9,4,8,1,5,6,0],
  #[8,3,2,7,5,6,4,1,9,0],
  #[6,8,3,2,1,9,5,4,7,0],
  #[2,3,8,6,1,7,4,5,9,0],
  #[3,8,6,9,4,2,5,1,7,0],
  #[3,2,7,9,4,8,1,5,6,0],
  #[3,8,6,9,4,2,5,1,7,0],
  #[8,6,9,7,5,3,1,4,2,0],
  #[0,1,2,3,4,5,6,7,8,9]]
  let pick (a b u : Fin 10) : Fin 10 := ((table[10*a.val+b.val]?).getD #[])[u.val]?.getD 0
  have orbit : ∀ a b : Fin 10, a ≠ b →
      (pick a b a = 0 ∧ (pick a b b = 1 ∨ pick a b b = 2) ∧ Function.Injective (pick a b) ∧
      ∀ i j : Fin 10, adj (pick a b i) (pick a b j) = adj i j) := by decide +kernel
  intro a b C s t dif fan size
  obtain ⟨anchor, kinds, inj, preserve⟩ := orbit a b dif
  let φ : Equiv.Perm (Fin 10) := Equiv.ofBijective (pick a b) ⟨inj, Finite.surjective_of_injective inj⟩
  have fixes : φ a = 0 := anchor
  have graph (x : Fin 10 → Bool) : G (x ∘ φ) = G x := by
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨i,j,hi,hj,edge⟩
      exact ⟨φ i,φ j,hi,hj,(preserve i j).trans edge⟩
    · rintro ⟨i,j,hi,hj,edge⟩
      refine ⟨φ.symm i,φ.symm j,by simpa using hi,by simpa using hj,?_⟩
      rw [← preserve]
      change adj (φ (φ.symm i)) (φ (φ.symm j)) = true
      simpa using edge
  let first : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and,[a.val,b.val]⟩],0⟩
  have first_eq (x : Fin 10 → Bool) : first.wires (List.ofFn x) = List.ofFn x ++ [x a && x b] := by
    have get (i : Fin 10) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt)]
      exact List.getElem_ofFn ..
    change List.ofFn x ++ [([(List.ofFn x).getD a.val false,(List.ofFn x).getD b.val false] : List Bool).all id] = _
    rw [get,get]
    simp
  let A := fun (x : Fin 10 → Bool) (j : Fin 18) => (C.wires (first.wires (List.ofFn x))).getD (10+j.val) false
  change (∃ x, A x s = true ∧ A x t = false) → (∃ x, A x s = false ∧ A x t = true) →
    (∀ x, F x = false → A x s = false ∧ A x t = false) → ∃ x, F x = true ∧ A x s = false ∧ A x t = false
  intro hs ht neg
  obtain ⟨D,fanD,sizeD,wire⟩ := relabel 10 φ C fan
  let B := fun (y : Fin 10 → Bool) (j : Fin 18) => (D.wires (List.ofFn y ++ [y 0 && y (φ b)])).getD (10+j.val) false
  have w (y : Fin 10 → Bool) (j : Fin 18) : B y j = A (y ∘ φ) j := by
    simp only [B,A,first_eq,Function.comp_apply,fixes]
    exact wire y _ j.val
  have back (x : Fin 10 → Bool) (j : Fin 18) : B (x ∘ φ.symm) j = A x j := by
    rw [w]
    simp [Function.comp_assoc]
  have cs : ∃ y, B y s = true ∧ B y t = false := by
    obtain ⟨x,xs,xt⟩ := hs
    exact ⟨x ∘ φ.symm,(back x s).trans xs,(back x t).trans xt⟩
  have ct : ∃ y, B y s = false ∧ B y t = true := by
    obtain ⟨x,xs,xt⟩ := ht
    exact ⟨x ∘ φ.symm,(back x s).trans xs,(back x t).trans xt⟩
  have cn : ∀ y, G y = false → B y s = false ∧ B y t = false := by
    intro y hy
    have no := neg (y ∘ φ) ((fun_eq _).trans ((graph y).trans hy))
    exact ⟨(w y s).trans no.1,(w y t).trans no.2⟩
  obtain ⟨y,yes,ys,yt⟩ := canonical (φ b) kinds D s t fanD (by omega) cs ct cn
  exact ⟨y ∘ φ,(fun_eq _).trans ((graph y).trans yes),(w y s).symm.trans ys,(w y t).symm.trans yt⟩
