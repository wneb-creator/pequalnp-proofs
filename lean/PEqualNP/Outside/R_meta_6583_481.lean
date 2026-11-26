import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_6583_481
  (coverWire : ∀ (C : Circuit) (i j : Fin 28) (q : Nat), FanInTwo C → C.size=18 →
    15 ≤ C.gates.countP (fun g => !g.op.eval [false]) →
    q ∈ ([907,822,621,469,250] : List Nat) →
    let W := fun (k : Fin 28) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD k.val false
    let A := (fun (q : Nat) (x : Fin 10 → Bool) => decide (∃ v : Fin 10, q.testBit v.val=true ∧ x v=true)) q
    W i = A → IncompRel (·≤·) A (W j) → (fun x => A x && W j x) ≠ (fun x : Fin 10 → Bool => (List.finRange 5).any fun t =>
        (x (Fin.castAdd 5 t) && (x (Fin.castAdd 5 (t+1)) || x (Fin.natAdd 5 t))) ||
          (x (Fin.natAdd 5 t) && x (Fin.natAdd 5 (t+2)))))
  (widePair : ∀ (C : Circuit) (i j : Fin 28), FanInTwo C → C.size=18 →
    15 ≤ C.gates.countP (fun g => !g.op.eval [false]) →
    let W := fun (k : Fin 28) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD k.val false
    let large := fun k => ¬ ∃ s : Finset (Fin 10), s.card ≤ 6 ∧ ∀ x y, (∀ v ∈ s, x v=y v) → W k x=W k y
    15 ≤ i.val → i < j → large i → large j → IncompRel (·≤·) (W i) (W j) →
    (fun x => W i x && W j x) ≠ (fun x : Fin 10 → Bool => (List.finRange 5).any fun t =>
        (x (Fin.castAdd 5 t) && (x (Fin.castAdd 5 (t+1)) || x (Fin.natAdd 5 t))) ||
          (x (Fin.natAdd 5 t) && x (Fin.natAdd 5 (t+2))))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (28 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (18 : ℕ) →       (15 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) x2.gates →         have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8)).getD x9 Bool.false;         (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 ↑x3 = Bool.true ∧ x8 x9 ↑x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 ↑x3 = Bool.false ∧ x8 x10 ↑x4 = Bool.true) → ¬∀ (x11 : Fin (10 : ℕ) → Bool), (x8 x11 ↑x3 && x8 x11 ↑x4) = x1 x11 := by
  intro F0 C a b fan sz flags W0 ab ba meet
  let E := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10))
  let F : (Fin 10 → Bool) → Bool := fun x => E.any (fun e => x e.1 && x e.2)
  let O := fun (q : Nat) (x : Fin 10 → Bool) => decide (∃ v : Fin 10, q.testBit v.val=true ∧ x v=true)
  let Controls := fun (g : (Fin 10 → Bool) → Bool) (s : Finset (Fin 10)) => ∀ x y, (∀ v ∈ s, x v = y v) → g x = g y
  let Q : Nat → Finset (Fin 10) := fun q => Finset.univ.filter (fun v => q.testBit v.val = true)
  have hgraph : ∀ S : Finset (Fin 10), S.card ≤ 6 → F (fun v => decide (v ∉ S)) = false →
      (∃ q ∈ ([907, 822, 621, 469, 250] : List Nat), S = Q q) ∧
      (∀ v ∈ S, F (fun u => decide (u ∉ S) || decide (u = v)) = true) := by
    dsimp [F, E, Q]
    decide
  have F_mono : ∀ x y : Fin 10 → Bool,
      (∀ v, x v = true → y v = true) → F x = true → F y = true := by
    intro x y hxy hx
    change List.any E (fun e => x e.1 && x e.2) = true at hx
    change List.any E (fun e => y e.1 && y e.2) = true
    obtain ⟨e, he, h⟩ := List.any_eq_true.mp hx
    rw [Bool.and_eq_true] at h
    refine List.any_eq_true.mpr ⟨e, he, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨hxy _ h.1, hxy _ h.2⟩
  have rigid : ∀ W S, Controls W S → S.card ≤ 6 →
      (∀ x, F x = true → W x = true) → (∃ x, W x = false) →
      ∃ q : Nat, q ∈ ([907, 822, 621, 469, 250] : List Nat) ∧ W = O q := by
    intro W S hcontrols hcard hdom hfalse
    obtain ⟨z, hz⟩ := hfalse
    let completion : (Fin 10 → Bool) → Fin 10 → Bool :=
      fun x v => if v ∈ S then x v else true
    have hcomp : ∀ x, W x = W (completion x) := by
      intro x
      exact hcontrols x (completion x) (fun v hv => by simp [completion, hv])
    have hcover : F (fun v => decide (v ∉ S)) = false := by
      cases hf : F (fun v => decide (v ∉ S))
      · rfl
      · have h := F_mono _ (completion z) (fun v hv => by
          have hnot : v ∉ S := of_decide_eq_true hv
          simp [completion, hnot]) hf
        have he := hcomp z
        simp [hz, hdom _ h] at he
    obtain ⟨⟨q, hq, hS⟩, hforce⟩ := hgraph S hcard hcover
    have hmem : ∀ v : Fin 10, v ∈ S ↔ q.testBit v.val = true := by
      intro v
      rw [hS]
      simp [Q]
    have hpositive : ∀ x, O q x = true → W x = true := by
      intro x hx
      change decide (∃ v : Fin 10, q.testBit v.val = true ∧ x v = true) = true at hx
      obtain ⟨v, hbit, hv⟩ := of_decide_eq_true hx
      have hs := (hmem v).mpr hbit
      rw [hcomp x]
      apply hdom
      refine F_mono (fun u => decide (u ∉ S) || decide (u = v)) (completion x) ?_ (hforce v hs)
      intro u hu
      change (decide (u ∉ S) || decide (u = v)) = true at hu
      rw [Bool.or_eq_true] at hu
      rcases hu with hnot | heq
      · have hnotS : u ∉ S := of_decide_eq_true hnot
        simp [completion, hnotS]
      · have huv : u = v := of_decide_eq_true heq
        subst u
        simp [completion, hs, hv]
    have hzeros : ∀ x, O q x = false → ∀ v ∈ S, x v = false := by
      intro x hx v hv
      cases hval : x v
      · rfl
      · have h : O q x = true := by
          change decide (∃ u : Fin 10, q.testBit u.val = true ∧ x u = true) = true
          exact decide_eq_true ⟨v, (hmem v).mp hv, hval⟩
        simp [hx] at h
    have hzero : O q z = false := by
      cases ho : O q z
      · rfl
      · have he := hpositive z ho
        simp [hz] at he
    refine ⟨q, hq, funext (fun x => ?_)⟩
    cases hx : O q x
    · exact (hcontrols x z (fun v hv => (hzeros x hx v hv).trans (hzeros z hzero v hv).symm)).trans hz
    · exact hpositive x hx

  classical
  let run (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have other (x : List Bool) (b : Bool) (i : ℕ) (h : i ≠ x.length) :
      (x ++ [b]).getD i false = x.getD i false := by
    by_cases lt : i < x.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have cone (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
      (n : ℕ) (T : Finset ℕ) :
      ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ j ∈ T, (run gs x).getD j false = (run gs y).getD j false := by
    induction gs generalizing n T with
    | nil => exact ⟨T,by simp,fun _ _ _ _ h => h⟩
    | cons g gs ih =>
      obtain ⟨S,small,protect⟩ := ih (fun u hu => arity u (by simp [hu])) (n+1) T
      let value (x : List Bool) := g.op.eval (g.inputs.map fun i => x.getD i false)
      by_cases used : n ∈ S
      · let R := S.erase n ∪ g.inputs.toFinset
        refine ⟨R,?_,?_⟩
        · have h := Finset.card_union_le (S.erase n) g.inputs.toFinset
          have ea := Finset.card_erase_add_one used
          have inputs := List.toFinset_card_le g.inputs
          have two := arity g (by simp)
          change (S.erase n ∪ g.inputs.toFinset).card ≤ T.card + (g :: gs).length
          simp only [List.length_cons]
          omega
        · intro x y hx hy agree
          apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
          intro j hj
          by_cases split : j = n
          · subst j
            have val : value x = value y := by
              apply congrArg g.op.eval
              apply List.map_congr_left
              intro i hi
              exact agree i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
            have atEnd (z : List Bool) (b : Bool) : (z ++ [b]).getD z.length false = b := by simp
            calc
              (x ++ [value x]).getD n false = value x := hx ▸ atEnd x _
              _ = value y := val
              _ = (y ++ [value y]).getD n false := hy ▸ (atEnd y _).symm
          · rw [other x _ j (by omega),other y _ j (by omega)]
            exact agree j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨split,hj⟩))
      · refine ⟨S,by simp only [List.length_cons]; omega,?_⟩
        intro x y hx hy agree
        apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
        intro j hj
        have diff : j ≠ n := fun h => used (h ▸ hj)
        rw [other x _ j (by omega),other y _ j (by omega)]
        exact agree j hj

  have runLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp
      omega

  have preserve (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (run gs w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD j false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hj]

  have prefixWire (C : Circuit) (x : List Bool) (hx : x.length = 10) (j : ℕ) (hj : j ≤ 14) :
      (C.wires x).getD j false = (run (C.gates.take 5) x).getD j false := by
    by_cases hsize : C.gates.length ≤ 5
    · have ht : C.gates.take 5 = C.gates := (List.take_eq_self_iff _).mpr hsize
      change (run C.gates x).getD j false = _
      rw [ht]
    · have hb : j < (run (C.gates.take 5) x).length := by
        rw [runLength, hx, List.length_take]
        omega
      have hs : C.gates.take 5 ++ C.gates.drop 5 = C.gates := List.take_append_drop _ _
      change (run C.gates x).getD j false = _
      calc
        (run C.gates x).getD j false = (run (C.gates.take 5 ++ C.gates.drop 5) x).getD j false :=
          congrArg (fun gs => (run gs x).getD j false) hs.symm
        _ = (run (C.gates.drop 5) (run (C.gates.take 5) x)).getD j false := by
          simp only [run, List.foldl_append]
        _ = _ := preserve (C.gates.drop 5) (run (C.gates.take 5) x) j hb

  have early (C : Circuit) (hc : FanInTwo C) (i : Fin 28) (hi : i.val ≤ 14) :
      ∃ S : Finset (Fin 10), S.card ≤ 6 ∧ ∀ x y : Fin 10 → Bool,
        (∀ v ∈ S, x v = y v) →
        (C.wires (List.ofFn x)).getD i.val false = (C.wires (List.ofFn y)).getD i.val false := by
    have arity : ∀ g ∈ C.gates.take 5, g.inputs.length ≤ 2 := by
      intro g hg
      exact (hc g (List.mem_of_mem_take hg)).2
    obtain ⟨T, hT, hdep⟩ := cone (C.gates.take 5) arity 10 {i.val}
    let S : Finset (Fin 10) := Finset.univ.filter (fun v => v.val ∈ T)
    have hsub : S.image Fin.val ⊆ T := by
      intro k hk
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_filter.mp hv).2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
    refine ⟨S, ?_, ?_⟩
    · simp only [Finset.card_singleton, List.length_take] at hT
      omega
    · intro x y agree
      rw [prefixWire C (List.ofFn x) (by simp) i.val hi,
          prefixWire C (List.ofFn y) (by simp) i.val hi]
      apply hdep (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ i.val (by simp)
      intro k hk
      by_cases h : k < 10
      · rw [List.getD_eq_getElem (List.ofFn x) _ (by simpa using h),
          List.getD_eq_getElem (List.ofFn y) _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact agree ⟨k, h⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

  let W := fun (k : Fin 28) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD k.val false
  let shortF := (fun x : Fin 10 → Bool => (List.finRange 5).any fun t =>
        (x (Fin.castAdd 5 t) && (x (Fin.castAdd 5 (t+1)) || x (Fin.natAdd 5 t))) ||
          (x (Fin.natAdd 5 t) && x (Fin.natAdd 5 (t+2))))
  have f0 : F0=F := by funext x; simp only [F0,F,E,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  have shortEq : F=shortF := by
    change (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) = (fun x : Fin 10 → Bool => (List.finRange 5).any fun t =>
        (x (Fin.castAdd 5 t) && (x (Fin.castAdd 5 (t+1)) || x (Fin.natAdd 5 t))) ||
          (x (Fin.natAdd 5 t) && x (Fin.natAdd 5 (t+2))))
    funext x
    have concrete : ∀ y : Fin 10 → Bool, ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e=>y e.1 && y e.2) = ((fun x : Fin 10 → Bool => (List.finRange 5).any fun t =>
        (x (Fin.castAdd 5 t) && (x (Fin.castAdd 5 (t+1)) || x (Fin.natAdd 5 t))) ||
          (x (Fin.natAdd 5 t) && x (Fin.natAdd 5 (t+2))))) y := by decide +kernel
    exact concrete x
  have pairEq (x) : (W a x && W b x)=F x := (meet x).trans (congrFun f0 x)
  have dom (x) (h : F x=true) : W a x=true ∧ W b x=true := by
    simpa only [Bool.and_eq_true] using (pairEq x).trans h
  obtain ⟨x,ax,bx⟩:=ab
  obtain ⟨y,ay,byy⟩:=ba
  have incomparable : IncompRel (·≤·) (W a) (W b) := by
    constructor
    · intro h
      have z : W b x=true := Bool.le_iff_imp.mp (h x) ax
      change W b x=false at bx
      exact Bool.noConfusion (bx.symm.trans z)
    · intro h
      have z : W a y=true := Bool.le_iff_imp.mp (h y) byy
      change W a y=false at ay
      exact Bool.noConfusion (ay.symm.trans z)
  have meetEq : (fun x=>W a x && W b x)=shortF := funext (fun t=>(pairEq t).trans (congrFun shortEq t))
  have reverseEq : (fun x=>W b x && W a x)=shortF := funext (fun t=>(Bool.and_comm _ _).trans (congrFun meetEq t))
  let small (i : Fin 28) := ∃s : Finset (Fin 10),s.card≤6 ∧ Controls (W i) s
  by_cases sa : small a
  · obtain ⟨s,szS,ctl⟩:=sa
    obtain ⟨q,hq,heq⟩:=rigid (W a) s ctl szS (fun t h => (dom t h).1) ⟨y,ay⟩
    have h1 : IncompRel (·≤·) (O q) (W b) := by rw [←heq];exact incomparable
    have h2 : (fun t=>O q t && W b t)=shortF := by rw [←heq];exact meetEq
    exact coverWire C a b q fan sz flags hq heq h1 h2
  by_cases sb : small b
  · obtain ⟨s,szS,ctl⟩:=sb
    obtain ⟨q,hq,heq⟩:=rigid (W b) s ctl szS (fun t h => (dom t h).2) ⟨x,bx⟩
    have inc : IncompRel (·≤·) (W b) (W a) := ⟨incomparable.2,incomparable.1⟩
    have h1 : IncompRel (·≤·) (O q) (W a) := by rw [←heq];exact inc
    have h2 : (fun t=>O q t && W a t)=shortF := by rw [←heq];exact reverseEq
    exact coverWire C b a q fan sz flags hq heq h1 h2
  have late (i : Fin 28) (h : ¬small i) : 15 ≤ i.val := by
    apply Nat.le_of_not_gt
    intro l
    exact h (early C fan i (by omega))
  rcases lt_trichotomy a b with h|h|h
  · exact widePair C a b fan sz flags (late a sa) h sa sb incomparable meetEq
  · subst b;exact incomparable.1 le_rfl
  · exact widePair C b a fan sz flags (late b sb) h sb sa ⟨incomparable.2,incomparable.1⟩ reverseEq
