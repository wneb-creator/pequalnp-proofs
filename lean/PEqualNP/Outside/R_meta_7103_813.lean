import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_7103_813
    (meetStart :
      let V := Fin 10
      let W := (V → Bool) → Bool
      let E : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
      let I (i : Fin 11) : W := if h : i.val < 10 then (fun x => x ⟨i.val,h⟩) else (fun x => x 0 || x 1)
      let B : List W := (fun _ => false) :: (fun _ => true) :: List.ofFn I
      ∀ i j : Fin 11, (i,j) ∈ ([(0,1),(1,2),(2,3),(2,10),(3,8),(3,10)] : List (Fin 11 × Fin 11)) →
      let g : W := fun x => I i x && I j x
      g ∉ B →
      ∀ L : List W, L.length ≤ 17 →
        (∀ k : Fin L.length, let A := (B ++ [g]) ++ L.take k.val
          L.get k ∉ A ∧ ∃ u ∈ A, ∃ v ∈ A, L.get k = (fun x => u x && v x) ∨ L.get k = (fun x => u x || v x)) →
        (∀ w ∈ g :: L, ∀ a b : V, a ≠ b →
          ¬ (E.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = true → w ≠ (fun x => x a && x b)) →
        (fun x => E.any fun e => x e.1 && x e.2) ∉ g :: L)
    (joinStart :
      let V := Fin 10
      let W := (V → Bool) → Bool
      let E : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
      let I (i : Fin 11) : W := if h : i.val < 10 then (fun x => x ⟨i.val,h⟩) else (fun x => x 0 || x 1)
      let B : List W := (fun _ => false) :: (fun _ => true) :: List.ofFn I
      ∀ i j : Fin 11, (i,j) ∈ ([(0,2),(0,3),(1,2),(2,3),(2,4),(2,10),(3,5),(3,7),(3,8),(3,10),(4,5)] : List (Fin 11 × Fin 11)) →
      let g : W := fun x => I i x || I j x
      g ∉ B →
      ∀ L : List W, L.length ≤ 17 →
        (∀ k : Fin L.length, let A := (B ++ [g]) ++ L.take k.val
          L.get k ∉ A ∧ ∃ u ∈ A, ∃ v ∈ A, L.get k = (fun x => u x && v x) ∨ L.get k = (fun x => u x || v x)) →
        (∀ w ∈ g :: L, ∀ a b : V, a ≠ b →
          ¬ (E.any fun e => decide ((a,b) = e ∨ (b,a) = e)) = true → w ≠ (fun x => x a && x b)) →
        (fun x => E.any fun e => x e.1 && x e.2) ∉ g :: L)
    : (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2, ∀ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 → ¬(x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true → x5 ≠ fun (x11 : Fin (10 : ℕ) → Bool) => x11 x7 && x11 x8) → (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  let V := Fin 10
  let Signal := (V → Bool) → Bool

  let graph : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)]

  let adjacency (a b : V) : Bool := graph.any (fun e => decide ((a,b) = e ∨ (b,a) = e))

  let target (x : V → Bool) : Bool := graph.any (fun e => x e.1 && x e.2)

  let perms : Fin 8 → V → V :=
    ![![0,1,2,3,4,5,6,7,8,9], ![0,1,2,7,5,4,6,3,9,8],
      ![0,1,6,9,4,5,2,8,7,3], ![0,1,6,8,5,4,2,9,3,7],
      ![1,0,5,8,6,2,4,7,3,9], ![1,0,5,7,2,6,4,8,9,3],
      ![1,0,4,9,6,2,5,3,7,8], ![1,0,4,3,2,6,5,9,8,7]]

  let action (σ : Fin 8) (i : Fin 11) : Fin 11 :=
    if h : i.val < 10 then (perms σ ⟨i.val,h⟩).castSucc else 10

  let reps : List (Fin 11 × Fin 11) :=
    [(0,1),(0,2),(0,3),(0,10),(1,2),(2,3),(2,4),(2,10),(3,5),(3,7),(3,8),(3,10),(4,5)]

  let meetReps : List (Fin 11 × Fin 11) := [(0,1),(1,2),(2,3),(2,10),(3,8),(3,10)]

  let joinReps : List (Fin 11 × Fin 11) :=
    [(0,2),(0,3),(1,2),(2,3),(2,4),(2,10),(3,5),(3,7),(3,8),(3,10),(4,5)]

  let input (i : Fin 11) : Signal :=
    if h : i.val < 10 then (fun x => x ⟨i.val,h⟩) else (fun x => x 0 || x 1)

  let rename (σ : Fin 8) (f : Signal) : Signal := fun x => f (fun i => x (perms σ i))

  have onto : ∀ σ : Fin 8, ∀ i : V, ∃ j : V, perms σ j = i := by decide +kernel

  have inject : ∀ σ : Fin 8, ∀ a b : V, perms σ a = perms σ b → a = b := by decide +kernel

  have actionOnto : ∀ σ : Fin 8, ∀ i : Fin 11, ∃ j : Fin 11, action σ j = i := by decide +kernel

  have seedFix : ∀ σ : Fin 8, (perms σ 0 = 0 ∧ perms σ 1 = 1) ∨
      (perms σ 0 = 1 ∧ perms σ 1 = 0) := by decide +kernel

  have representatives : ∀ a b : Fin 11, a ≠ b → ∃ σ : Fin 8,
      ((action σ a, action σ b) ∈ reps ∨ (action σ b, action σ a) ∈ reps) := by decide +kernel

  have preserveAdj : ∀ (σ : Fin 8) (a b : V),
      adjacency (perms σ a) (perms σ b) = adjacency a b := by decide +kernel

  have targetTrue (x : V → Bool) :
      target x = true ↔ ∃ a b, adjacency a b = true ∧ x a = true ∧ x b = true := by
    unfold target adjacency
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a,b⟩, h, ha, hb⟩
      exact ⟨a,b,⟨(a,b),h,Or.inl rfl⟩,ha,hb⟩
    · rintro ⟨a,b,⟨e,h,eq⟩,ha,hb⟩
      rcases eq with rfl | rfl
      · exact ⟨(a,b),h,ha,hb⟩
      · exact ⟨(b,a),h,hb,ha⟩

  have renameTarget (σ : Fin 8) : rename σ target = target := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change target (fun i => x (perms σ i)) = true ↔ target x = true
    refine (targetTrue (fun i => x (perms σ i))).trans (Iff.trans ?_ (targetTrue x).symm)
    constructor
    · rintro ⟨a,b,e,ha,hb⟩
      exact ⟨perms σ a, perms σ b, (preserveAdj σ a b).trans e,ha,hb⟩
    · rintro ⟨a,b,e,ha,hb⟩
      obtain ⟨a',ea⟩ := onto σ a
      obtain ⟨b',eb⟩ := onto σ b
      refine ⟨a',b',?_,ea ▸ ha,eb ▸ hb⟩
      rw [← preserveAdj σ a' b',ea,eb]
      exact e

  have renameInput (σ : Fin 8) (i : Fin 11) :
      rename σ (input i) = input (action σ i) := by
    funext x
    by_cases h : i.val < 10
    · simp [rename,input,action,h]
    · rcases seedFix σ with hseed | hseed
      · simp [rename,input,action,h,hseed.1,hseed.2]
      · simp [rename,input,action,h,hseed.1,hseed.2,Bool.or_comm]

  let base : List Signal := (fun _ => false) :: (fun _ => true) :: List.ofFn input

  have memBase (σ : Fin 8) (w : Signal) : w ∈ base ↔ ∃ f ∈ base, w = rename σ f := by
    simp only [base,List.mem_cons,List.mem_ofFn]
    constructor
    · rintro (rfl | rfl | ⟨i,rfl⟩)
      · exact ⟨_,Or.inl rfl,rfl⟩
      · exact ⟨_,Or.inr (Or.inl rfl),rfl⟩
      · obtain ⟨j,h⟩ := actionOnto σ i
        exact ⟨input j,Or.inr (Or.inr ⟨j,rfl⟩),((renameInput σ j).trans (congrArg input h)).symm⟩
    · rintro ⟨f, (rfl | rfl | ⟨i,rfl⟩), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨action σ i,(renameInput σ i).symm⟩)

  let meet (a b : Signal) : Signal := fun x => a x && b x

  let join (a b : Signal) : Signal := fun x => a x || b x

  have meetComm (a b : Signal) : meet a b = meet b a := by
    funext x
    exact Bool.and_comm _ _

  have joinComm (a b : Signal) : join a b = join b a := by
    funext x
    exact Bool.or_comm _ _

  have sourceMem (i : Fin 11) : input i ∈ base :=
    List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_ofFn.mpr ⟨i,rfl⟩))))

  have firstSources {f a b : Signal} (novel : f ∉ base) (ha : a ∈ base) (hb : b ∈ base)
      (h : f = meet a b ∨ f = join a b) :
      ∃ (i j : Fin 11), i ≠ j ∧ (f = meet (input i) (input j) ∨ f = join (input i) (input j)) := by
    have f0 : (fun _ => false) ∈ base := List.mem_cons_self
    have f1 : (fun _ => true) ∈ base := List.mem_cons.mpr (.inr List.mem_cons_self)
    have m0 (f : Signal) : meet (fun _ => false) f = (fun _ => false) := by
      funext x
      simp [meet]
    have j0 (f : Signal) : join (fun _ => false) f = f := by
      funext x
      simp [join]
    have m1 (f : Signal) : meet (fun _ => true) f = f := by
      funext x
      simp [meet]
    have j1 (f : Signal) : join (fun _ => true) f = (fun _ => true) := by
      funext x
      simp [join]
    have idemM (f : Signal) : meet f f = f := by funext x; simp [meet]
    have idemJ (f : Signal) : join f f = f := by funext x; simp [join]
    simp only [base, List.mem_cons, List.mem_ofFn] at ha hb
    rcases ha with rfl | rfl | ⟨i,rfl⟩
    · exfalso
      apply novel
      rcases h with rfl | rfl
      · rw [m0]; exact f0
      · rw [j0]; simpa only [base,List.mem_cons,List.mem_ofFn] using hb
    · exfalso
      apply novel
      rcases h with rfl | rfl
      · rw [m1]; simpa only [base,List.mem_cons,List.mem_ofFn] using hb
      · rw [j1]; exact f1
    · rcases hb with rfl | rfl | ⟨j,rfl⟩
      · exfalso
        apply novel
        rcases h with rfl | rfl
        · rw [meetComm,m0]; exact f0
        · rw [joinComm,j0]; exact sourceMem i
      · exfalso
        apply novel
        rcases h with rfl | rfl
        · rw [meetComm,m1]; exact sourceMem i
        · rw [joinComm,j1]; exact f1
      · by_cases eq : i = j
        · subst j
          exfalso
          apply novel
          rcases h with rfl | rfl
          · rw [idemM]; exact sourceMem i
          · rw [idemJ]; exact sourceMem i
        · exact ⟨i,j,eq,h⟩

  have firstOrbit {f a b : Signal} (novel : f ∉ base) (ha : a ∈ base) (hb : b ∈ base)
      (h : f = meet a b ∨ f = join a b) :
      ∃ (σ : Fin 8) (i j : Fin 11), (i,j) ∈ reps ∧
        (rename σ f = meet (input i) (input j) ∨ rename σ f = join (input i) (input j)) := by
    obtain ⟨a,b,ne,op⟩ := firstSources novel ha hb h
    obtain ⟨σ,steps⟩ := representatives a b ne
    have swap : rename σ (input a) = input (action σ a) ∧ rename σ (input b) = input (action σ b) :=
      ⟨renameInput σ a,renameInput σ b⟩
    have lift (g : Bool → Bool → Bool) :
        rename σ (fun x => g (input a x) (input b x)) =
          (fun x => g (input (action σ a) x) (input (action σ b) x)) := by
      funext x
      exact congrArg₂ g (congrFun swap.1 x) (congrFun swap.2 x)
    rcases steps with straight | reversed
    · refine ⟨σ,action σ a,action σ b,straight,?_⟩
      rcases op with rfl | rfl
      · exact Or.inl (lift (· && ·))
      · exact Or.inr (lift (· || ·))
    · refine ⟨σ,action σ b,action σ a,reversed,?_⟩
      rcases op with rfl | rfl
      · exact Or.inl ((lift (· && ·)).trans (meetComm _ _))
      · exact Or.inr ((lift (· || ·)).trans (joinComm _ _))

  have reindexOnto (σ : Fin 8) (y : V → Bool) :
      ∃ x : V → Bool, (fun i => x (perms σ i)) = y := by
    classical
    let rev (j : V) := (onto σ j).choose
    have opposite (i : V) : rev (perms σ i) = i :=
      inject σ _ _ (onto σ (perms σ i)).choose_spec
    exact ⟨fun i => y (rev i), funext fun i => congrArg y (opposite i)⟩

  have renameInject (σ : Fin 8) : Function.Injective (rename σ) := by
    intro a b h
    funext y
    obtain ⟨x, e⟩ := reindexOnto σ y
    have h' := congrFun h x
    unfold rename at h'
    rwa [e] at h'

  let Allowed (f : Signal) : Prop :=
    ∀ a b : V, a ≠ b → ¬ adjacency a b = true → f ≠ fun x => x a && x b

  have meetCases : ∀ i j : Fin 11, (i,j) ∈ reps →
      (i,j) ∈ meetReps ∨ (i = 0 ∧ j = 10) ∨
        ∃ a b : V, i = a.castSucc ∧ j = b.castSucc ∧ a ≠ b ∧ adjacency a b = false := by
    decide +kernel

  have joinCases : ∀ i j : Fin 11, (i,j) ∈ reps →
      (i,j) ∈ joinReps ∨ (i = 0 ∧ (j = 1 ∨ j = 10)) := by decide +kernel

  have meetAllowed {i j : Fin 11} (rep : (i,j) ∈ reps)
      (new : meet (input i) (input j) ∉ base) (allowed : Allowed (meet (input i) (input j))) :
      (i,j) ∈ meetReps := by
    rcases meetCases i j rep with good | trivial | ⟨a,b,hi,hj,ne,noedge⟩
    · exact good
    · obtain ⟨rfl,rfl⟩ := trivial
      exfalso
      apply new
      have same : meet (input 0) (input 10) = input 0 := by
        funext x
        change (x 0 && (x 0 || x 1)) = x 0
        cases x 0 <;> rfl
      rw [same]
      exact sourceMem 0
    · exfalso
      apply allowed a b ne (by simp [noedge])
      rw [hi,hj]
      funext x
      simp [meet,input,a.isLt,b.isLt]

  have joinAllowed {i j : Fin 11} (rep : (i,j) ∈ reps)
      (new : join (input i) (input j) ∉ base) : (i,j) ∈ joinReps := by
    rcases joinCases i j rep with good | ⟨rfl, eq | eq⟩
    · exact good
    · subst j
      exfalso
      apply new
      change input 10 ∈ base
      exact sourceMem 10
    · subst j
      exfalso
      apply new
      have same : join (input 0) (input 10) = input 10 := by
        funext x
        change (x 0 || (x 0 || x 1)) = (x 0 || x 1)
        cases x 0 <;> rfl
      rw [same]
      exact sourceMem 10

  have renameAllowed (σ : Fin 8) (f : Signal) (allowed : Allowed f) : Allowed (rename σ f) := by
    intro a b ne bad eq
    obtain ⟨i, hi⟩ := onto σ a
    obtain ⟨j, hj⟩ := onto σ b
    have ij : i ≠ j := fun h => ne (hi.symm.trans ((congrArg (perms σ) h).trans hj))
    have hij : ¬ adjacency i j = true :=
      fun e => bad (by rw [← hi, ← hj, preserveAdj σ i j]; exact e)
    apply allowed i j ij hij
    funext y
    obtain ⟨x, ex⟩ := reindexOnto σ y
    have h := congrFun eq x
    change f (fun k => x (perms σ k)) = (x a && x b) at h
    have hx (k : V) : x (perms σ k) = y k := congrFun ex k
    rw [← hi, ← hj, ex, hx i, hx j] at h
    exact h

  let Construction (B : List Signal) (L : List Signal) : Prop :=
    ∀ i : Fin L.length,
      let pool := B ++ L.take i.val
      L.get i ∉ pool ∧ ∃ a ∈ pool, ∃ b ∈ pool, L.get i = meet a b ∨ L.get i = join a b

  have remapPool (σ : Fin 8) (L : List Signal) (w : Signal) :
      w ∈ base ++ L.map (rename σ) ↔ ∃ f ∈ base ++ L, w = rename σ f := by
    simp only [List.mem_append]
    constructor
    · rintro (old | new)
      · obtain ⟨f, mem, eq⟩ := (memBase σ w).mp old
        exact ⟨f,Or.inl mem,eq⟩
      · obtain ⟨f, mem, eq⟩ := List.mem_map.mp new
        exact ⟨f,Or.inr mem,eq.symm⟩
    · rintro ⟨f, (old | new), eq⟩
      · exact Or.inl ((memBase σ w).mpr ⟨f,old,eq⟩)
      · exact Or.inr (List.mem_map.mpr ⟨f,new,eq.symm⟩)

  have renameConstruction (σ : Fin 8) (L : List Signal) (h : Construction base L) :
      Construction base (L.map (rename σ)) := by
    intro i
    let j : Fin L.length := ⟨i.val, by simpa using i.isLt⟩
    obtain ⟨fresh,a,ma,b,mb,rec⟩ := h j
    have access : (L.map (rename σ)).get i = rename σ (L.get j) := by
      simp [j]
    have hpool (w : Signal) : w ∈ base ++ (L.map (rename σ)).take i.val ↔
        ∃ f ∈ base ++ L.take j.val, w = rename σ f := by
      rw [← List.map_take]
      exact remapPool σ _ w
    dsimp only
    rw [access]
    refine ⟨?_, rename σ a, (hpool _).mpr ⟨a,ma,rfl⟩, rename σ b, (hpool _).mpr ⟨b,mb,rfl⟩, ?_⟩
    · intro was
      obtain ⟨f,hf,eq⟩ := (hpool _).mp was
      exact fresh ((renameInject σ eq).symm ▸ hf)
    · rcases rec with eq | eq
      · exact Or.inl (congrArg (rename σ) eq)
      · exact Or.inr (congrArg (rename σ) eq)

  have constructionTail (B : List Signal) (g : Signal) (L : List Signal)
      (h : Construction B (g :: L)) : Construction (B ++ [g]) L := by
    intro i
    have suffix := h ⟨i.val+1, by simpa only [List.length_cons] using Nat.succ_lt_succ i.isLt⟩
    simpa [List.take_succ_cons,List.append_assoc] using suffix

  have simplifyCounterexample (L : List Signal) (legal : Construction base L)
      (safe : ∀ w ∈ L, Allowed w) (y : target ∈ L) :
      ∃ (i j : Fin 11) (g : Signal) (tail : List Signal),
        (i,j) ∈ reps ∧ (g = meet (input i) (input j) ∨ g = join (input i) (input j)) ∧
        tail.length + 1 = L.length ∧ g ∉ base ∧ Construction (base ++ [g]) tail ∧
        (∀ w ∈ g :: tail, Allowed w) ∧ target ∈ g :: tail := by
    cases L with
    | nil => simp at y
    | cons a L =>
      obtain ⟨hne,u,hu,v,hv,hop⟩ := legal ⟨0, by simp⟩
      change a ∉ base ++ [] at hne
      change u ∈ base ++ [] at hu
      change v ∈ base ++ [] at hv
      simp only [List.append_nil] at hne hu hv
      obtain ⟨σ,i,j,rep,gate⟩ := firstOrbit hne hu hv hop
      have renLegal : Construction base (rename σ a :: L.map (rename σ)) :=
        renameConstruction σ (a :: L) legal
      have renFresh : rename σ a ∉ base := by
        have h := (renLegal ⟨0, by simp⟩).1
        simpa using h
      refine ⟨i,j,rename σ a,L.map (rename σ),rep,gate,by simp,renFresh,
        constructionTail base _ _ renLegal,?_ ,?_⟩
      · intro w mem
        obtain ⟨t,ht,rfl⟩ :=
          List.mem_map.mp (show w ∈ (a :: L).map (rename σ) from mem)
        exact renameAllowed σ t (safe t ht)
      · have m : rename σ target ∈ (a :: L).map (rename σ) :=
          List.mem_map.mpr ⟨target,y,rfl⟩
        rw [renameTarget σ] at m
        exact m

  have base_eq : base = ((fun _ : V → Bool => false) :: (fun _ => true) ::
      List.ofFn (fun i : V => fun x : V → Bool => x i)) ++ [fun x => x 0 || x 1] := by
    have raw : List.ofFn input = List.ofFn (fun i : V => fun x : V → Bool => x i) ++ [fun x => x 0 || x 1] := by
      rw [List.ofFn_succ_last]
      have original : (fun i : V => input i.castSucc) = fun i : V => fun x : V → Bool => x i := by
        funext i x
        simp [input,i.isLt]
      rw [original]
      rfl
    unfold base
    rw [raw]
    rfl
  dsimp only
  intro L small legality safe goal
  have legal : Construction base L := by
    intro i
    change L.get i ∉ base ++ L.take i.val ∧
      ∃ a ∈ base ++ L.take i.val, ∃ b ∈ base ++ L.take i.val, L.get i = meet a b ∨ L.get i = join a b
    simpa only [base_eq, List.append_assoc] using legality i
  have allSafe : ∀ w ∈ L, Allowed w := safe
  have found : target ∈ L := goal
  obtain ⟨i,j,g,tail,rep,op,len,fresh,legalTail,safeTail,contains⟩ :=
    simplifyCounterexample L legal allSafe found
  have bound : tail.length ≤ 17 := by omega
  rcases op with rfl | rfl
  · have valid := meetAllowed rep fresh (safeTail _ List.mem_cons_self)
    exact (meetStart i j valid fresh tail bound legalTail safeTail) contains
  · have valid := joinAllowed rep fresh
    exact (joinStart i j valid fresh tail bound legalTail safeTail) contains
