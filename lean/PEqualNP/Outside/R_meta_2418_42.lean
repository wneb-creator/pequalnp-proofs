import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- The conversion of the published max-false table to circuit predicates follows R_meta_2418_648.
-- The frontier at one live line has just 52 positives and 14 negatives.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2418_42
 (synth : let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
    let B := fun C : Circuit =>
      (∀ p l, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) ∧
      C.eval (incidenceInput (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) = false ∧
      ∀ l, C.eval (incidenceInput (S l)ᶜ {l}) = false
    ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
      (∀ p l, p ∈ S l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ P L, IsMaximalFalse S P L → ¬ IsGeneric S 0 P L → C.eval (incidenceInput P L) = false) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧ B D)
 (boundary : ∀ (S : Fin 13 → Finset (Fin 13)) (f : Finset (Fin 13) → Finset (Fin 13) → Bool),
    (∀ P Q L M, P ⊆ Q → L ⊆ M → f P L = true → f Q M = true) →
    (∀ p l, p ∈ S l → f {p} {l} = true) → f Finset.univ ∅ = false →
    (∀ l, f (S l)ᶜ {l} = false) →
    ∀ P L, L.card ≤ 1 → (f P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, p ∈ S l)) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  have monoMap : ∀ (C : Circuit), Monotone2 C → ∀ P Q L M : Finset (Fin 13),
    P ⊆ Q → L ⊆ M → C.eval (incidenceInput P L) = true →
    C.eval (incidenceInput Q M) = true := by
    intro C kind P Q L M hp hl
    let B : Bool → Bool → Prop := fun a b => a = true → b = true
    let R : List Bool → List Bool → Prop := List.Forall₂ B
    have ap {xs ys us vs : List Bool} (h : R xs ys) (h' : R us vs) : R (xs++us) (ys++vs) := by
      induction h with
      | nil => exact h'
      | cons h _ ih => exact .cons h ih
    have read {xs ys : List Bool} (h : R xs ys) (i : ℕ) : B (xs.getD i false) (ys.getD i false) := by
      induction h generalizing i with
      | nil => simp [B]
      | cons h _ ih =>
        cases i with
        | zero => exact h
        | succ i => exact ih i
    have inputs (A D : Finset (Fin 13)) (hs : A ⊆ D) :
        R (List.ofFn fun p => decide (p ∈ A)) (List.ofFn fun p => decide (p ∈ D)) := by
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp,?_⟩
      intro i ha hd
      simp only [B, List.get_eq_getElem, List.getElem_ofFn, decide_eq_true_eq]
      exact fun hi => hs hi
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have run (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (x y : List Bool) (h : R x y) :
        R (gs.foldl step x) (gs.foldl step y) := by
      induction gs generalizing x y with
      | nil => exact h
      | cons g gs ih =>
        apply ih (fun k hk => ok k (List.mem_cons_of_mem g hk))
        apply ap h
        apply List.Forall₂.cons _ List.Forall₂.nil
        rcases ok g (by simp) with hand | hor
        · rw [hand]
          change (g.inputs.map (fun i => x.getD i false)).all id = true →
            (g.inputs.map (fun i => y.getD i false)).all id = true
          simp only [List.all_eq_true, List.mem_map, id_eq]
          intro hx b hb
          obtain ⟨r,hr,rfl⟩ := hb
          exact read h r (hx _ ⟨r,hr,rfl⟩)
        · rw [hor]
          change (g.inputs.map (fun i => x.getD i false)).any id = true →
            (g.inputs.map (fun i => y.getD i false)).any id = true
          simp only [List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨b,⟨r,hr,rfl⟩,hb⟩
          exact ⟨_,⟨r,hr,rfl⟩,read h r hb⟩
    exact read (run C.gates (fun g hg => (kind g hg).1) _ _ (ap (inputs P Q hp) (inputs L M hl))) C.output
  dsimp only
  intro C mono size checks
  let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
  let I := fun p l : Fin 13 => ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d
  have sameInc : ∀ p l, p ∈ S l ↔ I p l := by
    intro p l
    constructor
    · intro h
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h|h|h|h
      · exact ⟨0,by simp,by simpa using h⟩
      · exact ⟨1,by simp,h⟩
      · exact ⟨3,by simp,h⟩
      · exact ⟨9,by simp,h⟩
    · rintro ⟨d,hd,rfl⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl|rfl|rfl|rfl <;> simp [S]
  have apart (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro e
    have h : p.val = 13+l.val := congrArg (fun i : Fin 26 => i.val) e
    have hp := p.isLt
    omega
  have row (P L : Finset (Fin 13)) :
      List.ofFn (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
        ∃ l ∈ L, k=Fin.natAdd 13 l)) = incidenceInput P L := by
    let f := fun k : Fin (13+13) => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
      ∃ l ∈ L, k=Fin.natAdd 13 l)
    have left (p : Fin 13) : f (Fin.castAdd 13 p) = decide (p ∈ P) := by
      unfold f
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro (⟨a,ha,e⟩ | ⟨l,_,e⟩)
        · exact ((Fin.castAdd_injective 13 13) e).symm ▸ ha
        · exact (apart p l e).elim
      · exact fun h => Or.inl ⟨p,h,rfl⟩
    have right (l : Fin 13) : f (Fin.natAdd 13 l) = decide (l ∈ L) := by
      unfold f
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro (⟨p,_,e⟩ | ⟨b,hb,e⟩)
        · exact (apart p l e.symm).elim
        · exact ((Fin.natAdd_injective 13 13) e).symm ▸ hb
      · exact fun h => Or.inr ⟨l,h,rfl⟩
    change List.ofFn f = _
    rw [List.ofFn_add]
    exact congrArg₂ List.append (congrArg List.ofFn (funext left)) (congrArg List.ofFn (funext right))
  have yes (p l : Fin 13) (inc : p ∈ S l) : C.eval (incidenceInput {p} {l}) = true := by
    rw [← row {p} {l}]
    have test := checks.1 p l ((sameInc p l).mp inc)
    change C.eval (List.ofFn (fun k : Fin 26 => decide (k=Fin.castAdd 13 p ∨ k=Fin.natAdd 13 l))) = true at test
    simpa only [Finset.mem_singleton,exists_eq_left] using test
  have no (P L : Finset (Fin 13)) (largest : IsMaximalFalse S P L)
      (degenerate : (∃ l, P ⊆ S l) ∨ ∃ p, ∀ l ∈ L, p ∈ S l) : C.eval (incidenceInput P L) = false := by
    have disj (l : Fin 13) : l ∈ L ↔ ∀ p ∈ P, ¬I p l := by
      constructor
      · intro hl p hp inc
        exact Finset.disjoint_left.mp (largest.1 l hl) ((sameInc p l).mpr inc) hp
      · intro hl
        by_contra missing
        apply largest.2.2 l missing
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | old
        · exact Finset.disjoint_left.mpr fun p hs hp => hl p hp ((sameInc p k).mp hs)
        · exact largest.1 k old
    have maxPoints (p : Fin 13) (hp : p ∉ P) : ∃ l, (∀ r ∈ P, ¬I r l) ∧ I p l := by
      classical
      by_contra fail
      apply largest.2.1 p hp
      intro l hl
      apply Finset.disjoint_left.mpr
      intro r hr hIn
      rcases Finset.mem_insert.mp hIn with rfl | old
      · exact fail ⟨l,(disj l).mp hl,(sameInc r l).mp hr⟩
      · exact Finset.disjoint_left.mp (largest.1 l hl) hr old
    have kind : (∃ l, ∀ p ∈ P, I p l) ∨ ∃ p, ∀ l, (∀ r ∈ P, ¬I r l) → I p l := by
      rcases degenerate with ⟨l,h⟩ | ⟨p,h⟩
      · exact Or.inl ⟨l,fun p hp => (sameInc p l).mp (h hp)⟩
      · exact Or.inr ⟨p,fun l hl => (sameInc p l).mp (h l ((disj l).mpr hl))⟩
    rw [← row P L]
    have hh := checks.2 P maxPoints kind
    change C.eval (List.ofFn (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
      ∃ l, k=Fin.natAdd 13 l ∧ ∀ r ∈ P, ¬I r l))) = false at hh
    have agree : (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
        ∃ l ∈ L, k=Fin.natAdd 13 l)) =
        (fun k : Fin 26 => decide ((∃ p ∈ P, k=Fin.castAdd 13 p) ∨
          ∃ l, k=Fin.natAdd 13 l ∧ ∀ r ∈ P, ¬I r l)) := by
      funext k
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,← disj,and_comm]
    rwa [agree]
  let thin : Set (Fin 26 → Bool) := {x | ∃ l : Fin 13, ∀ k : Fin 13,
    x (Fin.natAdd 13 k) = true → k=l}
  have noGeneric (P L : Finset (Fin 13)) (largest : IsMaximalFalse S P L)
      (generic : ¬ IsGeneric S 0 P L) : C.eval (incidenceInput P L) = false := by
    classical
    apply no P L largest
    by_contra h
    apply generic
    refine ⟨Nat.zero_le _,Nat.zero_le _,?_,?_⟩
    · exact fun l hl => h (Or.inl ⟨l,hl⟩)
    · exact fun p hp => h (Or.inr ⟨p,hp⟩)
  let P0 : Finset (Fin 13) := Finset.univ
  have zero : C.eval (incidenceInput P0 (∅ : Finset (Fin 13))) = false := by
    apply no _ _
    · refine ⟨(fun k hk => (Finset.notMem_empty k hk).elim), by simp [P0], ?_⟩
      intro k _ h
      have dk := h k (by simp)
      exact Finset.disjoint_left.mp dk (show k ∈ S k by simp [S]) (Finset.mem_univ k)
    · exact Or.inr ⟨0, by simp⟩
  have one (l : Fin 13) : C.eval (incidenceInput (S l)ᶜ {l}) = false := by
    apply no _ _
    · have sep : ∀ k j : Fin 13, k ≠ j → ∃ p ∈ S k, p ∉ S j := by
        intro k j hj
        by_cases hk : k ∈ S j
        · obtain ⟨a,ha,ka⟩ := (sameInc k j).mp hk
          have nz : a ≠ 0 := by
            rintro rfl
            exact hj (by simpa using ka)
          have noadj : ∀ a ∈ ({0,1,3,9} : Finset (Fin 13)), a ≠ 0 →
              a+1 ∉ ({0,1,3,9} : Finset (Fin 13)) := by
            intro t ht hn
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl|rfl|rfl|rfl <;> first | exact (hn rfl).elim | decide
          refine ⟨k+1,by simp [S],?_⟩
          intro bad
          obtain ⟨b,hb,e⟩ := (sameInc (k+1) j).mp bad
          have ab : a+1=b := add_left_cancel (show j+(a+1)=j+b by rwa [←add_assoc,←ka])
          exact noadj a ha nz (ab.symm ▸ hb)
        · exact ⟨k,by simp [S],hk⟩
      refine ⟨?_,?_,?_⟩
      · intro k hk
        obtain rfl := Finset.mem_singleton.mp hk
        exact Finset.disjoint_left.mpr fun p hi hc => (Finset.mem_compl.mp hc) hi
      · intro p hp h
        exact Finset.disjoint_left.mp (h l (by simp)) (by simpa using hp) (Finset.mem_insert_self _ _)
      · intro k hk h
        obtain ⟨p,pk,np⟩ := sep k l (by simpa using hk)
        exact Finset.disjoint_left.mp (h k (Finset.mem_insert_self _ _)) pk (Finset.mem_compl.mpr np)
    · exact Or.inr ⟨l,by simp [S]⟩
  obtain ⟨D,md,sz,deg,b⟩ := synth C mono size yes noGeneric
  refine ⟨D,md,sz,deg,?_⟩
  intro x hx
  let P := Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p)
  let L := Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l)
  have pbit (p : Fin 13) : (x (Fin.castAdd 13 p)) = decide (p ∈ P) := by simp [P]
  have lbit (l : Fin 13) : (x (Fin.natAdd 13 l)) = decide (l ∈ L) := by simp [L]
  have repr : List.ofFn x = incidenceInput P L := by
    let xx : Fin (13+13) → Bool := x
    change List.ofFn xx = _
    rw [List.ofFn_add]
    exact congrArg₂ List.append (congrArg List.ofFn (funext pbit)) (congrArg List.ofFn (funext lbit))
  obtain ⟨l,hl⟩ := hx
  have card : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (hl a (by simpa [L] using ha)).trans (hl b (by simpa [L] using hb)).symm
  change D.eval (List.ofFn x) = C.eval (List.ofFn x)
  rw [repr]
  apply Bool.eq_iff_iff.mpr
  have dz := b.2.1
  change D.eval (incidenceInput (S 0 ∪ (S 0)ᶜ) (S 0 \ S 0)) = false at dz
  have cu (A : Finset (Fin 13)) : A ∪ Aᶜ = Finset.univ := by ext a; simp
  have sd (A : Finset (Fin 13)) : A \ A = ∅ := by simp
  rw [cu,sd] at dz
  exact (boundary S (fun P L => D.eval (incidenceInput P L)) (monoMap D md) b.1 dz b.2.2 P L card).trans
    (boundary S (fun P L => C.eval (incidenceInput P L)) (monoMap C mono) yes zero one P L card).symm
