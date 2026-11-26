import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

-- Delete both terminal gates. Normalize their exclusive flags by collineations
-- and optional output exchange; point-line duality would change the negative rows.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6011_314
    (deletion : ∀ (n : ℕ), let ok := fun (D : Circuit) (g : Gate) => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
       g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < n+D.size
    let read := fun (D : Circuit) (g : Gate) (x : Fin n → Bool) =>
       g.op.eval (g.inputs.map fun w => (D.wires (List.ofFn x)).getD w false)
    let swap := fun (t : Bool) (v : Bool × Bool) => if t then v.swap else v
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack n C → n ≤ a → n ≤ b →
    a < n+C.size → b < n+C.size → a ≠ b → (∀ g ∈ C.gates, a ∉ g.inputs ∧ b ∉ g.inputs) →
    ∀ (π : Equiv.Perm (Fin n)) (t : Bool), ∃ (D : Circuit) (g h : Gate),
    D.size+2 ≤ C.size ∧ Monotone2 D ∧ ReadsBack n D ∧ ok D g ∧ ok D h ∧
      ∀ x, let w := C.wires (List.ofFn (x ∘ π))
           (read D g x,read D h x) = swap t (w.getD a false,w.getD b false))
    (normal : let X := fun (P L : Finset (Fin 13)) => Fin.append (fun i => decide (i ∈ P)) (fun i => decide (i ∈ L))
    let fits := fun (F : (Fin 26 → Bool) → Bool × Bool) =>
      (∀ p l : Fin 13, p ∈ singerLines3 l → F (X {p} {l}) ≠ (false,false)) ∧
      (∀ Q, IsQuadrangle singerLines3 Q → F (X Q (missLines singerLines3 Q)) = (false,false))
    let privateRow := fun (F : (Fin 26 → Bool) → Bool × Bool) (t : Bool × Bool) =>
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ F (X {p} {l}) = t
    let test := fun (F : (Fin 26 → Bool) → Bool × Bool) => F (X {0} {0}) = (true,false) ∧
       ∃ p l : Fin 13, 13*p.val+l.val ∈ ([4,13,14,27] : List ℕ) ∧ F (X {p} {l}) = (false,true)
    let swap := fun (t : Bool) (v : Bool × Bool) => if t then v.swap else v
    ∀ F, fits F → privateRow F (true,false) → privateRow F (false,true) →
      ∃ (π : Equiv.Perm (Fin 26)) (t : Bool), let H := fun x => swap t (F (x ∘ π))
      fits H ∧ test H)
    (search : let X := fun (P L : Finset (Fin 13)) => Fin.append (fun i => decide (i ∈ P)) (fun i => decide (i ∈ L))
    let fits := fun (F : (Fin 26 → Bool) → Bool × Bool) =>
      (∀ p l : Fin 13, p ∈ singerLines3 l → F (X {p} {l}) ≠ (false,false)) ∧
      (∀ Q, IsQuadrangle singerLines3 Q → F (X Q (missLines singerLines3 Q)) = (false,false))
    let test := fun (F : (Fin 26 → Bool) → Bool × Bool) => F (X {0} {0}) = (true,false) ∧
       ∃ p l : Fin 13, 13*p.val+l.val ∈ ([4,13,14,27] : List ℕ) ∧ F (X {p} {l}) = (false,true)
    let read := fun (D : Circuit) (g : Gate) (x : Fin 26 → Bool) =>
       g.op.eval (g.inputs.map fun w => (D.wires (List.ofFn x)).getD w false)
    ∀ (D : Circuit) (g h : Gate), D.size ≤ 60 → Monotone2 D → ReadsBack 26 D → Monotone2 (⟨[g,h],0⟩ : Circuit) →
      let H := fun x => (read D g x,read D h x)
      fits H → ¬ test H)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           (∀ x8 ∈ x1.gates, x2 ∉ x8.inputs ∧ x3 ∉ x8.inputs) →             have x9 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};             have x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x10 x11 : Fin (13 : ℕ)) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x10)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x11);             have x11 : Finset (Fin (13 : ℕ)) → List Bool := fun (x11 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 ∈ x11)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (∀ x13 ∈ x11, x13 - x12 ∉ x9);             have x12 : Finset (Fin (13 : ℕ)) → Prop := fun (x12 : Finset (Fin (13 : ℕ))) => x12.card = (4 : ℕ) ∧ ∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x12 | x14 - x13 ∈ x9}.card ≤ (2 : ℕ);             have x13 : ℕ → List Bool → Bool := fun (x13 : ℕ) (x14 : List Bool) => (x1.wires x14).getD x13 Bool.false;             (∀ (x14 x15 : Fin (13 : ℕ)), x14 - x15 ∈ x9 → x13 x2 (x10 x14 x15) = Bool.true ∨ x13 x3 (x10 x14 x15) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), x12 x15 → x13 x2 (x11 x15) = Bool.false ∧ x13 x3 (x11 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x9 ∧ x13 x2 (x10 x16 x17) = Bool.true ∧ x13 x3 (x10 x16 x17) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x9 ∧ x13 x3 (x10 x17 x18) = Bool.true ∧ x13 x2 (x10 x17 x18) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b mono back ha hb sink
  dsimp only
  intro covers rejects pA pB
  classical
  let X := fun (P L : Finset (Fin 13)) => Fin.append (fun i => decide (i ∈ P)) (fun i => decide (i ∈ L))
  let fits := fun (F : (Fin 26 → Bool) → Bool × Bool) =>
      (∀ p l : Fin 13, p ∈ singerLines3 l → F (X {p} {l}) ≠ (false,false)) ∧
      (∀ Q, IsQuadrangle singerLines3 Q → F (X Q (missLines singerLines3 Q)) = (false,false))
  let pr := fun (F : (Fin 26 → Bool) → Bool × Bool) (t : Bool × Bool) =>
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ F (X {p} {l}) = t
  let f := fun (x : Fin 26 → Bool) =>
    let w := C.wires (List.ofFn x)
    (w.getD a false,w.getD b false)
  let flags := fun (p l : Fin 13) => (List.ofFn fun i : Fin 13 => decide (i=p)) ++
                                      (List.ofFn fun i : Fin 13 => decide (i=l))
  have incidence (p l : Fin 13) : p ∈ singerLines3 l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13)) :=
    (by decide +kernel : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13))) p l
  have flagRow (p l : Fin 13) : List.ofFn (X {p} {l}) = flags p l := by
    rw [show List.ofFn (X {p} {l}) = _ from List.ofFn_fin_append _ _]
    simp [flags]
  have noRow (Q : Finset (Fin 13)) : List.ofFn (X Q (missLines singerLines3 Q)) =
      (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
      (List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ ({0,1,3,9} : Finset (Fin 13)))) := by
    change List.ofFn (Fin.append _ _) = _
    rw [List.ofFn_fin_append]
    congr 2
    funext l
    apply Bool.eq_iff_iff.mpr
    change (decide (l ∈ Finset.univ.filter (fun k : Fin 13 => Disjoint (singerLines3 k) Q)) = true ↔
      decide (∀ p ∈ Q, p-l ∉ ({0,1,3,9} : Finset (Fin 13))) = true)
    simp only [decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
    constructor
    · intro h p hp hi
      exact h ((incidence p l).mpr hi) hp
    · intro h p hi hp
      exact h p hp ((incidence p l).mp hi)
  have negative (Q : Finset (Fin 13)) (hq : IsQuadrangle singerLines3 Q) :
      f (X Q (missLines singerLines3 Q)) = (false,false) := by
    have qual : Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13))).card ≤ 2 := by
      refine ⟨hq.1,fun l => ?_⟩
      have eq : (Q.filter fun p => p-l ∈ ({0,1,3,9} : Finset (Fin 13))) = Q ∩ singerLines3 l := by
        ext p; simp only [Finset.mem_filter,Finset.mem_inter,incidence]
      exact eq ▸ hq.2 l
    obtain ⟨r,s⟩ := rejects Q qual
    change (_,_) = (false,false)
    apply Prod.ext
    · change (C.wires (List.ofFn (X Q _))).getD a false = false
      rwa [noRow Q]
    · change (C.wires (List.ofFn (X Q _))).getD b false = false
      rwa [noRow Q]
  have pass : fits f := by
    refine ⟨?_,negative⟩
    intro p l flag nope
    rcases covers p l ((incidence p l).mp flag) with h|h
    · have hf := congrArg Prod.fst nope
      change (C.wires (List.ofFn (X {p} {l}))).getD a false = false at hf
      rw [flagRow] at hf
      exact Bool.noConfusion (h.symm.trans hf)
    · have hf := congrArg Prod.snd nope
      change (C.wires (List.ofFn (X {p} {l}))).getD b false = false at hf
      rw [flagRow] at hf
      exact Bool.noConfusion (h.symm.trans hf)
  obtain ⟨p,l,i,ap,bp⟩ := pA
  obtain ⟨q,m,i',aq,bq⟩ := pB
  have ab : a ≠ b := fun eq => Bool.noConfusion (ap.symm.trans (eq ▸ bp))
  have A : pr f (true,false) := by
    refine ⟨p,l,(incidence p l).mpr i,?_⟩
    change ((C.wires _).getD a false,(C.wires _).getD b false) = _
    rw [flagRow]; exact Prod.ext ap bp
  have B : pr f (false,true) := by
    refine ⟨q,m,(incidence q m).mpr i',?_⟩
    change ((C.wires _).getD a false,(C.wires _).getD b false) = _
    rw [flagRow]; exact Prod.ext bq aq
  have allInputs (u : Fin 26) : ∃ Q, IsQuadrangle singerLines3 Q ∧ X Q (missLines singerLines3 Q) u = true := by
    let S : List (Finset (Fin 13)) := [{0,1,2,5},{3,4,7,9},{6,8,10,12},{0,3,8,11},{0,2,3,4}]
    obtain ⟨Q,_,h⟩ := (by decide +kernel : ∀ u : Fin 26, ∃ Q ∈ S, IsQuadrangle singerLines3 Q ∧ X Q (missLines singerLines3 Q) u = true) u
    exact ⟨Q,h⟩
  have owned (w : ℕ) (hw : w=a ∨ w=b) : 26 ≤ w := by
    by_contra! raw
    let u : Fin 26 := ⟨w,raw⟩
    obtain ⟨Q,quad,hot⟩ := allInputs u
    have off := negative Q quad
    let x := X Q (missLines singerLines3 Q)
    have val : (C.wires (List.ofFn x)).getD w false = x u := by
      have pref (gs : List Gate) (w : List Bool) : ∃ t, (gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]) w) = w ++ t := by
        induction gs generalizing w with
        | nil => exact ⟨[], by simp⟩
        | cons g gs ih =>
          obtain ⟨t,ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          exact ⟨_ :: t,by simpa only [List.foldl_cons,List.append_assoc,List.cons_append,List.nil_append] using ht⟩
      obtain ⟨tail,e⟩ := pref C.gates (List.ofFn x)
      change (C.wires (List.ofFn x)).getD w false = _
      change C.wires (List.ofFn x) = List.ofFn x ++ tail at e
      rw [e,List.getD_append _ _ _ _ (by simpa using raw),List.getD_eq_getElem _ _ (by simpa using raw)]
      exact List.getElem_ofFn ..
    rcases hw with rfl|rfl
    · exact Bool.noConfusion ((congrArg Prod.fst off).symm.trans (val.trans hot))
    · exact Bool.noConfusion ((congrArg Prod.snd off).symm.trans (val.trans hot))
  by_contra! short
  obtain ⟨π,t,tests,marked⟩ := normal f pass A B
  obtain ⟨D,g,h,cost,md,rd,lg,lh,run⟩ := deletion 26 C a b mono back (owned a (Or.inl rfl)) (owned b (Or.inr rfl)) ha hb ab sink π t
  have eq := funext run
  have roots : Monotone2 (⟨[g,h],0⟩ : Circuit) := by
    intro k hk
    have mem : k = g ∨ k = h := by simpa using hk
    rcases mem with rfl|rfl
    · exact ⟨lg.1,lg.2.1⟩
    · exact ⟨lh.1,lh.2.1⟩
  apply search D g h (by omega) md rd roots
  · rwa [eq]
  · rwa [eq]
