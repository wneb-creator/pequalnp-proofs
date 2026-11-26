import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6026_1
    (trace : let F := (Fin 10 → Bool) → Bool
      ∀ (C : Circuit) (inputs : List F) (S : Set F) (P : ℕ → Set F → Prop),
      FanInTwo C → (fun _ => false) ∈ S → (∀ f ∈ inputs, f ∈ S) → P 0 S →
      (∀ (k : ℕ) (T : Set F) (op : GateOp) (pins : List F),
        P k T → (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
        pins.length ≤ 2 → (∀ f ∈ pins, f ∈ T) →
        (fun x => op.eval (pins.map fun f => f x)) ∉ T →
        P (k+1) (insert (fun x => op.eval (pins.map fun f => f x)) T)) →
      ∃ (k : ℕ) (T : Set F), k ≤ C.size ∧ P k T ∧
        (fun x => C.eval (inputs.map fun f => f x)) ∈ T)
    (search : let F := (Fin 10 → Bool) → Bool
      let B : Set F := insert (fun _ => false) (insert (fun x => x 0 && x 2)
        (Set.range (fun i : Fin 10 => (fun x : Fin 10 → Bool => x i))))
      ∀ (a : List F), a.length ≤ 2 → (∀ f ∈ a, f ∈ B) →
      ∃ P : ℕ → Set F → Prop,
        P 0 (insert (fun x => GateOp.and.eval (a.map fun f => f x)) B) ∧
        (∀ (k : ℕ) (T : Set F) (op : GateOp) (pins : List F),
        P k T → (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
        pins.length ≤ 2 → (∀ f ∈ pins, f ∈ T) →
        (fun x => op.eval (pins.map fun f => f x)) ∉ T →
        P (k+1) (insert (fun x => op.eval (pins.map fun f => f x)) T)) ∧
        ∀ (k : ℕ) (T : Set F), k ≤ 17 → P k T →
        (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
            (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
          (fun e => x e.1 && x e.2)) ∉ T) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p hfan hsize first
  obtain ⟨g, gs, hg, hop⟩ := first
  let F := (Fin 10 → Bool) → Bool
  let B : Set F := insert (fun _ => false) (insert (fun x => x 0 && x 2)
        (Set.range (fun i : Fin 10 => (fun x : Fin 10 → Bool => x i))))
  let inputs : List F := (List.ofFn fun i : Fin 10 => (fun x : Fin 10 → Bool => x (p i))) ++
    [fun x => x 0 && x 2]
  let zero : F := fun _ => false
  have hz : zero ∈ B := Set.mem_insert _ _
  have hi : ∀ f ∈ inputs, f ∈ B := by
    intro f hf
    rcases List.mem_append.mp hf with h|h
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨p j, rfl⟩)
    · simp only [List.mem_singleton] at h
      exact h ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  let pins := g.inputs.map (fun i => inputs.getD i zero)
  have read (i : ℕ) : inputs.getD i zero ∈ B := by
    by_cases h : i < inputs.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hi _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact hz
  have hgm : g ∈ C.gates := by simp [hg]
  have plen : pins.length ≤ 2 := by simpa [pins] using (hfan g hgm).2
  have pmem : ∀ f ∈ pins, f ∈ B := by
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact read i
  let feature : F := fun x => GateOp.and.eval (pins.map fun f => f x)
  let S := insert feature B
  obtain ⟨P, start, step, finish⟩ := search pins plen pmem
  let D : Circuit := ⟨gs, C.output⟩
  have hd : FanInTwo D := fun a ha => hfan a (hg ▸ List.mem_cons_of_mem g ha)
  have hin : ∀ f ∈ inputs ++ [feature], f ∈ S := by
    intro f hf
    rcases List.mem_append.mp hf with h|h
    · exact Set.mem_insert_of_mem _ (hi _ h)
    · simp only [List.mem_singleton] at h
      exact h ▸ Set.mem_insert _ _
  obtain ⟨k,T,hk,hP,hout⟩ := trace D (inputs ++ [feature]) S P hd
    (Set.mem_insert_of_mem _ hz) hin start step
  have hs : D.size + 1 = C.size := by
    change gs.length + 1 = C.gates.length
    rw [hg]
    rfl
  have exclude := finish k T (by omega) hP
  have materialize (x : Fin 10 → Bool) : inputs.map (fun f => f x) =
      List.ofFn (x ∘ p) ++ [x 0 && x 2] := by
    simp [inputs,Function.comp_def]
  have wire (x : Fin 10 → Bool) (i : ℕ) :
      (inputs.getD i zero) x = (inputs.map (fun f => f x)).getD i false := by
    by_cases h : i < inputs.length
    · simp [h]
    · have hh : inputs.length ≤ i := by omega
      rw [List.getD_eq_default _ _ hh,List.getD_eq_default _ _ (by simpa using hh)]
  have peel (x : Fin 10 → Bool) :
      D.eval ((inputs ++ [feature]).map (fun f => f x)) =
        C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) := by
    rw [←materialize]
    let update := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    change (gs.foldl update _).getD C.output false = (C.gates.foldl update _).getD C.output false
    simp only [hg,List.foldl_cons,update,List.map_append,
      List.map_cons,List.map_nil, feature, pins,List.map_map,Function.comp_def,wire,hop]
  by_contra! equal
  apply exclude
  have identify : (fun x : Fin 10 → Bool => D.eval ((inputs ++ [feature]).map (fun f => f x))) =
      (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
            (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
          (fun e => x e.1 && x e.2)) := by
    funext x
    rw [peel,equal x]
    simp [List.any_cons,Bool.or_assoc]
  exact identify ▸ hout
