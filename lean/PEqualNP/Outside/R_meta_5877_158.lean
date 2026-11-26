import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CircuitMoves PEqualNP.ReadTwo PEqualNP.GenericRejection

-- A joint zero restriction deletes the base support and an activated eight-vertex test.
-- The three classes have 45, 41, or 37 edges after this restriction.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_5877_158
    (specialize :
      ∀ (C : Circuit) (i : Fin 14), Monotone2 C → C.size ≤ 124 →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ (fun x : Fin 42 → Bool => ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)) ∧ x a = true ∧ x b = true) x) →
        let m : Nat := (([693637218693,214750724172,43100670213,2201724715076,429513539622,10838245382,214756769811,412337856832,154640061441,1718003696225,1387274437386,3436007392450,3436108316976,1168315262978] : List Nat).getD i.val 0)
        let active (x : Nat) := ∃ j, isAnd C j ∧ gateVal 42 C j (fun w => x.testBit w.val) = true
        active 148193411399 → active m →
        33 ≤ ((Finset.range C.size).filter (fun j => ((C.gates[j]?.map (fun g => GateOp.rec false true false (fun _ => false) false g.op)).getD false && !gateVal 42 C j (fun w => m.testBit w.val)) = true)).card →
        let k : Nat := (if i.val<4 then 67 else if i.val<9 then 72 else 76)
        ∃ (g : (j : Fin k) → Fin (C.size-j.val)) (r : Fin k → Nat),
        ∀ x : Fin 42 → Bool, (∀ w, (148193411399 ||| m).testBit w.val = true → x w = false) →
          (((List.finRange k).foldl (fun T j => eraseGate 42 T (g j).val (r j)) C).eval (List.ofFn x)) = C.eval (List.ofFn x))
    (residual :
      ∀ (i : Fin 14) (C : Circuit), Monotone2 C →
        let m : Nat := (([693637218693,214750724172,43100670213,2201724715076,429513539622,10838245382,214756769811,412337856832,154640061441,1718003696225,1387274437386,3436007392450,3436108316976,1168315262978] : List Nat).getD i.val 0)
        (∀ x : Fin 42 → Bool, (∀ w, (148193411399 ||| m).testBit w.val = true → x w = false) →
          (C.eval (List.ofFn x) = true ↔ (fun x : Fin 42 → Bool => ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val)%21 ∈ ([0,5,7,17,20] : List Nat)) ∧ x a = true ∧ x b = true) x)) → (if i.val<4 then 58 else if i.val<9 then 53 else 49) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (124 : ℕ) →       (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) →         have x5 : List ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (3436108316976 : ℕ), (154640061441 : ℕ), (1168315262978 : ℕ)];         have x6 : ℕ → Fin (42 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (42 : ℕ)) => x6.testBit ↑x7;         have x7 : (Fin (42 : ℕ) → Bool) → Prop := fun (x7 : Fin (42 : ℕ) → Bool) => ∃ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn x7)).getD ((42 : ℕ) + x8) Bool.false = Bool.true;         have x8 : ℕ → Finset ℕ := fun (x8 : ℕ) => {x9 ∈ Finset.range x1.size | ((Option.map (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x10.op) x1.gates[x9]?).getD Bool.false && !(x1.wires (List.ofFn (x6 x8))).getD ((42 : ℕ) + x9) Bool.false) = Bool.true};         (x7 fun (x9 : Fin (42 : ℕ)) => Decidable.decide (↑x9 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)])) → ((∃ x10 ∈ x5, x7 (x6 x10)) ∧ ∀ x10 ∈ x5, (33 : ℕ) ≤ (x8 x10).card) → False := by
  intro C mono small correct ms word hit silent base more
  obtain ⟨⟨m,hm,hmHit⟩,enough⟩ := more
  let labels : List Nat := [693637218693,214750724172,43100670213,2201724715076,429513539622,10838245382,214756769811,412337856832,154640061441,1718003696225,1387274437386,3436007392450,3436108316976,1168315262978]
  have represented (a : Nat) (ha : a ∈ ms) : ∃ i : Fin 14, labels.getD i.val 0 = a := by
    change a ∈ _ at ha
    have enc : ∀ v ∈ ms, ∃ i : Fin 14, labels.getD i.val 0 = v := by decide +kernel
    exact enc a ha
  obtain ⟨i,hi⟩ := represented m hm
  let K : Nat := if i.val < 4 then 67 else if i.val < 9 then 72 else 76
  have active (a : Nat) (h : hit (word a)) :
      ∃ j, isAnd C j ∧ gateVal 42 C j (fun w => a.testBit w.val) = true := by
    obtain ⟨j,g,hg,ho,truth⟩ := h
    obtain ⟨bound,rfl⟩ := List.getElem?_eq_some_iff.mp hg
    refine ⟨j,⟨bound,?_⟩,truth⟩
    change (C.gates.getD j _).op = _
    rw [List.getD_eq_getElem _ _ bound]
    exact ho
  have baseWord : (fun w : Fin 42 => (148193411399 : Nat).testBit w.val) =
      (fun w : Fin 42 => decide (w.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List Nat))) := by
    funext w
    exact (show ∀ j : Fin 42, (148193411399 : Nat).testBit j.val =
      decide (j.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List Nat)) by decide +kernel) w
  have hbase : hit (word 148193411399) := by rw [show word 148193411399 = _ from baseWord]; exact base
  have h0 := specialize C i mono small correct (active _ hbase)
  change labels.getD i.val 0 = m at hi
  change (∃ j, isAnd C j ∧ gateVal 42 C j (fun w => (labels.getD i.val 0).testBit w.val) = true) → _ at h0
  rw [hi] at h0
  obtain ⟨g,r,agrees⟩ := h0 (active _ hmHit) (enough m hm)
  let edit (T : Circuit) (i : Fin K) := eraseGate 42 T (g i).val (r i)
  have erases {T : Circuit} (i : Fin K) (ok : (g i).val < T.size) (mt : Monotone2 T) :
      (edit T i).size + 1 = T.size ∧ Monotone2 (edit T i) := by
    change (g i).val < T.gates.length at ok
    unfold edit eraseGate
    rw [ite_eq_left ok]
    constructor
    · change (T.gates.take _ ++ (T.gates.drop _).map _).length + 1 = T.gates.length
      rw [List.length_append,List.length_take,List.length_map,List.length_drop,Nat.min_eq_left (Nat.le_of_lt ok)]
      omega
    · intro z hz
      simp only [List.mem_append,List.mem_map] at hz
      rcases hz with before | ⟨a,ha,rfl⟩
      · exact mt _ (List.mem_of_mem_take before)
      · obtain ⟨ops,len⟩ := mt _ (List.mem_of_mem_drop ha)
        exact ⟨ops,by simpa using len⟩
  have priced (ix : List (Fin K)) (T : Circuit) (pos : ℕ) (mT : Monotone2 T)
      (budget : T.size + pos = C.size) (keys : ∀ j : Fin ix.length, (ix.get j).val = pos + j.val) :
      (ix.foldl edit T).size + ix.length = T.size ∧ Monotone2 (ix.foldl edit T) := by
    induction ix generalizing T pos with
    | nil => exact ⟨by simp,mT⟩
    | cons i tail ih =>
      have first := keys ⟨0,by simp⟩
      change i.val = pos + 0 at first
      have admiss : (g i).val < T.size := by
        have z := (g i).isLt
        change (g i).val < C.size - i.val at z
        omega
      obtain ⟨cost,okay⟩ := erases i admiss mT
      have bound : (edit T i).size + (pos+1) = C.size := by omega
      have ktail (j : Fin tail.length) : (tail.get j).val = (pos+1) + j.val := by
        have z := keys ⟨j.val + 1, by simp⟩
        change (tail.get j).val = pos + (j.val+1) at z
        omega
      obtain ⟨n,filtered⟩ := ih (edit T i) (pos+1) okay bound ktail
      refine ⟨?_,filtered⟩
      change (tail.foldl edit (edit T i)).size + (tail.length+1) = T.size
      omega
  have calculation := priced (List.finRange K) C 0 mono (by omega) (by intro j; simp)
  let D := (List.finRange K).foldl edit C
  have cost : D.size + K = C.size := by
    simpa only [List.length_finRange] using calculation.1
  have low := residual i D calculation.2 (by
    intro x hx
    change ∀ w, (148193411399 ||| labels.getD i.val 0).testBit w.val = true → x w = false at hx
    rw [hi] at hx
    rw [show D.eval (List.ofFn x) = C.eval (List.ofFn x) from agrees x hx]
    exact correct x)
  dsimp only [K] at cost
  by_cases a : i.val < 4 <;> by_cases b : i.val < 9 <;> simp only [a,b,ite_true,ite_false] at cost low <;> omega
