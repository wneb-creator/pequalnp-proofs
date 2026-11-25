import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On an independent input, only an OR path can carry a true literal past a safe AND.
-- A first AND violating safety has at most two operands and therefore a witness of size at most two.
-- This lets the second step specify the new circuit entirely on singletons and pairs.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_1904_493
    (singletons : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let evalGraph := fun (x : Fin n → Bool) => decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    let on := fun (S : Finset (Fin n)) (i : Fin n) => decide (i ∈ S)
    let one := fun (C : Circuit) => ∀ j g, C.gates[j]?=some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 → (C.wires (List.ofFn (on S))).getD (n+j) false = false
    (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
    (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
    ∃ C : Circuit, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = evalGraph x) ∧
      (∀ T : Circuit, Monotone2 T → (∀ x, T.eval (List.ofFn x) = evalGraph x) → C.size ≤ T.size) ∧ one C)
    (pairs : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let evalGraph := fun (x : Fin n → Bool) => decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    let on := fun (S : Finset (Fin n)) (i : Fin n) => decide (i ∈ S)
    let one := fun (C : Circuit) => ∀ j g, C.gates[j]?=some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 → (C.wires (List.ofFn (on S))).getD (n+j) false = false
    (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
    (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
    ∀ C : Circuit, Monotone2 C → (∀ x, C.eval (List.ofFn x) = evalGraph x) → one C →
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
      (∀ u v, G.Adj u v → D.eval (List.ofFn (on {u,v}))=true) ∧
      (∀ u, D.eval (List.ofFn (on {u}))=false) ∧
      (∀ j g, D.gates[j]?=some g → g.op = GateOp.and → ∀ S : Finset (Fin n), S.card ≤ 2 →
        (D.wires (List.ofFn (on S))).getD (n+j) false=true →
        ∃ a ∈ S, ∃ b ∈ S, G.Adj a b)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  classical
  have and_eval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have or_eval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let trace {n} (gs : List Gate) (x : Fin n → Bool) := gs.foldl step (List.ofFn x)
  let pin {n} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) := (trace gs x).getD i false
  let val {n} (gs : List Gate) (g : Gate) (x : Fin n → Bool) := g.op.eval (g.inputs.map (pin gs x))
  let hit {n} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) := ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true
  let mask {n} (S : Finset (Fin n)) (u : Fin n) := decide (u ∈ S)
  let tiny {n} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
    ∀ j g, C.gates[j]? = some g → g.op = .and → ∀ S : Finset (Fin n), S.card ≤ 2 →
      pin C.gates (mask S) (n+j) = true → hit G (mask S)
  have tr_snoc {n} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
      trace (gs++[g]) x = trace gs x ++ [val gs g x] := by
    simp only [trace, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have tr_len {n} (gs : List Gate) (x : Fin n → Bool) : (trace gs x).length = n + gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [trace]
    | append_singleton l g ih => simp [tr_snoc,ih,Nat.add_assoc]
  have prefix_tail (w : List Bool) (rest : List Gate) : ∃ t, rest.foldl step w = w ++ t := by
    induction rest generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih =>
      obtain ⟨t,e⟩ := ih (step w g)
      exact ⟨_ :: t, by simpa [List.foldl_cons,step,List.append_assoc] using e⟩
  have gate_value {n} (pre rest : List Gate) (g : Gate) (x : Fin n → Bool) :
      pin (pre ++ g::rest) x (n + pre.length) = val pre g x := by
    have e : trace (pre ++ g::rest) x = rest.foldl step (trace pre x ++ [val pre g x]) := by
      simp only [trace, List.foldl_append, List.foldl_cons]
      rfl
    obtain ⟨t,et⟩ := prefix_tail (trace pre x ++ [val pre g x]) rest
    dsimp only [pin]
    rw [e,et,List.append_assoc]
    have hl := tr_len pre x
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),← hl,Nat.sub_self]
    rfl
  let roots {n} (gs : List Gate) (x : Fin n → Bool) : Prop := ∀ k, pin gs x k = true →
      ∃ u, x u = true ∧ ∀ z : Fin n → Bool, z u = true → pin gs z k = true
  have reject {n G C} (checks : tiny G C) (M : Monotone2 C) {x : Fin n → Bool} (bad : ¬hit G x)
      {pre rest : List Gate} {g : Gate} (split : C.gates = pre ++ g :: rest) (hg : g.op = .and)
      (prior : roots pre x) : val pre g x ≠ true := by
    intro lit
    have gate_mem : g ∈ C.gates := by simp [split]
    have gate_at : C.gates[pre.length]? = some g := by simp [split]
    have ht : ∀ i ∈ g.inputs, pin pre x i = true := by simpa [val,hg,and_eval,or_eval] using lit
    have each (i : {k // k ∈ g.inputs}) := prior i (ht i i.property)
    choose u on force using each
    let S := (g.inputs.attach.map u).toFinset
    have bound : S.card ≤ 2 :=
      (List.toFinset_card_le _).trans (by simpa using (M g gate_mem).2)
    have sub : ∀ a ∈ S, x a = true := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact on i
    have still : ∀ k ∈ g.inputs, pin pre (mask S) k = true := by
      intro k hk
      let q : {i // i ∈ g.inputs} := ⟨k,hk⟩
      apply force q
      apply decide_eq_true
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, List.mem_attach _ _, rfl⟩)
    have active : pin C.gates (mask S) (n+pre.length) = true := by
      rw [split,gate_value]
      simpa [val,hg,and_eval,or_eval] using still
    obtain ⟨a,b,adj,ha,hb⟩ := checks _ _ gate_at hg S bound active
    exact bad ⟨a,b,adj,sub a (of_decide_eq_true ha),sub b (of_decide_eq_true hb)⟩
  have provenance {n G C} (checks : tiny G C) (M : Monotone2 C) {x : Fin n → Bool} (bad : ¬hit G x)
      (pre : List Gate) : (∃ rest, C.gates = pre ++ rest) → roots pre x := by
    induction pre using List.reverseRecOn with
    | nil =>
      intro _ k hk
      by_cases h : k < n
      · refine ⟨⟨k,h⟩,by simpa [pin,trace,List.getD,List.getElem?_ofFn,h] using hk,?_⟩
        intro z htrue
        simpa [pin,trace,List.getD,List.getElem?_ofFn,h] using htrue
      · simp [pin,trace,List.getD,List.getElem?_ofFn,h] at hk
    | append_singleton pre g ih =>
      rintro ⟨rest,split⟩
      have total : C.gates = pre ++ g :: rest := by simpa [List.append_assoc] using split
      have prior := ih ⟨_,total⟩
      have member : g ∈ C.gates := by simp [total]
      intro k hk
      by_cases old : k < n+pre.length
      · have keep (y : Fin n → Bool) : pin (pre++[g]) y k = pin pre y k := by
          simp only [pin,tr_snoc]
          exact List.getD_append _ _ _ _ (by rwa [tr_len])
        rw [keep] at hk
        obtain ⟨u,hu,hu'⟩ := prior k hk
        exact ⟨u,hu,fun z hz => (keep z).trans (hu' z hz)⟩
      · have access (y : Fin n → Bool) : pin (pre++[g]) y k = [val pre g y].getD (k-(n+pre.length)) false := by
          dsimp only [pin]
          rw [tr_snoc,List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [tr_len]; omega),tr_len]
          rfl
        rw [access] at hk
        cases e : k-(n+pre.length) with
        | zero =>
          rw [e] at hk
          change val pre g x = true at hk
          have shape : g.op = .and ∨ g.op = .or := by simpa using (M g member).1
          rcases shape with ha|ho
          · exact False.elim (reject checks M bad total ha prior hk)
          · have many : ∃ i ∈ g.inputs, pin pre x i = true := by simpa [val,ho,and_eval,or_eval] using hk
            obtain ⟨i,hi,uses⟩ := many
            obtain ⟨u,hu,fu⟩ := prior i uses
            refine ⟨u,hu,?_⟩
            intro z hz
            rw [access,e]
            change val pre g z = true
            simpa [val,ho,and_eval,or_eval] using (show ∃ j ∈ g.inputs, pin pre z j = true from ⟨i,hi,fu z hz⟩)
        | succ d => simp [e,List.getD] at hk
  have safety {n G C} (checks : tiny G C) (M : Monotone2 C) :
      ∀ j g, C.gates[j]? = some g → g.op = .and → ∀ x : Fin n → Bool, pin C.gates x (n+j) = true → hit G x := by
    intro j g entry and x lit
    by_contra nope
    obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp entry
    let pre := C.gates.take j
    let rest := C.gates.drop (j+1)
    have split : C.gates = pre ++ g :: rest := by
      rw [← hg]
      exact (List.take_append_drop j C.gates).symm.trans (by rw [List.drop_eq_getElem_cons hj])
    have plen : pre.length = j := by simp [pre,Nat.min_eq_left (Nat.le_of_lt hj)]
    have prior := provenance checks M nope pre ⟨_,split⟩
    have Z := reject checks M nope split and prior
    apply Z
    rwa [← gate_value pre rest g x,← split,plen]
  have pin_mono {n} (gs : List Gate) (allOps : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) (k : ℕ) :
      pin gs x k = true → pin gs y k = true := by
    induction gs using List.reverseRecOn generalizing k with
    | nil =>
      by_cases lt : k<n
      · simpa [pin,trace,List.getD,lt] using h ⟨k,lt⟩
      · simp [pin,trace,List.getD,lt]
    | append_singleton l g ih =>
      have base := ih (fun a ha => allOps a (List.mem_append_left _ ha))
      by_cases old : k < n+l.length
      · have keep (z : Fin n → Bool) : pin (l++[g]) z k = pin l z k := by
          simp only [pin,tr_snoc]
          exact List.getD_append _ _ _ _ (by rwa [tr_len])
        simpa only [keep] using base k
      · have access (z : Fin n → Bool) : pin (l++[g]) z k = [val l g z].getD (k-(n+l.length)) false := by
          dsimp only [pin]
          rw [tr_snoc,List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [tr_len]; omega),tr_len]
          rfl
        rw [access,access]
        cases k-(n+l.length) with
        | succ j => simp [List.getD]
        | zero =>
          change val l g x = true → val l g y = true
          rcases allOps g (by simp) with ha|ho
          · simp only [val,ha,and_eval,or_eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
            exact fun p j hj => base j (p j hj)
          · simp only [val,ho,and_eval,or_eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
            rintro ⟨j,hj,on⟩
            exact ⟨j,hj,base j on⟩
  have correct {n} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C} (checks : tiny G C) (M : Monotone2 C)
      (edge : ∀ u v, G.Adj u v → C.eval (List.ofFn (mask {u,v})) = true)
      (single : ∀ u : Fin n, C.eval (List.ofFn (mask {u})) = false) :
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true) := by
    classical
    intro x
    change pin C.gates x C.output = decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    by_cases good : hit G x
    · rw [decide_eq_true good]
      obtain ⟨u,v,uv,hu,hv⟩ := good
      let S : Finset (Fin n) := {u,v}
      have uvsub : ∀ i, mask S i = true → x i = true := by
        intro i on
        simp only [mask,decide_eq_true_eq,S,Finset.mem_insert,Finset.mem_singleton] at on
        rcases on with rfl|rfl
        · exact hu
        · exact hv
      exact pin_mono C.gates (fun g hg => by simpa using (M g hg).1) uvsub C.output (edge u v uv)
    · rw [decide_eq_false good]
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨u,hu,force⟩ := provenance checks M good C.gates ⟨[],by simp⟩ C.output on
      have active := force (mask {u}) (by simp [mask])
      change C.eval (List.ofFn (mask {u})) = true at active
      rw [single u] at active
      contradiction
  intro n G inst tri square
  obtain ⟨C, cm, cf, least, ones⟩ := singletons n G tri square
  obtain ⟨D, dm, cost, edges, single, test⟩ := pairs n G tri square C cm cf ones
  have checks : tiny G D := by
    intro j g entry hg S hS active
    obtain ⟨a,ha,b,hb,adj⟩ := test j g entry hg S hS active
    exact ⟨a,b,adj,decide_eq_true ha,decide_eq_true hb⟩
  exact ⟨D,dm,correct checks dm edges single,fun T tm tf => cost.trans (least T tm tf),
    safety checks dm⟩
