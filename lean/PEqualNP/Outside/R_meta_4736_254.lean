import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- The first child is the pair-clean graph bound from L_meta_1892.
-- The finite child receives the first OR as an extra input. Its target tests are
-- the twelve edges and twelve maximal independent sets. It only needs to rule
-- out an AND that accepts one of the twenty-four two-vertex nonedges.
-- A matching sixteen-gate construction takes the OR of five stars, centered
-- at 1, 0, 3, 7 and 8 with leaves 026, 45, 248, 25 and 65 respectively.
-- Start the first star by forming the prescribed OR of inputs 0 and 2.
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_4736_254
    (cleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      (∀ k < C.gates.length, (gateAt C k).op = .and → ∀ u v : Fin n, ¬ G.Adj u v →
        gateVal n C k (pairInput u v) = false) →
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeFinset.card + T.card ≤ C.size + 1)
    (finite : let seed (m : ℕ) := List.ofFn (fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 2]
      ∀ D : Circuit, Monotone2 D → D.size ≤ 14 → D.output ≤ 24 →
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      (∀ a b : Fin 9, a ≠ b → (⟨.and,[a.val,b.val]⟩ : Gate) ∉ D.gates) →
      (∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), D.eval (seed m) = true) →
      (∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), D.eval (seed m) = false) →
      ∀ j : Fin D.size, (D.gates.get j).op = GateOp.and →
      ∀ m ∈ ([5,9,10,18,20,34,36,40,48,65,68,72,80,96,129,130,136,144,192,257,258,260,272,384] : List ℕ), (D.wires (seed m)).getD (10+j.val) false = false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (∀ (x4 x5 : Fin (9 : ℕ)), x4 ≠ x5 → { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x4, ↑x5] : PEqualNP.CircuitLowerBounds.Gate } ∉ x1.gates) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C mono first noRaw computes
  let f := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let es : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
  let G := edgeGraph 9 es
  have squareFree : ∀ a b c d : Fin 9, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    decide
  have edgeCount : 12 ≤ G.edgeFinset.card := by
    decide
  have cover : ∀ T : Finset (Fin 9),
      (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) → 5 ≤ T.card := by
    decide
  have graphEq : f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext x
    have allx : ∀ y : Fin 9 → Bool,
        f y = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y := by
      decide
    exact allx x


  let bits (m : ℕ) (u : Fin 9) := m.testBit u.val
  let seed (m : ℕ) := List.ofFn (bits m) ++ [m.testBit 0 || m.testBit 2]
  let pos : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
  let neg : List ℕ := [42,50,69,104,116,138,201,208,261,276,385,402]
  let non : List ℕ := [5,9,10,18,20,34,36,40,48,65,68,72,80,96,129,130,136,144,192,257,258,260,272,384]
  have hit : ∀ m ∈ pos, f (bits m) = true := by decide +kernel
  have miss : ∀ m ∈ neg, f (bits m) = false := by decide +kernel
  have extendPair : ∀ a b : Fin 9, ¬ G.Adj a b →
      ∃ m ∈ non, bits m a = true ∧ bits m b = true := by
    intro a b h
    have allPairs : ∀ u v : Fin 9, ¬ G.Adj u v →
        non.any (fun m => bits m u && bits m v) = true := by decide +kernel
    obtain ⟨m, hm, both⟩ := List.any_eq_true.mp (allPairs a b h)
    exact ⟨m,hm,by simpa only [Bool.and_eq_true] using both⟩
  have wireMonotone (C : Circuit) (hC : Monotone2 C)
      (x y : Fin 9 → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
      (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    classical
    let step (v : List Bool) (g : Gate) :=
      v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]
    let run (gs : List Gate) (v : List Bool) := gs.foldl step v
    let rel (u v : List Bool) :=
      u.length = v.length ∧ ∀ j, u.getD j false = true → v.getD j false = true
    have gateMono (g : Gate) (u v : List Bool) (hr : rel u v)
        (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
        g.op.eval (g.inputs.map fun j => u.getD j false) = true →
          g.op.eval (g.inputs.map fun j => v.getD j false) = true := by
      have allMono (is : List ℕ) :
          (is.map fun j => u.getD j false).all id = true →
            (is.map fun j => v.getD j false).all id = true := by
        induction is with
        | nil => simp
        | cons a rest ih =>
          simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
          intro h
          exact ⟨hr.2 a h.1, ih h.2⟩
      have anyMono (is : List ℕ) :
          (is.map fun j => u.getD j false).any id = true →
            (is.map fun j => v.getD j false).any id = true := by
        induction is with
        | nil => simp
        | cons a rest ih =>
          simp only [List.map_cons, List.any_cons, Bool.or_eq_true]
          intro h
          exact h.elim (fun h => Or.inl (hr.2 a h)) (fun h => Or.inr (ih h))
      rcases hop with hop | hop
      · rw [hop]
        exact allMono g.inputs
      · rw [hop]
        exact anyMono g.inputs
    have appendRel (u v : List Bool) (a b : Bool) (hr : rel u v)
        (hab : a = true → b = true) : rel (u ++ [a]) (v ++ [b]) := by
      refine ⟨by simp [hr.1], fun j hj => ?_⟩
      by_cases h : j < u.length
      · rw [List.getD_append _ _ _ _ h] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hr.2 j hj
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hj
        rw [List.getD_append_right _ _ _ _ (by omega), ← hr.1]
        by_cases heq : j = u.length
        · simp only [heq, Nat.sub_self, List.getD_cons_zero] at hj ⊢
          exact hab hj
        · have hn : 0 < j - u.length := by omega
          have hd : [a].getD (j - u.length) false = false := by
            apply List.getD_eq_default
            simp
            omega
          rw [hd] at hj
          contradiction
    have runMono (gs : List Gate) (u v : List Bool) (hr : rel u v)
        (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
        rel (run gs u) (run gs v) := by
      induction gs generalizing u v with
      | nil => exact hr
      | cons g gs ih =>
        change rel (run gs (step u g)) (run gs (step v g))
        apply ih
        · exact appendRel _ _ _ _ hr (gateMono g u v hr (hgs g (by simp)))
        · intro g' hg'
          exact hgs g' (by simp [hg'])
    have initial : rel (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp, fun j hj => ?_⟩
      by_cases h : j < 9
      · let k : Fin 9 := ⟨j, h⟩
        have get (z : Fin 9 → Bool) : (List.ofFn z).getD j false = z k := by
          rw [List.getD_eq_getElem _ _ (by simp [h]), List.getElem_ofFn]
        rw [get x] at hj
        rw [get y]
        exact hxy k hj
      · rw [List.getD_eq_default _ false (by simp; omega)] at hj
        contradiction
    have allowed : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have hg' := (hC g hg).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg'
    exact (runMono C.gates _ _ initial allowed).2 w

  have clampTail (D : Circuit) (hf : Monotone2 D) (hs : D.size ≤ 14)
      (hno : ∀ g ∈ D.gates, g.op = GateOp.and → ∀ a b : Nat,
        a < 9 → b < 9 → a ≠ b → a ∈ g.inputs → b ∈ g.inputs → False) :
      ∃ E : Circuit, Monotone2 E ∧ E.size = D.size ∧
        (∀ g ∈ E.gates, ∀ i ∈ g.inputs, i ≤ 24) ∧ E.output ≤ 24 ∧
        (∀ j : Nat, (E.gates[j]?).map Gate.op = (D.gates[j]?).map Gate.op) ∧
        (∀ g ∈ E.gates, g.op = GateOp.and → ∀ a b : Nat,
          a < 9 → b < 9 → a ≠ b → a ∈ g.inputs → b ∈ g.inputs → False) ∧
        (∀ l : List Bool, l.length = 10 → E.wires l = D.wires l) ∧
        (∀ l : List Bool, l.length = 10 → E.eval l = D.eval l) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    have lengthRun (gs : List Gate) (w : List Bool) :
        (run gs w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp [run]
      | cons g gs ih =>
        change (run gs (step w g)).length = _
        rw [ih]
        simp [step]
        omega
    let clip (i : Nat) := min i 24
    let clipGate (g : Gate) : Gate := ⟨g.op, g.inputs.map clip⟩
    let clipped (D : Circuit) : Circuit := ⟨D.gates.map clipGate, clip D.output⟩
    have clipRead (w : List Bool) (hw : w.length ≤ 24) (i : Nat) :
        w.getD (clip i) false = w.getD i false := by
      change w.getD (min i 24) false = _
      by_cases h : i ≤ 24
      · rw [min_eq_left h]
      · rw [min_eq_right (by omega : 24 ≤ i), List.getD_eq_default _ false hw,
          List.getD_eq_default _ false (by omega : w.length ≤ i)]
    have clipRun (gs : List Gate) (w : List Bool) (hw : w.length + gs.length ≤ 24) :
        run (gs.map clipGate) w = run gs w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change run (gs.map clipGate) (step w (clipGate g)) = run gs (step w g)
        have same : step w (clipGate g) = step w g := by
          simp only [step, clipGate, List.map_map, Function.comp_def, clipRead w (by omega)]
        rw [same]
        apply ih
        simp only [List.length_cons] at hw
        simp [step]
        omega
    have hlen : D.gates.length ≤ 14 := hs
    have mono : Monotone2 (clipped D) := by
      intro g hg
      obtain ⟨g0, hm, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hf g0 hm).1, by simpa [clipGate] using (hf g0 hm).2⟩
    have indices : ∀ g ∈ (clipped D).gates, ∀ i ∈ g.inputs, i ≤ 24 := by
      intro g hg i hi
      obtain ⟨g0, hm, rfl⟩ := List.mem_map.mp hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact min_le_right j 24
    have forbidden : ∀ g ∈ (clipped D).gates, g.op = GateOp.and → ∀ a b : Nat,
        a < 9 → b < 9 → a ≠ b → a ∈ g.inputs → b ∈ g.inputs → False := by
      intro g hg hop a b ha hb hab hga hgb
      obtain ⟨g0, hm, rfl⟩ := List.mem_map.mp hg
      obtain ⟨a0, ha0, ea⟩ := List.mem_map.mp hga
      obtain ⟨b0, hb0, eb⟩ := List.mem_map.mp hgb
      have ea' : a0 = a := by dsimp [clip] at ea; omega
      have eb' : b0 = b := by dsimp [clip] at eb; omega
      subst a0
      subst b0
      exact hno g0 hm hop a b ha hb hab ha0 hb0
    have wires (l : List Bool) (hl : l.length = 10) :
        (clipped D).wires l = D.wires l := by
      change run (D.gates.map clipGate) l = run D.gates l
      apply clipRun
      omega
    refine ⟨clipped D, mono, ?_, indices, min_le_right _ 24, ?_, forbidden, wires, ?_⟩
    · change (D.gates.map clipGate).length = D.gates.length
      simp only [List.length_map]
    · intro j
      simp [clipped, clipGate, List.getElem?_map, Function.comp_def]
    · intro l hl
      change (run (D.gates.map clipGate) l).getD (clip D.output) false =
        (run D.gates l).getD D.output false
      rw [clipRun _ _ (by omega), clipRead _ (by rw [lengthRun]; omega)]

  by_contra! small
  have smallC : C.size ≤ 15 := by omega
  have prepared : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      ∀ e w : Fin 9, ¬ G.Adj e w → gateVal 9 C k (pairInput e w) = false := by
    rcases C with ⟨gs,out⟩
    cases gs with
    | nil => intro k hk; exact (Nat.not_lt_zero k hk).elim
    | cons g gs =>
      let D : Circuit := ⟨gs,out⟩
      let step (ws : List Bool) (a : Gate) := ws ++ [a.op.eval (a.inputs.map fun i => ws.getD i false)]
      have keep (ls : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
          (ls.foldl step ws).getD i false = ws.getD i false := by
        induction ls generalizing ws with
        | nil => rfl
        | cons h ls ih =>
          change (ls.foldl step (step ws h)).getD i false = _
          rw [ih _ (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hi
      have headEval (x : Fin 9 → Bool) :
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
        have h := first x
        change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
        rw [keep _ _ _ (by simp [step])] at h
        simpa only [step, List.getD_append_right _ _ _ _ (by simp : (List.ofFn x).length ≤ 9),
          List.length_ofFn, Nat.sub_self, List.getD_cons_zero] using h
      have notAnd : g.op ≠ GateOp.and := by
        intro op
        have all (x : Fin 9 → Bool) :
            (g.inputs.map fun i => (List.ofFn x).getD i false).all id = (x 0 || x 2) := by
          have h := headEval x
          rw [op] at h
          exact h
        cases pins : g.inputs with
        | nil =>
          have h := all (fun _ => false)
          rw [pins] at h
          contradiction
        | cons a rest =>
          have singleton (u : Fin 9) (hu : u = 0 ∨ u = 2) : a = u.val := by
            let x : Fin 9 → Bool := fun i => decide (i = u)
            have on : (x 0 || x 2) = true := by rcases hu with rfl | rfl <;> decide
            have h := all x
            rw [pins,on] at h
            simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
            have read := h.1
            change (List.ofFn x).getD a false = true at read
            by_cases ha : a < 9
            · rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getElem_ofFn] at read
              exact congrArg Fin.val (of_decide_eq_true read)
            · rw [List.getD_eq_default _ false (by simp; omega)] at read
              contradiction
          have zero := singleton 0 (Or.inl rfl)
          have two := singleton 2 (Or.inr rfl)
          omega
      have wires (x : Fin 9 → Bool) :
          (⟨g :: gs,out⟩ : Circuit).wires (List.ofFn x) =
          D.wires (List.ofFn x ++ [x 0 || x 2]) := by
        change gs.foldl step (List.ofFn x ++ [_]) = gs.foldl step _
        rw [headEval x]
      have hm : Monotone2 D := fun a ha => mono a (List.mem_cons_of_mem _ ha)
      have hs : D.size ≤ 14 := by
        change (g :: gs).length ≤ 15 at smallC
        change gs.length ≤ 14
        simp only [List.length_cons] at smallC
        omega
      have rawD : ∀ a b : Fin 9, a ≠ b → (⟨.and,[a.val,b.val]⟩ : Gate) ∉ D.gates :=
        fun a b h mem => noRaw a b h (List.mem_cons_of_mem _ mem)
      have exclude (z : Gate) (hz : z ∈ D.gates) (hop : z.op = .and)
          (a b : ℕ) (ha : a < 9) (hb : b < 9) (ne : a ≠ b)
          (ma : a ∈ z.inputs) (mb : b ∈ z.inputs) : False := by
        obtain ⟨o,ls⟩ := z
        change o = .and at hop
        subst o
        change a ∈ ls at ma
        change b ∈ ls at mb
        have len : ls.length ≤ 2 := (hm _ hz).2
        cases ls with
        | nil => contradiction
        | cons u ls =>
          cases ls with
          | nil => simp only [List.mem_singleton] at ma mb; exact ne (ma.trans mb.symm)
          | cons v ls =>
            cases ls with
            | cons z ls => simp at len
            | nil =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ma mb
              rcases ma with au | av <;> rcases mb with bu | bv
              · exact ne (au.trans bu.symm)
              · subst u; subst v
                exact rawD ⟨a,ha⟩ ⟨b,hb⟩ (fun h => ne (congrArg Fin.val h)) hz
              · subst u; subst v
                exact rawD ⟨b,hb⟩ ⟨a,ha⟩ (fun h => ne (congrArg Fin.val h.symm)) hz
              · exact ne (av.trans bv.symm)
      obtain ⟨E,monoE,sz,inputsE,outE,ops,noAnd,sameWires,sameEval⟩ := clampTail D hm hs exclude
      have sizeE : E.size ≤ 14 := by omega
      have rawE (a b : Fin 9) (ne : a ≠ b) (mem : (⟨.and,[a.val,b.val]⟩ : Gate) ∈ E.gates) : False :=
        noAnd _ mem rfl a.val b.val a.isLt b.isLt (fun h => ne (Fin.ext h)) (by simp) (by simp)
      have sameOp (j : ℕ) (hj : j < D.size) (h : (D.gates.get ⟨j,hj⟩).op = .and) :
          (E.gates.get ⟨j,by change j < E.size; omega⟩).op = .and := by
        have hE : j < E.gates.length := by change j < E.size; omega
        have hD : j < D.gates.length := hj
        have eq := ops j
        simp only [List.getElem?_eq_getElem hE, List.getElem?_eq_getElem hD, Option.map_some,
          Option.some.injEq] at eq
        exact eq.trans h

      have values (m : ℕ) : E.eval (seed m) = f (bits m) := by
        rw [sameEval _ (by simp [seed])]
        have eq := congrFun computes (bits m)
        change ((⟨g :: gs,out⟩ : Circuit).wires _).getD out false = _ at eq
        rw [wires] at eq
        exact eq
      have cleanTail := finite E monoE sizeE outE inputsE rawE
        (fun m hm => (values m).trans (hit m hm)) (fun m hm => (values m).trans (miss m hm))
      intro k hk op a b nonedge
      cases k with
      | zero => exact (notAnd op).elim
      | succ j =>
        have hj : j < D.size := by exact Nat.lt_of_succ_lt_succ hk
        have opD : (D.gates.get ⟨j,hj⟩).op = GateOp.and := by
          have eq : gateAt (⟨g :: gs,out⟩ : Circuit) (j+1) = (g::gs)[j+1] :=
            List.getD_eq_getElem _ _ hk
          rw [eq] at op
          exact op
        obtain ⟨m,mem,ha,hb⟩ := extendPair a b nonedge
        have enlarged (h : gateVal 9 (⟨g::gs,out⟩ : Circuit) (j+1) (pairInput a b) = true) :
            (E.wires (seed m)).getD (10+j) false = true := by
          have le (i : Fin 9) (h : pairInput a b i = true) : bits m i = true := by
            change decide (i = a ∨ i = b) = true at h
            rcases of_decide_eq_true h with rfl | rfl <;> assumption
          have value := wireMonotone _ mono _ _ le (9+(j+1)) h
          rw [wires] at value
          rw [sameWires _ (by simp [seed])]
          change (D.wires (List.ofFn (bits m) ++ [m.testBit 0 || m.testBit 2])).getD (10+j) false = true
          rw [show 10+j = 9+(j+1) by omega]
          exact value
        by_contra! high
        have falseVal := cleanTail ⟨j,by omega⟩ (sameOp j hj opD) m mem
        have isHigh : gateVal 9 (⟨g::gs,out⟩ : Circuit) (j+1) (pairInput a b) = true :=
          Bool.eq_true_of_not_eq_false high
        rw [enlarged isHigh] at falseVal
        contradiction
  have func : circuitFun 9 C = graphFun G ∅ := computes.trans graphEq
  obtain ⟨T,covers,bound⟩ := cleanBound 9 G squareFree C mono func prepared
  have count := cover T covers
  omega
