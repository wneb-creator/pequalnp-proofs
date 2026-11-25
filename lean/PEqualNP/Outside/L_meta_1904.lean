import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
lemma pair_safe_implies_safe (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hmono : Monotone2 C)
    (hsmall : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 2 →
        (C.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n + j) false = true →
          ∃ a ∈ S, ∃ b ∈ S, G.Adj a b) :
    ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
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
  have hchecks : tiny G C := by
    intro j g entry hg S hS active
    obtain ⟨a, ha, b, hb, adj⟩ := hsmall j g entry hg S hS active
    exact ⟨a, b, adj, decide_eq_true ha, decide_eq_true hb⟩
  exact safety hchecks hmono

lemma exists_minimum (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hC : Monotone2 C) (hCf : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ D : Circuit, Monotone2 D ∧ (∀ x, D.eval (List.ofFn x) = f x) ∧
      ∀ E : Circuit, Monotone2 E → (∀ x, E.eval (List.ofFn x) = f x) →
        D.size ≤ E.size := by
  classical
  have hex : ∃ s : ℕ, ∃ D : Circuit,
      Monotone2 D ∧ (∀ x, D.eval (List.ofFn x) = f x) ∧ D.size = s :=
    ⟨C.size, C, hC, hCf, rfl⟩
  obtain ⟨D, hD, hf, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hf, fun E hE hEf => ?_⟩
  rw [hs]
  exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩

lemma edgeless (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : ∀ a b, ¬ G.Adj a b) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
      (∀ E : Circuit, Monotone2 E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) =
          decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) →
        D.size ≤ E.size) ∧
      ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
  · simp [Monotone2]
  · intro x
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hedge]
  · intro E _ _
    exact Nat.zero_le _
  · intro j g h
    simp at h

def path4Adj (a b : Fin 4) : Prop := a.val + 1 = b.val ∨ b.val + 1 = a.val

def path4Fun (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def path4Block (op : Bool) (a b : Fin 6) : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩,
    ⟨if op then .and else .or, [a.val, b.val]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def path4Short : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

lemma path4_exchange_identity : ∀ a b c d : Bool,
    (((a || c) && (b || d)) && (b || c)) =
      ((b && (a || c)) || (c && d)) := by
  decide

lemma path4_block_mono (op : Bool) (a b : Fin 6) :
    PEqualNP.MetaComplexity.Monotone2 (path4Block op a b) := by
  cases op <;> simp [PEqualNP.MetaComplexity.Monotone2, path4Block]

lemma path4_short_mono : PEqualNP.MetaComplexity.Monotone2 path4Short := by
  simp [PEqualNP.MetaComplexity.Monotone2, path4Short]

lemma path4_no_triangle : ∀ a b c : Fin 4,
    path4Adj a b → path4Adj b c → ¬ path4Adj c a := by
  unfold path4Adj
  decide

lemma path4_no_four_cycle : ∀ a b c d : Fin 4,
    path4Adj a b → path4Adj b c → path4Adj c d → path4Adj d a →
      a = c ∨ b = d := by
  unfold path4Adj
  decide

lemma path4_edge_function : ∀ x : Fin 4 → Bool,
    path4Fun x = decide (∃ a b : Fin 4,
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) ∧ x a = true ∧ x b = true) := by
  decide

lemma path4_block_computes : ∀ x : Fin 4 → Bool,
    (path4Block true 4 5).eval (List.ofFn x) = path4Fun x := by
  decide

lemma path4_block_dirty :
    let x : Fin 4 → Bool := fun i => decide (i = 0 ∨ i = 3)
    ((path4Block true 4 5).wires (List.ofFn x)).getD 6 false = true ∧
      path4Fun x = false := by
  decide

set_option maxHeartbeats 2000000 in
lemma path4_one_gate_obstruction : ∀ (op : Bool) (a b : Fin 6),
    (∀ x : Fin 4 → Bool, (path4Block op a b).eval (List.ofFn x) = path4Fun x) →
    ∃ x : Fin 4 → Bool,
      ((path4Block op a b).wires (List.ofFn x)).getD 6 false = true ∧
        path4Fun x = false := by
  decide

lemma path4_shorter_safe : path4Short.size < (path4Block true 4 5).size ∧
    ∀ x : Fin 4 → Bool, path4Short.eval (List.ofFn x) = path4Fun x ∧
      (((path4Short.wires (List.ofFn x)).getD 5 false = true → path4Fun x = true) ∧
       ((path4Short.wires (List.ofFn x)).getD 6 false = true → path4Fun x = true)) := by
  decide

open PEqualNP.EdgeOwnership

lemma graph_hit_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (h : ∃ a b : Fin n, G.Adj a b ∧
      pairInput u v a = true ∧ pairInput u v b = true) : G.Adj u v := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  simp only [pairInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp at hab
  · exact hab
  · exact hab.symm
  · simp at hab

lemma singleton_pair_le {n : ℕ} (u v w : Fin n) (hw : w = u ∨ w = v) :
    pairInput w w ≤ pairInput u v := by
  intro i
  by_cases hi : i = w
  · subst i
    simp [pairInput, hw]
  · simp [pairInput, hi]

lemma monotone_singleton_pair {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hF : Monotone F) (u v w : Fin n) (hw : w = u ∨ w = v)
    (h : F (pairInput w w) = true) : F (pairInput u v) = true := by
  have hle := hF (singleton_pair_le u v w hw)
  by_contra hnot
  have hfalse : F (pairInput u v) = false := by simpa using hnot
  rw [h, hfalse] at hle
  exact (show ¬ ((true : Bool) ≤ false) by decide) hle

lemma singleton_overlap_orientation {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (A B T : (Fin n → Bool) → Bool)
    (hA : Monotone A) (hB : Monotone B) (hT : Monotone T)
    (hbelow : ∀ x : Fin n → Bool, A x = true → B x = true → T x = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)
    (a : Fin n) (haA : A (pairInput a a) = true)
    (haB : B (pairInput a a) = true) :
    (∀ b : Fin n, A (pairInput b b) = true → T (pairInput b b) = false) ∨
      (∀ c : Fin n, B (pairInput c c) = true → T (pairInput c c) = false) := by
  by_cases hleft : ∀ b : Fin n,
      A (pairInput b b) = true → T (pairInput b b) = false
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨b, hbA, hbT⟩ := hleft
    have hbT' : T (pairInput b b) = true := by simpa using hbT
    refine Or.inr ?_
    intro c hcB
    by_contra hcT
    have hcT' : T (pairInput c c) = true := by simpa using hcT
    have hab : G.Adj a b := graph_hit_pair G a b (hbelow _
      (monotone_singleton_pair A hA a b a (Or.inl rfl) haA)
      (monotone_singleton_pair B hB a b a (Or.inl rfl) haB)
      (monotone_singleton_pair T hT a b b (Or.inr rfl) hbT'))
    have hac : G.Adj a c := graph_hit_pair G a c (hbelow _
      (monotone_singleton_pair A hA a c a (Or.inl rfl) haA)
      (monotone_singleton_pair B hB a c a (Or.inl rfl) haB)
      (monotone_singleton_pair T hT a c c (Or.inr rfl) hcT'))
    have hbc : G.Adj b c := graph_hit_pair G b c (hbelow _
      (monotone_singleton_pair A hA b c b (Or.inl rfl) hbA)
      (monotone_singleton_pair B hB b c c (Or.inr rfl) hcB)
      (monotone_singleton_pair T hT b c b (Or.inl rfl) hbT'))
    exact htri a b c hab hbc hac.symm

end PEqualNP.Outside.L_meta_1904
