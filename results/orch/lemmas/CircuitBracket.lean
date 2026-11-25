import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import PEqualNP.Defs
import Mathlib.Data.List.Forall2

namespace PEqualNP.Outside.L_meta_2592_aux.PetersenBracket

lemma low_replacement_of_generators {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (E : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (generators : ∀ x, f x = true → ∃ e ∈ E, e ≤ x ∧ f e = true)
    (allH : ∀ e ∈ E, h e = true) :
    ∀ x, G x false = f x := by
  intro x
  have below : G x false ≤ f x := by
    rw [← correct x]
    apply monoZ x
    cases h x <;> decide
  cases hx : f x with
  | false =>
    rw [hx] at below
    cases hg : G x false with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using below))
  | true =>
    obtain ⟨e, he, hex, hfe⟩ := generators x hx
    have hge : G e false = true := by simpa [allH e he, hfe] using correct e
    have le : G e false ≤ G x false := monoX false hex
    rw [hge] at le
    cases hg : G x false with
    | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using le))
    | true => rfl

lemma high_replacement_of_cogenerators {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (M : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (cogenerators : ∀ x, f x = false → ∃ m ∈ M, x ≤ m ∧ f m = false)
    (allH : ∀ m ∈ M, h m = false) :
    ∀ x, G x true = f x := by
  intro x
  have above : f x ≤ G x true := by
    rw [← correct x]
    apply monoZ x
    cases h x <;> decide
  cases hx : f x with
  | false =>
    obtain ⟨m, hm, hxm, hfm⟩ := cogenerators x hx
    have hgm : G m true = false := by simpa [allH m hm, hfm] using correct m
    have le : G x true ≤ G m true := monoX true hxm
    rw [hgm] at le
    cases hg : G x true with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using le))
  | true =>
    rw [hx] at above
    cases hg : G x true with
    | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using above))
    | true => rfl

lemma critical_generator {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (E : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (generators : ∀ x, f x = true → ∃ e ∈ E, e ≤ x ∧ f e = true)
    (changed : ∃ x, G x false ≠ f x) :
    ∃ e ∈ E, h e = false := by
  classical
  by_contra! no
  have allH : ∀ e ∈ E, h e = true := by
    intro e he
    have ne := no e he
    cases hh : h e <;> simp_all
  obtain ⟨x, hx⟩ := changed
  exact hx (low_replacement_of_generators f h G E monoX monoZ correct generators allH x)

lemma critical_cogenerator {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (M : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (cogenerators : ∀ x, f x = false → ∃ m ∈ M, x ≤ m ∧ f m = false)
    (changed : ∃ x, G x true ≠ f x) :
    ∃ m ∈ M, h m = true := by
  classical
  by_contra! no
  have allH : ∀ m ∈ M, h m = false := by
    intro m hm
    have ne := no m hm
    cases hh : h m <;> simp_all
  obtain ⟨x, hx⟩ := changed
  exact hx (high_replacement_of_cogenerators f h G M monoX monoZ correct cogenerators allH x)


def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def row (m : ℕ) : Fin 10 → Bool := fun i => m.testBit i.val

def edgeMasks : Finset ℕ :=
  {3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288}

def independentMasks : Finset ℕ :=
  {50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma edge_cover : ∀ x : Fin 10 → Bool, petersen x = true →
    ∃ e ∈ edgeMasks, row e ≤ x ∧ petersen (row e) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma independent_cover : ∀ x : Fin 10 → Bool, petersen x = false →
    ∃ m ∈ independentMasks, x ≤ row m ∧ petersen (row m) = false := by
  decide

lemma edge_truth : ∀ e ∈ edgeMasks, petersen (row e) = true := by
  decide

lemma independent_false : ∀ m ∈ independentMasks, petersen (row m) = false := by
  decide

lemma critical_petersen_witnesses
    (h : (Fin 10 → Bool) → Bool) (G : (Fin 10 → Bool) → Bool → Bool)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = petersen x)
    (changedLow : ∃ x, G x false ≠ petersen x)
    (changedHigh : ∃ x, G x true ≠ petersen x) :
    ∃ e ∈ edgeMasks, ∃ m ∈ independentMasks, h (row e) = false ∧ h (row m) = true := by
  classical
  have generators : ∀ x, petersen x = true →
      ∃ e ∈ edgeMasks.image row, e ≤ x ∧ petersen e = true := by
    intro x hx
    obtain ⟨e, he, hle, htrue⟩ := edge_cover x hx
    exact ⟨row e, Finset.mem_image.mpr ⟨e, he, rfl⟩, hle, htrue⟩
  have cogenerators : ∀ x, petersen x = false →
      ∃ m ∈ independentMasks.image row, x ≤ m ∧ petersen m = false := by
    intro x hx
    obtain ⟨m, hm, hle, hfalse⟩ := independent_cover x hx
    exact ⟨row m, Finset.mem_image.mpr ⟨m, hm, rfl⟩, hle, hfalse⟩
  obtain ⟨e, he, hhe⟩ := critical_generator petersen h G (edgeMasks.image row)
    monoX monoZ correct generators changedLow
  obtain ⟨m, hm, hhm⟩ := critical_cogenerator petersen h G (independentMasks.image row)
    monoX monoZ correct cogenerators changedHigh
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨a, ha, b, hb, hhe, hhm⟩

end PEqualNP.Outside.L_meta_2592_aux.PetersenBracket

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

lemma split_last (l : List Gate) (h : ∃ g ∈ l, g.op = GateOp.not) :
    ∃ pre g suf, l = pre ++ g :: suf ∧ g.op = GateOp.not ∧
      ∀ q ∈ suf, q.op ≠ GateOp.not := by
  classical
  induction l with
  | nil => obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons a l ih =>
    by_cases h' : ∃ g ∈ l, g.op = GateOp.not
    · obtain ⟨pre, g, suf, h1, h2, h3⟩ := ih h'
      exact ⟨a :: pre, g, suf, by rw [h1]; rfl, h2, h3⟩
    · push_neg at h'
      obtain ⟨g, hg, hn⟩ := h
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨[], g, l, rfl, hn, h'⟩
      · exact absurd hn (h' g hg)

lemma split_one (C : Circuit) (hn : PEqualNP.NotBracket.notCount C = 1) :
    ∃ pre g suf, C.gates = pre ++ g :: suf ∧ g.op = GateOp.not ∧
      (∀ q ∈ pre, q.op ≠ GateOp.not) ∧ (∀ q ∈ suf, q.op ≠ GateOp.not) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  change (C.gates.filter fun g => decide (g.op = GateOp.not)).length = 1 at hn
  have hhas : ∃ g ∈ C.gates, g.op = GateOp.not := by
    cases he : C.gates.filter (fun g => decide (g.op = GateOp.not)) with
    | nil => simp [he] at hn
    | cons g gs =>
      have hmem : g ∈ C.gates.filter (fun q => decide (q.op = GateOp.not)) := by
        rw [he]
        exact List.mem_cons_self
      obtain ⟨hg, hop⟩ := List.mem_filter.mp hmem
      exact ⟨g, hg, of_decide_eq_true hop⟩
  obtain ⟨pre, g, suf, he, hg, hs⟩ := split_last C.gates hhas
  refine ⟨pre, g, suf, he, hg, ?_, hs⟩
  have hlen : (pre.filter fun q => decide (q.op = GateOp.not)).length = 0 := by
    rw [he] at hn
    simp only [List.filter_append, List.filter_cons, hg, decide_true, if_true,
      List.length_append, List.length_cons] at hn
    omega
  have hempty := List.length_eq_zero_iff.mp hlen
  intro q hq hnot
  have hmem : q ∈ pre.filter (fun a => decide (a.op = GateOp.not)) := by
    simp [hq, hnot]
  rw [hempty] at hmem
  cases hmem

lemma replace_middle (pre suf : List Gate) (g : Gate) (b : Bool) :
    PEqualNP.NotPremium.replaceByConst (pre ++ g :: suf) pre.length b =
      pre ++ PEqualNP.NotPremium.constGate b :: suf := by
  change (pre ++ g :: suf).set pre.length (PEqualNP.NotPremium.constGate b) = _
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    change a :: (pre ++ g :: suf).set pre.length (PEqualNP.NotPremium.constGate b) =
      a :: (pre ++ PEqualNP.NotPremium.constGate b :: suf)
    rw [ih]

lemma cut (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hn : PEqualNP.NotBracket.notCount C = 1) :
    ∃ P Q : Circuit, Monotone2 P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      (∃ g : Gate, C.gates[P.size]? = some g ∧ g.op = GateOp.not) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)])) ∧
      (∀ (b : Bool) (x : Fin n → Bool),
        (Circuit.mk (PEqualNP.NotPremium.replaceByConst C.gates P.size b)
          C.output).eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [b])) := by
  obtain ⟨pre, g, suf, he, hg, hp, hs⟩ := split_one C hn
  refine ⟨⟨pre, g.inputs.headD (n + pre.length)⟩, ⟨suf, C.output⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have ha' : a ∈ pre := ha
    obtain ⟨ho, hl⟩ := hf a (by rw [he]; simp [ha'])
    refine ⟨?_, hl⟩
    have := hp a ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    tauto
  · intro a ha
    have ha' : a ∈ suf := ha
    obtain ⟨ho, hl⟩ := hf a (by rw [he]; simp [ha'])
    refine ⟨?_, hl⟩
    have := hs a ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    tauto
  · simp [Circuit.size, he]; omega
  · exact ⟨g, by simp [Circuit.size, he], hg⟩
  · intro x
    simp only [Circuit.eval, wires_eq, he, List.foldl_append, List.foldl_cons]
    congr 2
    have hl : (List.foldl step (List.ofFn x) pre).length = n + pre.length := by
      rw [fold_len]
      simp
    generalize List.foldl step (List.ofFn x) pre = W at hl
    simp only [step, hg]
    congr 2
    rcases g.inputs with _ | ⟨a, t⟩
    · simp [GateOp.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none, hl]
    · simp [GateOp.eval]
  · intro b x
    simp only [Circuit.size, he, replace_middle, Circuit.eval, wires_eq,
      List.foldl_append, List.foldl_cons]
    cases b <;> rfl

end PEqualNP.Outside.L_meta_2592_aux.OneNotCut

namespace PEqualNP.Outside.L_meta_2592_aux.CircuitBracket

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma getD_le {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) (i : ℕ) :
    a.getD i false ≤ b.getD i false := by
  induction h generalizing i with
  | nil => exact le_rfl
  | cons hhead htail ih =>
    cases i with
    | zero => exact hhead
    | succ i => exact ih i

lemma all_map_le (is : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (is.map f).all id ≤ (is.map g).all id := by
  apply Bool.le_iff_imp.mpr
  intro hf
  change (is.map f).all id = true at hf
  rw [List.all_eq_true] at hf ⊢
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact Bool.le_iff_imp.mp (h i) (hf (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩))

lemma any_map_le (is : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (is.map f).any id ≤ (is.map g).any id := by
  apply Bool.le_iff_imp.mpr
  intro hf
  change (is.map f).any id = true at hf
  rw [List.any_eq_true] at hf ⊢
  obtain ⟨b, hb, htrue⟩ := hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact ⟨g i, List.mem_map.mpr ⟨i, hi, rfl⟩, Bool.le_iff_imp.mp (h i) htrue⟩

lemma gate_eval_le (g : Gate) (basis : g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) :
    g.op.eval (g.inputs.map fun i => a.getD i false) ≤
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
  rcases basis with hand | hor
  · rw [hand]
    exact all_map_le _ _ _ (getD_le h)
  · rw [hor]
    exact any_map_le _ _ _ (getD_le h)

lemma wires_le (C : Circuit) (mono : Monotone2 C) {a b : List Bool}
    (h : List.Forall₂ (· ≤ ·) a b) : List.Forall₂ (· ≤ ·) (C.wires a) (C.wires b) := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · exact List.rel_append h (List.Forall₂.cons
        (gate_eval_le g (mono g List.mem_cons_self).1 h) List.Forall₂.nil)
    · intro q hq
      exact mono q (List.mem_cons_of_mem g hq)

lemma eval_le (C : Circuit) (mono : Monotone2 C) {a b : List Bool}
    (h : List.Forall₂ (· ≤ ·) a b) : C.eval a ≤ C.eval b :=
  getD_le (wires_le C mono h) C.output

lemma ofFn_le {n : ℕ} {x y : Fin n → Bool} (h : x ≤ y) :
    List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
  apply List.forall₂_iff_get.mpr
  constructor
  · simp
  · intro i hi hj
    simpa using h ⟨i, by simpa using hi⟩

lemma rel_self (a : List Bool) : List.Forall₂ (· ≤ ·) a a := by
  induction a with
  | nil => exact List.Forall₂.nil
  | cons a as ih => exact List.Forall₂.cons le_rfl ih

lemma bracket_monoX (n : ℕ) (P Q : Circuit) (hp : Monotone2 P) (hq : Monotone2 Q)
    (z : Bool) : Monotone (fun x : Fin n → Bool => Q.eval (P.wires (List.ofFn x) ++ [z])) := by
  intro x y hxy
  exact eval_le Q hq (List.rel_append (wires_le P hp (ofFn_le hxy))
    (List.Forall₂.cons le_rfl List.Forall₂.nil))

lemma bracket_monoZ (n : ℕ) (P Q : Circuit) (hq : Monotone2 Q) (x : Fin n → Bool) :
    Monotone (fun z => Q.eval (P.wires (List.ofFn x) ++ [z])) := by
  intro a b hab
  exact eval_le Q hq (List.rel_append (rel_self _) (List.Forall₂.cons hab List.Forall₂.nil))

lemma set_at_append {α : Type*} (pre : List α) (g : α) (post : List α) (b : α) :
    (pre ++ g :: post).set pre.length b = pre ++ b :: post := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    change a :: (pre ++ g :: post).set pre.length b = a :: (pre ++ b :: post)
    rw [ih]

lemma replacement_eval (P Q : Circuit) (g : Gate) (b : Bool) (x : List Bool) :
    Circuit.eval ⟨PEqualNP.NotPremium.replaceByConst (P.gates ++ g :: Q.gates) P.size b,
      Q.output⟩ x = Q.eval (P.wires x ++ [b]) := by
  unfold PEqualNP.NotPremium.replaceByConst Circuit.size
  rw [set_at_append]
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  cases b <;> rfl


lemma critical_for_decomposition (C P Q : Circuit)
    (hp : Monotone2 P) (hq : Monotone2 Q)
    (factor : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
      Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]))
    (replacements : ∀ (b : Bool) (x : Fin 10 → Bool),
      (Circuit.mk (PEqualNP.NotPremium.replaceByConst C.gates P.size b)
        C.output).eval (List.ofFn x) = Q.eval (P.wires (List.ofFn x) ++ [b]))
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = PetersenBracket.petersen x)
    (changed : ∀ b : Bool, ∃ x : Fin 10 → Bool,
      (Circuit.mk (PEqualNP.NotPremium.replaceByConst C.gates P.size b)
        C.output).eval (List.ofFn x) ≠ C.eval (List.ofFn x)) :
    ∃ e ∈ PetersenBracket.edgeMasks, ∃ m ∈ PetersenBracket.independentMasks,
      P.eval (List.ofFn (PetersenBracket.row e)) = false ∧
      P.eval (List.ofFn (PetersenBracket.row m)) = true := by
  apply PetersenBracket.critical_petersen_witnesses
    (fun x => P.eval (List.ofFn x)) (fun x z => Q.eval (P.wires (List.ofFn x) ++ [z]))
    (bracket_monoX 10 P Q hp hq) (bracket_monoZ 10 P Q hq)
  · intro x
    exact (factor x).symm.trans (correct x)
  · obtain ⟨x, hx⟩ := changed false
    refine ⟨x, ?_⟩
    rw [← replacements false x, ← correct x]
    exact hx
  · obtain ⟨x, hx⟩ := changed true
    refine ⟨x, ?_⟩
    rw [← replacements true x, ← correct x]
    exact hx

lemma essential_one_not_circuit (C : Circuit) (fan : FanInTwo C)
    (one : PEqualNP.NotBracket.notCount C = 1) (budget : C.size ≤ 19)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = PetersenBracket.petersen x)
    (essential : ∀ i : ℕ, (∃ g : Gate, C.gates[i]? = some g ∧ g.op = GateOp.not) →
      ∀ b : Bool, ∃ x : Fin 10 → Bool,
        (Circuit.mk (PEqualNP.NotPremium.replaceByConst C.gates i b)
          C.output).eval (List.ofFn x) ≠ C.eval (List.ofFn x)) :
    ∃ P Q : Circuit, Monotone2 P ∧ Monotone2 Q ∧ P.size + Q.size ≤ 18 ∧
      P.size + Q.size + 1 = C.size ∧
      (∀ x : Fin 10 → Bool,
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) = PetersenBracket.petersen x) ∧
      ∃ e ∈ PetersenBracket.edgeMasks, ∃ m ∈ PetersenBracket.independentMasks,
        P.eval (List.ofFn (PetersenBracket.row e)) = false ∧
        P.eval (List.ofFn (PetersenBracket.row m)) = true := by
  obtain ⟨P, Q, hp, hq, size, position, factor, replacements⟩ := OneNotCut.cut 10 C fan one
  refine ⟨P, Q, hp, hq, by omega, size, ?_, ?_⟩
  · intro x
    exact (factor x).symm.trans (correct x)
  · exact critical_for_decomposition C P Q hp hq factor replacements correct
      (essential P.size position)

end PEqualNP.Outside.L_meta_2592_aux.CircuitBracket
