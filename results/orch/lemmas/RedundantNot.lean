import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


namespace PEqualNP.Outside.L_meta_2592_aux.RedundantNotCut

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

end PEqualNP.Outside.L_meta_2592_aux.RedundantNotCut

namespace PEqualNP.Outside.L_meta_2592_aux.RedundantNot

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)



lemma simplifyGate_mono (op : GateOp) (basis : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  rcases basis with rfl | rfl
  · intro g hg
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplifyGate, simpAnd] at hg
    subst hg
    simp
  · intro g hg
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplifyGate, simpOr] at hg
    subst hg
    simp

lemma elimPass_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ha : ∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (elimPass m gs acc).2,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    · exact fun q hq => hs q (List.mem_cons_of_mem g hq)
    · intro q hq
      rcases List.mem_append.mp hq with old | new
      · exact ha q old
      · exact simplifyGate_mono g.op (hs g List.mem_cons_self).1 _ _ q (by simpa using new)

lemma elimPass_length (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    have tail := ih (elimStep m acc g)
    have one := toList_opt_len_le
      (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
    simp only [elimStep, List.length_append] at tail
    simp only [List.length_cons]
    omega

def cutInit (n : ℕ) (P : Circuit) (c : Bool) : List (Bool ⊕ ℕ) × List Gate :=
  (((List.range (n + P.size)).map (Sum.inr : ℕ → Bool ⊕ ℕ)) ++ [Sum.inl c], P.gates)

lemma cut_inv (n : ℕ) (P : Circuit) (c : Bool) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (P.wires (List.ofFn x) ++ [c]) (cutInit n P c) := by
  let m := n + P.size
  let w := P.wires (List.ofFn x)
  have len : w.length = m := by
    change (wiresFrom P.gates (List.ofFn x)).length = _
    simp [wiresFrom_length, m, Circuit.size]
  have l2 : ((List.range m).map (Sum.inr : ℕ → Bool ⊕ ℕ)).length = m := by simp
  refine ⟨by simp, ?_, ?_⟩
  · change (((List.range m).map (Sum.inr : ℕ → Bool ⊕ ℕ)) ++ [Sum.inl c]).length = (w ++ [c]).length
    simp only [List.length_append, List.length_singleton, l2, len]
  intro i
  change statValid m ((((List.range m).map (Sum.inr : ℕ → Bool ⊕ ℕ)) ++ [Sum.inl c]).getD i (.inl false)) ∧
    statVal w ((((List.range m).map (Sum.inr : ℕ → Bool ⊕ ℕ)) ++ [Sum.inl c]).getD i (.inl false)) =
      (w ++ [c]).getD i false
  rcases Nat.lt_trichotomy i m with h | h | h
  · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
    simp [List.getD_eq_getElem?_getD, h, statValid, statVal]
  · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ (by omega)]
    exact ⟨trivial, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma constant_cut_mono (n : ℕ) (P Q : Circuit) (c : Bool)
    (hp : Monotone2 P) (hq : Monotone2 Q)
    (nonconstant : ∃ x y : Fin n → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [c]) ≠ Q.eval (P.wires (List.ofFn y) ++ [c])) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ P.size + Q.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = Q.eval (P.wires (List.ofFn x) ++ [c]) := by
  let acc := elimPass n Q.gates (cutInit n P c)
  have ok (g : Gate) (hg : g ∈ Q.gates) : OkGate g := by
    obtain ⟨ho, hl⟩ := hq g hg
    refine ⟨?_, hl⟩
    rcases ho with hand | hor
    · exact Or.inl hand
    · exact Or.inr (Or.inl hor)
  have mono : ∀ g ∈ acc.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    elimPass_mono n Q.gates (cutInit n P c) hq hp
  have size : acc.2.length ≤ P.size + Q.size :=
    elimPass_length n Q.gates (cutInit n P c)
  have result (x : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD Q.output (.inl false)) =
        Q.eval (P.wires (List.ofFn x) ++ [c]) :=
    ((elimInv_pass n (List.ofFn x) Q.gates _ (cutInit n P c) ok (cut_inv n P c x)).2.2 Q.output).2
  cases out : acc.1.getD Q.output (.inl false) with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := nonconstant
    have hx := result x
    have hy := result y
    rw [out] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨acc.2, j⟩, mono, size, ?_⟩
    intro x
    have hx := result x
    rwa [out] at hx

lemma one_not_alternative (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (one : PEqualNP.NotBracket.notCount C = 1) (f : (Fin n → Bool) → Bool)
    (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (nonconstant : ∃ x y, f x ≠ f y) :
    (∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) ∨
    ∃ P Q : Circuit, Monotone2 P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      (∀ x : Fin n → Bool, Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) = f x) ∧
      ∀ b : Bool, ∃ x : Fin n → Bool, Q.eval (P.wires (List.ofFn x) ++ [b]) ≠ f x := by
  classical
  obtain ⟨P, Q, hp, hq, size, position, factor, replacements⟩ :=
    PEqualNP.Outside.L_meta_2592_aux.RedundantNotCut.cut n C fan one
  by_cases changes : ∀ b : Bool, ∃ x : Fin n → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [b]) ≠ f x
  · exact Or.inr ⟨P, Q, hp, hq, size, fun x => (factor x).symm.trans (correct x), changes⟩
  · push Not at changes
    obtain ⟨b, hb⟩ := changes
    have nc : ∃ x y : Fin n → Bool,
        Q.eval (P.wires (List.ofFn x) ++ [b]) ≠ Q.eval (P.wires (List.ofFn y) ++ [b]) := by
      obtain ⟨x, y, hxy⟩ := nonconstant
      exact ⟨x, y, by simpa only [hb] using hxy⟩
    obtain ⟨D, hd, small, computes⟩ := constant_cut_mono n P Q b hp hq nc
    exact Or.inl ⟨D, hd, by omega, fun x => (computes x).trans (hb x)⟩

end PEqualNP.Outside.L_meta_2592_aux.RedundantNot
