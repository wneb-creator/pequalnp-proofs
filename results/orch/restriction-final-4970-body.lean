
namespace PEqualNP.Outside.L_meta_4970_aux.Restriction

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970_aux.Structural

def aliasVal (w : List Bool) : Option ℕ → Bool
  | none => false
  | some j => w.getD j false

def aliasValid (m : ℕ) (s : Option ℕ) : Prop := ∀ j ∈ s, j < m

def reduceAnd (m : ℕ) : Option ℕ → Option ℕ → Option Gate × Option ℕ
  | some a, some b => (some ⟨GateOp.and, [a,b]⟩, some m)
  | _, _ => (none, none)

def reduceOr (m : ℕ) : Option ℕ → Option ℕ → Option Gate × Option ℕ
  | none, b => (none, b)
  | some a, none => (none, some a)
  | some a, some b => (some ⟨GateOp.or, [a,b]⟩, some m)

def reduce (op : GateOp) (m : ℕ) (a b : Option ℕ) : Option Gate × Option ℕ :=
  match op with
  | .and => reduceAnd m a b
  | .or => reduceOr m a b
  | _ => (none, none)

def gateOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

lemma aliasValid_mono {m k : ℕ} (h : m ≤ k) (s : Option ℕ)
    (hs : aliasValid m s) : aliasValid k s := by
  intro j hj
  exact Nat.lt_of_lt_of_le (hs j hj) h

lemma aliasVal_append (w t : List Bool) (s : Option ℕ)
    (hs : aliasValid w.length s) : aliasVal (w ++ t) s = aliasVal w s := by
  cases s with
  | none => rfl
  | some j =>
    exact List.getD_append _ _ _ _ (hs j rfl)

lemma reduce_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (a b : Option ℕ)
    (ha : aliasValid w.length a) (hb : aliasValid w.length b) :
    aliasValid (w.length + (reduce op w.length a b).1.toList.length)
      (reduce op w.length a b).2 ∧
    aliasVal (wiresFrom (reduce op w.length a b).1.toList w)
      (reduce op w.length a b).2 = op.eval [aliasVal w a, aliasVal w b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduce, reduceAnd, reduceOr, aliasValid, aliasVal, wiresFrom, GateOp.eval]

def step (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  let r := reduce g.op (n + acc.2.length)
    (acc.1.getD (g.inputs.getD 0 0) none) (acc.1.getD (g.inputs.getD 1 0) none)
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def run (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    List (Option ℕ) × List Gate := gs.foldl (step n) acc

lemma run_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    run n (g :: gs) acc = run n gs (step n acc g) := rfl

lemma snoc_getD_ne {α : Type*} (l : List α) (a d : α) (i : ℕ) (h : i ≠ l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma snoc_getD_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by simp

lemma run_getD (n k : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    k < acc.1.length → (run n gs acc).1.getD k none = acc.1.getD k none := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [run_cons, ih (step n acc g) (by simp [step]; omega)]
    exact snoc_getD_ne _ _ _ _ (by omega)

lemma run_length (n : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (run n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [run_cons, ih]
    simp [step]
    omega

lemma option_length_le (o : Option Gate) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma run_size (n : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (run n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [run]
  | cons g gs ih =>
    intro acc
    have h := ih (step n acc g)
    have hs := option_length_le (reduce g.op (n + acc.2.length)
      (acc.1.getD (g.inputs.getD 0 0) none) (acc.1.getD (g.inputs.getD 1 0) none)).1
    have hh : (step n acc g).2.length ≤ acc.2.length + 1 := by
      simp [step]
    rw [run_cons, List.length_cons]
    omega

lemma inputs_two (g : Gate) (hg : gateOK g) : ∃ a b, g.inputs = [a,b] := by
  rcases g with ⟨op,l⟩
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp_all [gateOK]

def Inv (n : ℕ) (y w : List Bool) (acc : List (Option ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    aliasValid (n + acc.2.length) (acc.1.getD i none) ∧
    aliasVal (wiresFrom acc.2 y) (acc.1.getD i none) = w.getD i false

lemma inv_run (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Option ℕ) × List Gate),
    (∀ g ∈ gs, gateOK g) → Inv n y w acc →
    Inv n y (wiresFrom gs w) (run n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (step n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    have hg := hok g List.mem_cons_self
    obtain ⟨a,b,hab⟩ := inputs_two g hg
    let w' := wiresFrom acc.2 y
    have lw' : w'.length = n + acc.2.length := by simp [w', length_wiresFrom, hy]
    let r := reduce g.op (n + acc.2.length) (acc.1.getD a none) (acc.1.getD b none)
    have hs := reduce_sound g.op hg.1 w' (acc.1.getD a none) (acc.1.getD b none)
      (by rw [lw']; exact (hi a).1) (by rw [lw']; exact (hi b).1)
    rw [lw'] at hs
    change aliasValid (n + acc.2.length + r.1.toList.length) r.2 ∧
      aliasVal (wiresFrom r.1.toList w') r.2 =
      g.op.eval [aliasVal w' (acc.1.getD a none), aliasVal w' (acc.1.getD b none)] at hs
    have hstep : step n acc g = (acc.1 ++ [r.2], acc.2 ++ r.1.toList) := by
      simp [step, hab, r]
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      exact wiresFrom_append _ _ _
    obtain ⟨t,ht,htl⟩ := wiresFrom_ext r.1.toList w'
    rw [hstep]
    refine ⟨by simp [hl], ?_⟩
    intro i
    rw [List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst i
      rw [snoc_getD_eq, hl, Structural.getD_snoc_eq]
      constructor
      · exact hs.1
      · rw [hnew, hs.2]
        simp only [hab, List.map_cons, List.map_nil]
        change g.op.eval [aliasVal (wiresFrom acc.2 y) (acc.1.getD a none),
          aliasVal (wiresFrom acc.2 y) (acc.1.getD b none)] =
          g.op.eval [w.getD a false, w.getD b false]
        rw [(hi a).2, (hi b).2]
    · rw [snoc_getD_ne _ _ _ _ hil,
        snoc_getD_ne _ _ _ _ (by omega)]
      refine ⟨aliasValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [hnew, ht, aliasVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

lemma reduce_none (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (a b : Option ℕ) (h : a = none ∨ b = none) :
    (reduce op m a b).1 = none := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduce, reduceAnd, reduceOr]

lemma step_none (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (k : ℕ) (hk : k ∈ g.inputs) (hc : acc.1.getD k none = none) :
    (step n acc g).2.length = acc.2.length := by
  obtain ⟨a,b,hab⟩ := inputs_two g hg
  have h : acc.1.getD a none = none ∨ acc.1.getD b none = none := by
    simp only [hab, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with h | h
    · exact Or.inl (by simpa only [h] using hc)
    · exact Or.inr (by simpa only [h] using hc)
  have hn := reduce_none g.op hg.1 (n + acc.2.length)
    (acc.1.getD a none) (acc.1.getD b none) h
  simpa [step, hab] using congrArg (fun o : Option Gate => acc.2.length + o.toList.length) hn

lemma run_count (n k : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, gateOK g) → k < acc.1.length → acc.1.getD k none = none →
    (run n gs acc).2.length + gs.countP (fun g => g.inputs.contains k)
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [run]
  | cons g gs ih =>
    intro acc hok hk hc
    have h1 := ih (step n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [step]; omega)
      (by
        change (acc.1 ++ [_]).getD k none = none
        rw [snoc_getD_ne _ _ _ _ (by omega)]
        exact hc)
    rw [run_cons, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · have h2 := step_none n acc g (hok g List.mem_cons_self) k hkg hc
      have hct : g.inputs.contains k = true := by simpa using hkg
      simp only [hct, ↓reduceIte]
      omega
    · have h2 : (step n acc g).2.length ≤ acc.2.length + 1 := by
        have := option_length_le (reduce g.op (n + acc.2.length)
          (acc.1.getD (g.inputs.getD 0 0) none) (acc.1.getD (g.inputs.getD 1 0) none)).1
        simp [step]
      have hct : g.inputs.contains k = false := by simpa using hkg
      simp only [hct, Bool.false_eq_true, ↓reduceIte]
      omega

def initial (n x : ℕ) : List (Option ℕ) :=
  List.ofFn (fun i : Fin n => if i.val = x then none else some i.val)

lemma inv_initial (n : ℕ) (x : Fin n) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y x false)) (initial n x.val, []) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · by_cases hix : i = x.val
    · have he : (⟨i,hi⟩ : Fin n) = x := Fin.ext hix
      simp [initial, hix, aliasValid, aliasVal]
    · have he : (⟨i,hi⟩ : Fin n) ≠ x := fun h => hix (congrArg Fin.val h)
      simp [initial, hix, aliasValid, aliasVal, wiresFrom, hi, Function.update_of_ne he]
  · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    simp [aliasValid, aliasVal]


lemma circuit_gateOK (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ g ∈ C.gates, gateOK g := by
  intro g hg
  exact ⟨hC.1 g hg, hC.2.2 g hg⟩

def data (n : ℕ) (C : Circuit) (x : ℕ) : List (Option ℕ) × List Gate :=
  run n C.gates (initial n x, [])

def circuit (n : ℕ) (C : Circuit) (x : ℕ) : Circuit :=
  let acc := data n C x
  ⟨acc.2, (acc.1.getD C.output none).getD (n + acc.2.length)⟩

lemma data_inv (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (C.wires (List.ofFn (Function.update y x false))) (data n C x.val) := by
  exact inv_run n (List.ofFn y) (by simp) C.gates _ _ (circuit_gateOK n C hC)
    (inv_initial n x y)

lemma data_alias (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (y : Fin n → Bool) (w : ℕ) :
    aliasVal ((circuit n C x.val).wires (List.ofFn y))
      ((data n C x.val).1.getD w none) = wireValue n C w (Function.update y x false) := by
  exact ((data_inv n C hC x y).2 w).2

lemma circuit_eval (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (y : Fin n → Bool) :
    (circuit n C x.val).eval (List.ofFn y) = C.eval (List.ofFn (Function.update y x false)) := by
  have hv := data_alias n C hC x y C.output
  change aliasVal ((circuit n C x.val).wires (List.ofFn y))
    ((data n C x.val).1.getD C.output none) =
    C.eval (List.ofFn (Function.update y x false)) at hv
  cases hs : (data n C x.val).1.getD C.output none with
  | none =>
    rw [hs] at hv
    change false = _ at hv
    rw [← hv]
    change (wiresFrom (data n C x.val).2 (List.ofFn y)).getD
      (((data n C x.val).1.getD C.output none).getD (n + (data n C x.val).2.length)) false = false
    rw [hs]
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp)
  | some j =>
    rw [hs] at hv
    simpa only [circuit, Circuit.eval, hs, Option.getD_some, aliasVal] using hv

lemma circuit_size_saved (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) :
    (circuit n C x.val).size + C.gates.countP (fun g => g.inputs.contains x.val) ≤ C.size := by
  have h := run_count n x.val C.gates (initial n x.val, []) (circuit_gateOK n C hC)
    (by simp [initial]) (by simp [initial, x.isLt])
  simpa [circuit, data, Circuit.size] using h


def listOK (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), gateOK gs[j] ∧ ∀ k ∈ gs[j].inputs, k < n + j

lemma listOK_append (n : ℕ) (gs : List Gate) (g : Gate) (hs : listOK n gs)
    (hg : gateOK g ∧ ∀ k ∈ g.inputs, k < n + gs.length) : listOK n (gs ++ [g]) := by
  intro j hj
  by_cases h : j < gs.length
  · simpa only [List.getElem_append_left h] using hs j h
  · have he : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    simpa using hg

lemma reduce_emitted (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (a b : Option ℕ) (ha : aliasValid m a) (hb : aliasValid m b)
    (g : Gate) (hg : (reduce op m a b).1 = some g) :
    gateOK g ∧ ∀ k ∈ g.inputs, k < m := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduce, reduceAnd, reduceOr, gateOK, aliasValid]
  all_goals rcases hg with rfl; simp_all

def Safe (n : ℕ) (acc : List (Option ℕ) × List Gate) : Prop :=
  listOK n acc.2 ∧ ∀ i, aliasValid (n + acc.2.length) (acc.1.getD i none)

lemma step_safe (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (h : Safe n acc) : Safe n (step n acc g) := by
  obtain ⟨a,b,hab⟩ := inputs_two g hg
  let r := reduce g.op (n + acc.2.length) (acc.1.getD a none) (acc.1.getD b none)
  have hstep : step n acc g = (acc.1 ++ [r.2], acc.2 ++ r.1.toList) := by simp [step,hab,r]
  have hv : aliasValid (n + acc.2.length + r.1.toList.length) r.2 := by
    have hh := (reduce_sound g.op hg.1 (List.replicate (n + acc.2.length) false)
      (acc.1.getD a none) (acc.1.getD b none) (by simpa using h.2 a) (by simpa using h.2 b)).1
    simpa [r] using hh
  rw [hstep]
  constructor
  · cases hr : r.1 with
    | none => simpa only [hr, Option.toList_none, List.append_nil] using h.1
    | some q =>
      have hq := reduce_emitted g.op hg.1 (n + acc.2.length)
        (acc.1.getD a none) (acc.1.getD b none) (h.2 a) (h.2 b) q hr
      simpa only [hr, Option.toList_some] using listOK_append n acc.2 q h.1 hq
  · intro i
    change aliasValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i none)
    rw [List.length_append, ← Nat.add_assoc]
    by_cases hi : i = acc.1.length
    · subst i
      rw [snoc_getD_eq]
      exact hv
    · rw [snoc_getD_ne _ _ _ _ hi]
      exact aliasValid_mono (by omega) _ (h.2 i)

lemma run_safe (n : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, gateOK g) → Safe n acc → Safe n (run n gs acc) := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hok h
    exact ih (step n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (step_safe n acc g (hok g List.mem_cons_self) h)

lemma circuit_isAO2 (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) : PEqualNP.TopForm.IsAO2 n (circuit n C x.val) := by
  have hi : Safe n (initial n x.val, []) := by
    constructor
    · intro j hj; simp at hj
    · intro i
      exact ((inv_initial n x (fun _ => false)).2 i).1
  have hs := (run_safe n C.gates (initial n x.val, []) (circuit_gateOK n C hC) hi).1
  change listOK n (data n C x.val).2 at hs
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    exact (hs j hj).1.1
  · intro j hj i hi
    have hv := (hs j hj).2
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, circuit] at hi
    have hh : j < (data n C x.val).2.length := hj
    rw [List.getD_eq_getElem _ _ hh] at hi
    exact hv i hi
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    exact (hs j hj).1.2


lemma run_append (n : ℕ) (pre post : List Gate) (acc : List (Option ℕ) × List Gate) :
    run n (pre ++ post) acc = run n post (run n pre acc) := by
  simp [run, List.foldl_append]

lemma step_and_none (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (hand : g.op = GateOp.and) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k none = none) :
    (step n acc g).1.getD acc.1.length none = none := by
  obtain ⟨a,b,hab⟩ := inputs_two g hg
  have h : acc.1.getD a none = none ∨ acc.1.getD b none = none := by
    simp only [hab, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with h | h
    · exact Or.inl (by simpa only [h] using hc)
    · exact Or.inr (by simpa only [h] using hc)
  change (acc.1 ++ [_]).getD acc.1.length none = none
  rw [snoc_getD_eq]
  simp only [hab, List.getD_cons_zero, List.getD_cons_succ, hand, reduce]
  cases ha : acc.1.getD a none <;> cases hb : acc.1.getD b none <;> simp_all [reduceAnd]

lemma step_zero (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (k : ℕ) (hk : k ∈ g.inputs) (hc : acc.1.getD k none = none)
    (hzero : g.op = GateOp.and ∨ g.inputs = [k,k]) :
    (step n acc g).1.getD acc.1.length none = none := by
  rcases hzero with hand | hdup
  · exact step_and_none n acc g hg hand k hk hc
  · change (acc.1 ++ [_]).getD acc.1.length none = none
    rw [snoc_getD_eq]
    rcases hg.1 with hand | hor
    · simp only [hdup,List.getD_cons_zero,List.getD_cons_succ,hand,reduce,hc,reduceAnd]
    · simp only [hdup,List.getD_cons_zero,List.getD_cons_succ,hor,reduce,hc,reduceOr]

lemma run_two_zero (n : ℕ) (x : Fin n) (pre post : List Gate) (g : Gate)
    (hok : ∀ h ∈ pre ++ g :: post, gateOK h)
    (hzero : g.op = GateOp.and ∨ g.inputs = [x.val,x.val]) (hx : x.val ∈ g.inputs)
    (hreader : ∃ h ∈ post, n + pre.length ∈ h.inputs) :
    (run n (pre ++ g :: post) (initial n x.val, [])).2.length + 2 ≤
      (pre ++ g :: post).length := by
  let a := run n pre (initial n x.val, [])
  let b := step n a g
  have haLen : a.1.length = n + pre.length := by simp [a, run_length, initial]
  have haSize : a.2.length ≤ pre.length := by
    simpa [a] using run_size n pre (initial n x.val, [])
  have haZero : a.1.getD x.val none = none := by
    rw [show a = run n pre (initial n x.val, []) from rfl,
      run_getD n x.val pre _ (by simp [initial])]
    simp [initial, x.isLt]
  have hg : gateOK g := hok g (by simp)
  have hbSize : b.2.length = a.2.length := step_none n a g hg x.val hx haZero
  have hbZero : b.1.getD (n + pre.length) none = none := by
    rw [← haLen]
    exact step_zero n a g hg x.val hx haZero hzero
  have hbLen : n + pre.length < b.1.length := by simp [b,step,haLen]
  have hp := run_count n (n + pre.length) post b
    (fun h hh => hok h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))) hbLen hbZero
  have hr : 1 ≤ post.countP (fun h => h.inputs.contains (n + pre.length)) := by
    obtain ⟨h,hh,hr⟩ := hreader
    exact List.countP_pos_iff.mpr ⟨h,hh,by simpa using hr⟩
  rw [run_append,run_cons]
  change (run n post b).2.length + 2 ≤ _
  simp only [List.length_append,List.length_cons]
  omega

lemma circuit_size_two_and (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (pre post : List Gate) (g : Gate) (hgs : C.gates = pre ++ g :: post)
    (hand : g.op = GateOp.and) (hx : x.val ∈ g.inputs)
    (hreader : ∃ h ∈ post, n + pre.length ∈ h.inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have hh := run_two_zero n x pre post g
    (by rw [← hgs]; exact circuit_gateOK n C hC) (Or.inl hand) hx hreader
  simpa [circuit,data,Circuit.size,hgs] using hh


lemma circuit_size_two_zero (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (pre post : List Gate) (g : Gate) (hgs : C.gates = pre ++ g :: post)
    (hzero : g.op = GateOp.and ∨ g.inputs = [x.val,x.val]) (hx : x.val ∈ g.inputs)
    (hreader : ∃ h ∈ post, n + pre.length ∈ h.inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have hh := run_two_zero n x pre post g
    (by rw [← hgs]; exact circuit_gateOK n C hC) hzero hx hreader
  simpa [circuit,data,Circuit.size,hgs] using hh

lemma circuit_wire_alias (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (w : ℕ)
    (hnz : ∃ y : Fin n → Bool, wireValue n C w (Function.update y x false) = true) :
    ∃ j < n + (circuit n C x.val).size, ∀ y : Fin n → Bool,
      wireValue n (circuit n C x.val) j y = wireValue n C w (Function.update y x false) := by
  obtain ⟨z,hz⟩ := hnz
  cases hs : (data n C x.val).1.getD w none with
  | none =>
    have hv := data_alias n C hC x z w
    rw [hs] at hv
    change false = _ at hv
    rw [hz] at hv
    cases hv
  | some j =>
    refine ⟨j,?_,?_⟩
    · have hv := ((data_inv n C hC x z).2 w).1
      exact hv j hs
    · intro y
      have hv := data_alias n C hC x y w
      rw [hs] at hv
      exact hv


lemma countP_two {α : Type*} (l : List α) (p : α → Bool)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.length_cons] at hi hj
    cases i with
    | zero =>
      cases j with
      | zero => exact (hne rfl).elim
      | succ j =>
        change p a = true at hpi
        change p l[j] = true at hpj
        have hh : 0 < l.countP p := List.countP_pos_iff.mpr ⟨l[j],List.getElem_mem _,hpj⟩
        simp only [List.countP_cons,hpi,↓reduceIte]
        omega
    | succ i =>
      cases j with
      | zero =>
        change p a = true at hpj
        change p l[i] = true at hpi
        have hh : 0 < l.countP p := List.countP_pos_iff.mpr ⟨l[i],List.getElem_mem _,hpi⟩
        simp only [List.countP_cons,hpj,↓reduceIte]
        omega
      | succ j =>
        have hh := ih i j (by omega) (by omega) (by omega) hpi hpj
        simp only [List.countP_cons]
        split_ifs <;> omega

lemma circuit_size_two_readers (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (i j : ℕ) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hne : i ≠ j)
    (hri : x.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs)
    (hrj : x.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have hpi : (C.gates[i]).inputs.contains x.val = true := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hi] at hri
    simpa using hri
  have hpj : (C.gates[j]).inputs.contains x.val = true := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hj] at hrj
    simpa using hrj
  have hh := countP_two C.gates (fun g => g.inputs.contains x.val) i j hi hj hne hpi hpj
  have hs := circuit_size_saved n C hC x
  omega

lemma circuit_size_two_zero_at (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (j : ℕ) (hj : j < C.gates.length)
    (hzero : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [x.val,x.val])
    (hx : x.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs)
    (hreader : ∃ k < C.gates.length, j < k ∧
      n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have he : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    exact List.getD_eq_getElem _ _ hj
  rw [he] at hzero hx
  have hgs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hh := (List.take_append_drop j C.gates).symm
    rw [List.drop_eq_getElem_cons hj] at hh
    exact hh
  apply circuit_size_two_zero n C hC x (C.gates.take j) (C.gates.drop (j+1)) C.gates[j]
    hgs hzero hx
  obtain ⟨k,hk,hjk,hr⟩ := hreader
  have hkt : k-(j+1) < (C.gates.drop (j+1)).length := by simp; omega
  refine ⟨(C.gates.drop (j+1))[k-(j+1)],List.getElem_mem hkt,?_⟩
  rw [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hk] at hr
  have helem : (C.gates.drop (j+1))[k-(j+1)] = C.gates[k] := by
    rw [List.getElem_drop]
    congr 1
    omega
  rw [helem,List.length_take,min_eq_left (Nat.le_of_lt hj)]
  exact hr

end PEqualNP.Outside.L_meta_4970_aux.Restriction
