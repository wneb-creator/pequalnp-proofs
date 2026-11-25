import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket


-- Section 1: U2 Circuit Model and Translation from FanInTwo

abbrev WireRef := Sum Bool (ℕ × Bool)

abbrev U2Gate := ℕ × ℕ × Bool × Bool

abbrev U2Gate.a (g : U2Gate) : ℕ := g.1
abbrev U2Gate.b (g : U2Gate) : ℕ := g.2.1
abbrev U2Gate.pa (g : U2Gate) : Bool := g.2.2.1
abbrev U2Gate.pb (g : U2Gate) : Bool := g.2.2.2

abbrev U2Circuit := List U2Gate × WireRef

abbrev U2Circuit.gates (D : U2Circuit) : List U2Gate := D.1
abbrev U2Circuit.out (D : U2Circuit) : WireRef := D.2

def u2Step (w : List Bool) (g : U2Gate) : List Bool :=
  w ++ [((w.getD g.a false) != g.pa) && ((w.getD g.b false) != g.pb)]

def u2Wires (gs : List U2Gate) (x : List Bool) : List Bool :=
  gs.foldl u2Step x

def u2Val (gs : List U2Gate) (x : Fin 10 → Bool) (w : ℕ) : Bool :=
  (u2Wires gs (List.ofFn x)).getD w false

def refEval (w : List Bool) : WireRef → Bool
  | Sum.inl c => c
  | Sum.inr (i, fl) => (w.getD i false) != fl

def refWf (bound : ℕ) : WireRef → Prop
  | Sum.inl _ => True
  | Sum.inr (i, _) => i < bound

def flipRef (fl : Bool) : WireRef → WireRef
  | Sum.inl c => Sum.inl (c != fl)
  | Sum.inr (i, f) => Sum.inr (i, f != fl)

def u2Eval (D : U2Circuit) (x : Fin 10 → Bool) : Bool :=
  refEval (u2Wires D.gates (List.ofFn x)) D.out

def U2GatesWf (gs : List U2Gate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].a < 10 + j ∧ gs[j].b < 10 + j

def U2Wf (D : U2Circuit) : Prop :=
  U2GatesWf D.gates ∧ refWf (10 + D.gates.length) D.out

lemma refEval_flipRef (w : List Bool) (fl : Bool) (r : WireRef) :
    refEval w (flipRef fl r) = (refEval w r != fl) := by
  rcases r with c | ⟨i, f⟩ <;> cases fl <;> simp [refEval, flipRef]

lemma refWf_flipRef (bound : ℕ) (fl : Bool) (r : WireRef) :
    refWf bound (flipRef fl r) ↔ refWf bound r := by
  rcases r with c | ⟨i, f⟩ <;> simp [refWf, flipRef]

lemma refWf_mono {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) {r : WireRef} (hr : refWf b₁ r) :
    refWf b₂ r := by
  rcases r with c | ⟨i, f⟩
  · trivial
  · exact Nat.lt_of_lt_of_le hr h

lemma u2Wires_nil (x : List Bool) : u2Wires [] x = x := rfl

lemma u2Wires_cons (g : U2Gate) (gs : List U2Gate) (x : List Bool) :
    u2Wires (g :: gs) x = u2Wires gs (u2Step x g) := rfl

lemma u2Wires_append (gs₁ gs₂ : List U2Gate) (x : List Bool) :
    u2Wires (gs₁ ++ gs₂) x = u2Wires gs₂ (u2Wires gs₁ x) := by
  simp [u2Wires, List.foldl_append]

lemma u2Wires_snoc (gs : List U2Gate) (g : U2Gate) (x : List Bool) :
    u2Wires (gs ++ [g]) x = u2Step (u2Wires gs x) g := by
  rw [u2Wires_append]; rfl

lemma u2Wires_length (gs : List U2Gate) (x : List Bool) :
    (u2Wires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [u2Wires]
  | cons g gs ih =>
    rw [u2Wires_cons, ih]
    simp [u2Step]
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (v d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_eq' {α : Type*} (l : List α) (v d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [v]).getD i d = v := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

lemma u2Wires_getD_lt (gs : List U2Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (u2Wires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [u2Wires_cons, ih (u2Step x g) (by simp only [u2Step, List.length_append, List.length_singleton]; omega)]
    exact getD_snoc_lt x _ false i hi

lemma u2Val_input (gs : List U2Gate) (x : Fin 10 → Bool) (i : ℕ) (hi : i < 10) :
    u2Val gs x i = x ⟨i, hi⟩ := by
  unfold u2Val
  rw [u2Wires_getD_lt gs (List.ofFn x) i (by rw [List.length_ofFn]; exact hi)]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

lemma u2Val_take (gs : List U2Gate) (x : Fin 10 → Bool) (j u : ℕ) (hj : j ≤ gs.length)
    (hu : u < 10 + j) :
    (u2Wires (gs.take j) (List.ofFn x)).getD u false = u2Val gs x u := by
  unfold u2Val
  have hs : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hs, u2Wires_append]
  exact (u2Wires_getD_lt _ _ u (by rw [u2Wires_length, List.length_ofFn, List.length_take]; omega)).symm

lemma u2Val_gate (gs : List U2Gate) (x : Fin 10 → Bool) (j : ℕ) (hj : j < gs.length)
    (ha : gs[j].a < 10 + j) (hb : gs[j].b < 10 + j) :
    u2Val gs x (10 + j) = ((u2Val gs x gs[j].a != gs[j].pa) && (u2Val gs x gs[j].b != gs[j].pb)) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hlen : (u2Wires (gs.take j) (List.ofFn x)).length = 10 + j := by
    rw [u2Wires_length, List.length_ofFn, List.length_take]
    omega
  rw [← u2Val_take gs x j gs[j].a (by omega) ha, ← u2Val_take gs x j gs[j].b (by omega) hb]
  unfold u2Val
  conv_lhs => rw [hsplit, u2Wires_append, u2Wires_cons]
  rw [u2Wires_getD_lt _ _ (10 + j) (by simp only [u2Step, List.length_append, List.length_singleton]; omega)]
  unfold u2Step
  exact getD_snoc_eq' _ _ false (10 + j) hlen.symm

lemma refEval_snoc_of_wf (w : List Bool) (v : Bool) (r : WireRef)
    (hr : refWf w.length r) :
    refEval (w ++ [v]) r = refEval w r := by
  rcases r with c | ⟨i, f⟩
  · rfl
  · simp only [refEval]
    rw [getD_snoc_lt w v false i hr]

lemma refEval_append_of_wf (gs₁ gs₂ : List U2Gate) (x : List Bool) (r : WireRef)
    (hr : refWf (x.length + gs₁.length) r) :
    refEval (u2Wires (gs₁ ++ gs₂) x) r = refEval (u2Wires gs₁ x) r := by
  rcases r with c | ⟨i, f⟩
  · rfl
  · simp only [refEval]
    rw [u2Wires_append, u2Wires_getD_lt gs₂ _ i (by rw [u2Wires_length]; exact hr)]

def evalAndRef (ea eb : WireRef) (gs : List U2Gate) : WireRef × List U2Gate :=
  match ea, eb with
  | Sum.inl false, _ => (Sum.inl false, gs)
  | _, Sum.inl false => (Sum.inl false, gs)
  | Sum.inl true, eb => (eb, gs)
  | ea, Sum.inl true => (ea, gs)
  | Sum.inr (wa, fa), Sum.inr (wb, fb) =>
    (Sum.inr (10 + gs.length, false), gs ++ [⟨wa, wb, fa, fb⟩])

lemma evalAndRef_spec (ea eb : WireRef) (gs : List U2Gate)
    (hwa : refWf (10 + gs.length) ea) (hwb : refWf (10 + gs.length) eb) (hwf : U2GatesWf gs) :
    let res := evalAndRef ea eb gs
    U2GatesWf res.2 ∧
    refWf (10 + res.2.length) res.1 ∧
    gs.length ≤ res.2.length ∧
    res.2.length ≤ gs.length + 1 ∧
    (∀ x : List Bool, x.length = 10 →
      (∀ i < 10 + gs.length, (u2Wires res.2 x).getD i false = (u2Wires gs x).getD i false) ∧
      refEval (u2Wires res.2 x) res.1 = (refEval (u2Wires gs x) ea && refEval (u2Wires gs x) eb)) := by
  rcases ea with ca | ⟨wa, fa⟩ <;> rcases eb with cb | ⟨wb, fb⟩
  · cases ca <;> cases cb <;> simp [evalAndRef, hwf, refWf, refEval]
  · cases ca
    · simp [evalAndRef, hwf, refWf, refEval]
    · simp [evalAndRef, hwf, hwb, refEval]
  · cases cb
    · simp [evalAndRef, hwf, refWf, refEval]
    · simp [evalAndRef, hwf, hwa, refEval]
  · simp only [evalAndRef]
    refine ⟨?_, ?_, by simp, by simp, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt]
        exact hwf j hlt
      · have heq : j = gs.length := by omega
        subst heq
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
        exact ⟨hwa, hwb⟩
    · simp [refWf]
    · intro x hx
      have hlen : (u2Wires gs x).length = 10 + gs.length := by rw [u2Wires_length, hx]
      constructor
      · intro i hi
        rw [u2Wires_snoc, u2Step, getD_snoc_lt _ _ _ i (by omega)]
      · rw [u2Wires_snoc, u2Step]
        simp only [refEval, Bool.bne_false]
        exact getD_snoc_eq' _ _ false (10 + gs.length) hlen.symm

lemma evalAndRef_noGate (ea eb : WireRef) (gs : List U2Gate)
    (h : (∃ ca, ea = Sum.inl ca) ∨ (∃ cb, eb = Sum.inl cb)) :
    (evalAndRef ea eb gs).2 = gs := by
  rcases h with ⟨ca, rfl⟩ | ⟨cb, rfl⟩
  · cases ca <;> rcases eb with cb | ⟨wb, fb⟩ <;> (try cases cb) <;> rfl
  · cases cb <;> rcases ea with ca | ⟨wa, fa⟩ <;> (try cases ca) <;> rfl

lemma evalAndRef_const_left (eb : WireRef) (gs : List U2Gate) :
    (evalAndRef (Sum.inl false) eb gs).1 = Sum.inl false := by
  rfl

lemma evalAndRef_const_right (ea : WireRef) (gs : List U2Gate) :
    (evalAndRef ea (Sum.inl false) gs).1 = Sum.inl false := by
  rcases ea with ca | ⟨wa, fa⟩
  · cases ca <;> rfl
  · rfl

lemma evalAndRef_const_both (ca cb : Bool) (gs : List U2Gate) :
    ∃ c, (evalAndRef (Sum.inl ca) (Sum.inl cb) gs).1 = Sum.inl c := by
  cases ca <;> cases cb <;> exact ⟨_, rfl⟩

-- Translation from Circuit to U2Circuit

def circuitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl circuitStep x := rfl

def toU2Step (env : List WireRef) (gs : List U2Gate) (g : Gate) :
    List WireRef × List U2Gate :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (env ++ [Sum.inl true], gs)
    | u :: _ => (env ++ [flipRef true (env.getD u (Sum.inl false))], gs)
  | GateOp.and =>
    match g.inputs with
    | [] => (env ++ [Sum.inl true], gs)
    | [u] => (env ++ [env.getD u (Sum.inl false)], gs)
    | [u, v] =>
      let res := evalAndRef (env.getD u (Sum.inl false)) (env.getD v (Sum.inl false)) gs
      (env ++ [res.1], res.2)
    | _ => (env ++ [Sum.inl false], gs)
  | GateOp.or =>
    match g.inputs with
    | [] => (env ++ [Sum.inl false], gs)
    | [u] => (env ++ [env.getD u (Sum.inl false)], gs)
    | [u, v] =>
      let res := evalAndRef (flipRef true (env.getD u (Sum.inl false)))
        (flipRef true (env.getD v (Sum.inl false))) gs
      (env ++ [flipRef true res.1], res.2)
    | _ => (env ++ [Sum.inl false], gs)
  | _ => (env ++ [Sum.inl false], gs)

def initEnv : List WireRef :=
  (List.range 10).map fun i => Sum.inr (i, false)

def toU2Fold (cgs : List Gate) (env : List WireRef) (gs : List U2Gate) :
    List WireRef × List U2Gate :=
  cgs.foldl (fun st g => toU2Step st.1 st.2 g) (env, gs)

def toU2 (C : Circuit) : U2Circuit :=
  let res := toU2Fold C.gates initEnv []
  ⟨res.2, res.1.getD C.output (Sum.inl false)⟩


end PEqualNP.Outside.L_meta_2592.Signed

namespace PEqualNP.Outside.L_meta_2592_aux.NotBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket
open PEqualNP.Outside.L_meta_2592.Signed

def RefGood (phase : List Bool) (marks : Finset ℕ) : WireRef → Prop
  | Sum.inl _ => True
  | Sum.inr (i, p) => i < phase.length ∧ (i ∉ marks → p = phase.getD i false)

def GatesGood (phase : List Bool) (marks : Finset ℕ) (gs : List U2Gate) : Prop :=
  phase.length = 10 + gs.length ∧
  (∀ i < 10, phase.getD i false = false) ∧ U2GatesWf gs ∧
  ∀ j (hj : j < gs.length),
    (gs[j].a ∉ marks → gs[j].pa = (phase.getD gs[j].a false != phase.getD (10 + j) false)) ∧
    (gs[j].b ∉ marks → gs[j].pb = (phase.getD gs[j].b false != phase.getD (10 + j) false))

def StateGood (phase : List Bool) (marks : Finset ℕ)
    (env : List WireRef) (gs : List U2Gate) : Prop :=
  GatesGood phase marks gs ∧ ∀ r ∈ env, RefGood phase marks r

lemma refGood_mono {phase : List Bool} {marks more : Finset ℕ} {r : WireRef}
    (hm : marks ⊆ more) (hr : RefGood phase marks r) : RefGood phase more r := by
  rcases r with c | ⟨i,p⟩
  · trivial
  · exact ⟨hr.1, fun hi => hr.2 (fun h => hi (hm h))⟩

lemma gatesGood_mono {phase : List Bool} {marks more : Finset ℕ} {gs : List U2Gate}
    (hm : marks ⊆ more) (h : GatesGood phase marks gs) : GatesGood phase more gs := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro j hj
  exact ⟨fun hi => (h.2.2.2 j hj).1 (fun h => hi (hm h)),
    fun hi => (h.2.2.2 j hj).2 (fun h => hi (hm h))⟩

lemma refGood_snoc {phase : List Bool} {marks : Finset ℕ} {r : WireRef}
    (p : Bool) (hr : RefGood phase marks r) : RefGood (phase ++ [p]) marks r := by
  rcases r with c | ⟨i,q⟩
  · trivial
  · refine ⟨by simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hr.1, ?_⟩
    intro hi
    rw [getD_snoc_lt phase p false i hr.1]
    exact hr.2 hi

lemma env_getD_good {phase : List Bool} {marks : Finset ℕ} {env : List WireRef}
    (h : ∀ r ∈ env, RefGood phase marks r) (i : ℕ) :
    RefGood phase marks (env.getD i (Sum.inl false)) := by
  by_cases hi : i < env.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    trivial

lemma refGood_flip_mark {phase : List Bool} {marks : Finset ℕ} {i : ℕ} {p : Bool}
    (hr : RefGood phase marks (Sum.inr (i,p))) :
    RefGood phase (insert i marks) (flipRef true (Sum.inr (i,p))) := by
  exact ⟨hr.1, by simp⟩

lemma append_gate {phase : List Bool} {marks : Finset ℕ} {gs : List U2Gate}
    {wa wb : ℕ} {fa fb : Bool} (p : Bool)
    (hg : GatesGood phase marks gs)
    (ha : RefGood phase marks (Sum.inr (wa,fa)))
    (hb : RefGood phase marks (Sum.inr (wb,fb))) :
    GatesGood (phase ++ [p]) marks (gs ++ [(wa,wb,fa != p,fb != p)]) ∧
    RefGood (phase ++ [p]) marks (Sum.inr (10 + gs.length,p)) := by
  have hwa : wa < 10 + gs.length := by simpa only [hg.1] using ha.1
  have hwb : wb < 10 + gs.length := by simpa only [hg.1] using hb.1
  constructor
  · refine ⟨by simp only [List.length_append, List.length_singleton, hg.1]; omega, ?_, ?_, ?_⟩
    · intro i hi
      rw [getD_snoc_lt phase p false i (by rw [hg.1]; omega)]
      exact hg.2.1 i hi
    · intro j hj
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt]
        exact hg.2.2.1 j hlt
      · have heq : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
        subst j
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
        exact ⟨hwa,hwb⟩
    · intro j hj
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt]
        have hjp : 10+j < phase.length := by rw [hg.1]; omega
        have hja : gs[j].a < phase.length := by have := (hg.2.2.1 j hlt).1; rw [hg.1]; omega
        have hjb : gs[j].b < phase.length := by have := (hg.2.2.1 j hlt).2; rw [hg.1]; omega
        rw [getD_snoc_lt phase p false (10+j) hjp,
          getD_snoc_lt phase p false gs[j].a hja, getD_snoc_lt phase p false gs[j].b hjb]
        exact hg.2.2.2 j hlt
      · have heq : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
        subst j
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton,
          U2Gate.a, U2Gate.b, U2Gate.pa, U2Gate.pb]
        rw [getD_snoc_lt phase p false wa ha.1, getD_snoc_lt phase p false wb hb.1,
          getD_snoc_eq' phase p false (10+gs.length) hg.1.symm]
        exact ⟨fun hi => congrArg (fun b : Bool => b != p) (ha.2 hi),
          fun hi => congrArg (fun b : Bool => b != p) (hb.2 hi)⟩
  · refine ⟨by simp only [List.length_append, List.length_singleton, hg.1]; omega, ?_⟩
    intro _
    exact (getD_snoc_eq' phase p false (10+gs.length) hg.1.symm).symm

end PEqualNP.Outside.L_meta_2592_aux.NotBudget
