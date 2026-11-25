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

lemma getD_env_wf (env : List WireRef) (b : ℕ) (henv : ∀ r ∈ env, refWf b r) (u : ℕ) :
    refWf b (env.getD u (Sum.inl false)) := by
  by_cases hu : u < env.length
  · rw [List.getD_eq_getElem _ _ hu]
    exact henv _ (List.getElem_mem hu)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu)]
    trivial

lemma getD_env_eval (env : List WireRef) (cw uw : List Bool)
    (hlen : env.length = cw.length)
    (hagree : ∀ i < env.length, refEval uw (env.getD i (Sum.inl false)) = cw.getD i false)
    (u : ℕ) :
    refEval uw (env.getD u (Sum.inl false)) = cw.getD u false := by
  by_cases hu : u < env.length
  · exact hagree u hu
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu),
        List.getD_eq_default _ _ (by omega)]
    rfl

lemma toU2Fold_spec (cgs : List Gate) (env : List WireRef) (gs : List U2Gate)
    (hfan : ∀ g ∈ cgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hwf : U2GatesWf gs)
    (henv : ∀ r ∈ env, refWf (10 + gs.length) r) :
    let res := toU2Fold cgs env gs
    U2GatesWf res.2 ∧
    (∀ r ∈ res.1, refWf (10 + res.2.length) r) ∧
    res.1.length = env.length + cgs.length ∧
    res.2.length + (cgs.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)).length ≤ gs.length + cgs.length ∧
    (∀ (x : List Bool) (cw : List Bool), x.length = 10 → env.length = cw.length →
      (∀ i < env.length, refEval (u2Wires gs x) (env.getD i (Sum.inl false)) = cw.getD i false) →
      ∀ i < res.1.length,
        refEval (u2Wires res.2 x) (res.1.getD i (Sum.inl false)) = (cgs.foldl circuitStep cw).getD i false) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨hwf, henv, by simp [toU2Fold], by simp [toU2Fold], ?_⟩
    intro x cw _ _ hagree i hi
    exact hagree i hi
  | cons g cgs ih =>
    have hg := hfan g List.mem_cons_self
    have hcgs : ∀ g' ∈ cgs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    have hstep :
        let st := toU2Step env gs g
        U2GatesWf st.2 ∧
        (∀ r ∈ st.1, refWf (10 + st.2.length) r) ∧
        st.1.length = env.length + 1 ∧
        st.2.length + (if g.op = GateOp.not then 1 else 0) ≤ gs.length + 1 ∧
        (∀ (x cw : List Bool), x.length = 10 → env.length = cw.length →
          (∀ i < env.length, refEval (u2Wires gs x) (env.getD i (Sum.inl false)) = cw.getD i false) →
          ∀ i < st.1.length,
            refEval (u2Wires st.2 x) (st.1.getD i (Sum.inl false)) = (circuitStep cw g).getD i false) := by
      rcases g with ⟨op, ins⟩
      rcases hg with ⟨hop, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · -- AND
        rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · trivial
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              rfl
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · exact getD_env_wf env _ henv u
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              simpa [GateOp.eval] using getD_env_eval env cw (u2Wires gs x) hlc hagree u
        · have hsp := evalAndRef_spec (env.getD u (Sum.inl false)) (env.getD v (Sum.inl false)) gs
            (getD_env_wf env _ henv u) (getD_env_wf env _ henv v) hwf
          rcases hsp with ⟨hwf', hrf', hle1, hle2, hev⟩
          refine ⟨hwf', ?_, by simp [toU2Step], by dsimp only [toU2Step]; simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]; omega, ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            dsimp only [toU2Step]
            rcases hr with hr | rfl
            · exact refWf_mono (by omega) (henv r hr)
            · exact hrf'
          · intro x cw hx hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            obtain ⟨hpres, hval⟩ := hev x hx
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              have hrw := getD_env_wf env _ henv i
              have hsame : refEval (u2Wires (evalAndRef (env.getD u (Sum.inl false)) (env.getD v (Sum.inl false)) gs).2 x)
                  (env.getD i (Sum.inl false)) =
                  refEval (u2Wires gs x) (env.getD i (Sum.inl false)) := by
                rcases hri : env.getD i (Sum.inl false) with c | ⟨idx, fl⟩
                · rfl
                · rw [hri] at hrw
                  simp only [refEval]
                  rw [hpres idx hrw]
              rw [hsame]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq, hval]
              rw [getD_env_eval env cw (u2Wires gs x) hlc hagree u,
                  getD_env_eval env cw (u2Wires gs x) hlc hagree v]
              simp [GateOp.eval]
        · simp at hlen
      · -- OR
        rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · trivial
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              rfl
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · exact getD_env_wf env _ henv u
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              simpa [GateOp.eval] using getD_env_eval env cw (u2Wires gs x) hlc hagree u
        · have hsp := evalAndRef_spec (flipRef true (env.getD u (Sum.inl false)))
            (flipRef true (env.getD v (Sum.inl false))) gs
            ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv u))
            ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv v)) hwf
          rcases hsp with ⟨hwf', hrf', hle1, hle2, hev⟩
          refine ⟨hwf', ?_, by simp [toU2Step], by dsimp only [toU2Step]; simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]; omega, ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            dsimp only [toU2Step]
            rcases hr with hr | rfl
            · exact refWf_mono (by omega) (henv r hr)
            · exact (refWf_flipRef _ _ _).mpr hrf'
          · intro x cw hx hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            obtain ⟨hpres, hval⟩ := hev x hx
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              have hrw := getD_env_wf env _ henv i
              have hsame : refEval (u2Wires (evalAndRef (flipRef true (env.getD u (Sum.inl false)))
                    (flipRef true (env.getD v (Sum.inl false))) gs).2 x)
                  (env.getD i (Sum.inl false)) =
                  refEval (u2Wires gs x) (env.getD i (Sum.inl false)) := by
                rcases hri : env.getD i (Sum.inl false) with c | ⟨idx, fl⟩
                · rfl
                · rw [hri] at hrw
                  simp only [refEval]
                  rw [hpres idx hrw]
              rw [hsame]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq, refEval_flipRef, hval,
                  refEval_flipRef, refEval_flipRef]
              rw [getD_env_eval env cw (u2Wires gs x) hlc hagree u,
                  getD_env_eval env cw (u2Wires gs x) hlc hagree v]
              cases h1 : cw.getD u false <;> cases h2 : cw.getD v false <;>
                simp [GateOp.eval, List.getD_eq_getElem?_getD] at h1 h2 ⊢ <;> simp [h1, h2]
        · simp at hlen
      · -- NOT
        rcases ins with _ | ⟨u, rest⟩
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · trivial
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq]
              rfl
        · refine ⟨hwf, ?_, by simp [toU2Step], by simp [toU2Step], ?_⟩
          · intro r hr
            simp only [toU2Step, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact henv r hr
            · exact (refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv u)
          · intro x cw _ hlc hagree i hi
            simp only [toU2Step, List.length_append, List.length_singleton] at hi
            simp only [toU2Step, circuitStep]
            by_cases hlt : i < env.length
            · rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
              exact hagree i hlt
            · have heq : i = env.length := by omega
              subst heq
              rw [getD_snoc_eq, hlc, getD_snoc_eq, refEval_flipRef]
              rw [getD_env_eval env cw (u2Wires gs x) hlc hagree u]
              simp [GateOp.eval]
    rcases hstep with ⟨hwf1, henv1, hlen1, hsize1, hev1⟩
    have ih' := ih (toU2Step env gs g).1 (toU2Step env gs g).2 hcgs hwf1 henv1
    rcases ih' with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
    refine ⟨hwf2, henv2, ?_, ?_, ?_⟩
    · change (toU2Fold cgs (toU2Step env gs g).1 (toU2Step env gs g).2).1.length = env.length + (g :: cgs).length
      simp only [List.length_cons]; omega
    · change (toU2Fold cgs (toU2Step env gs g).1 (toU2Step env gs g).2).2.length +
        ((g :: cgs).filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)).length ≤ gs.length + (g :: cgs).length
      simp only [List.filter_cons, List.length_cons]
      by_cases hnot : g.op = GateOp.not
      · simp only [hnot, decide_true, ↓reduceIte, List.length_cons] at hsize1 ⊢; omega
      · simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte] at hsize1 ⊢; omega
    · intro x cw hx hlc hagree i hi
      simp only [toU2Fold, List.foldl_cons] at hi ⊢
      exact hev2 x (circuitStep cw g) hx (by simp [circuitStep, hlen1, hlc])
        (hev1 x cw hx hlc hagree) i hi

lemma toU2_spec (C : Circuit) (hfan : FanInTwo C) :
    U2Wf (toU2 C) ∧
    (toU2 C).gates.length ≤ C.size - PEqualNP.NotBracket.notCount C ∧
    (∀ x : Fin 10 → Bool, u2Eval (toU2 C) x = C.eval (List.ofFn x)) := by
  have hinit_wf : ∀ r ∈ initEnv, refWf (10 + ([] : List U2Gate).length) r := by
    intro r hr
    simp only [initEnv, List.mem_map, List.mem_range] at hr
    rcases hr with ⟨i, hi, rfl⟩
    exact hi
  have hsp := toU2Fold_spec C.gates initEnv [] hfan (fun j hj => by simp at hj) hinit_wf
  rcases hsp with ⟨hwf, henv, hlen, hsize, hev⟩
  refine ⟨⟨hwf, getD_env_wf _ _ henv C.output⟩, ?_, ?_⟩
  · change (toU2Fold C.gates initEnv []).2.length ≤ C.gates.length -
      (C.gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)).length
    simp only [List.length_nil, Nat.zero_add] at hsize
    omega
  · intro x
    have hagree0 : ∀ i < initEnv.length,
        refEval (u2Wires [] (List.ofFn x)) (initEnv.getD i (Sum.inl false)) =
          (List.ofFn x).getD i false := by
      intro i hi
      simp only [initEnv, List.length_map, List.length_range] at hi
      have hget : initEnv.getD i (Sum.inl false) = Sum.inr (i, false) := by
        simp [initEnv, List.getD_eq_getElem?_getD, hi]
      rw [hget]
      simp [refEval, u2Wires]
    have hcw : (toU2Fold C.gates initEnv []).1.length = (C.wires (List.ofFn x)).length := by
      have hcwl : ∀ (gs : List Gate) (w : List Bool), (gs.foldl circuitStep w).length = w.length + gs.length := by
        intro gs; induction gs with
        | nil => intro w; simp
        | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [circuitStep]; omega
      rw [wires_eq_foldl, hcwl, hlen]
      simp [initEnv]
    unfold u2Eval toU2 Circuit.eval
    rw [wires_eq_foldl]
    exact getD_env_eval _ _ _ hcw (hev (List.ofFn x) (List.ofFn x) (by simp) (by simp [initEnv]) hagree0) C.output

-- Section 2: Minimal U2 Circuits, Deletion, and Constant-Propagation Restriction

def HasU2Size (f : (Fin 10 → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ D : U2Circuit, U2Wf D ∧ D.gates.length ≤ s ∧ ∀ x, u2Eval D x = f x

def IsMinU2 (f : (Fin 10 → Bool) → Bool) (D : U2Circuit) : Prop :=
  U2Wf D ∧ (∀ x, u2Eval D x = f x) ∧
  ∀ D' : U2Circuit, U2Wf D' → (∀ x, u2Eval D' x = f x) → D.gates.length ≤ D'.gates.length

lemma exists_minU2 {f : (Fin 10 → Bool) → Bool} {s : ℕ} (h : HasU2Size f s) :
    ∃ D : U2Circuit, IsMinU2 f D ∧ D.gates.length ≤ s := by
  classical
  have hex : ∃ m, HasU2Size f m := ⟨s, h⟩
  let m := Nat.find hex
  have hm : HasU2Size f m := Nat.find_spec hex
  have hle : m ≤ s := Nat.find_min' hex h
  rcases hm with ⟨D, hwf, hlen, hev⟩
  refine ⟨D, ⟨hwf, hev, ?_⟩, Nat.le_trans hlen hle⟩
  intro D' hwf' hev'
  have hmle : m ≤ D'.gates.length := Nat.find_min' hex ⟨D', hwf', Nat.le_refl _, hev'⟩
  omega

-- Generic single-pass U2 gate compilation/restriction/deletion engine.
def passStep (env : List WireRef) (gs : List U2Gate) (g : U2Gate) :
    List WireRef × List U2Gate :=
  let ea := flipRef g.pa (env.getD g.a (Sum.inl false))
  let eb := flipRef g.pb (env.getD g.b (Sum.inl false))
  let res := evalAndRef ea eb gs
  (env ++ [res.1], res.2)

def passFold (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate) :
    List WireRef × List U2Gate :=
  cgs.foldl (fun st g => passStep st.1 st.2 g) (env, gs)

lemma passFold_spec (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate)
    (hwf : U2GatesWf gs)
    (henv : ∀ r ∈ env, refWf (10 + gs.length) r) :
    let res := passFold cgs env gs
    U2GatesWf res.2 ∧
    (∀ r ∈ res.1, refWf (10 + res.2.length) r) ∧
    res.1.length = env.length + cgs.length ∧
    res.2.length ≤ gs.length + cgs.length ∧
    (∀ (x y : List Bool), x.length = 10 → env.length = y.length →
      (∀ i < env.length, refEval (u2Wires gs x) (env.getD i (Sum.inl false)) = y.getD i false) →
      ∀ i < res.1.length,
        refEval (u2Wires res.2 x) (res.1.getD i (Sum.inl false)) = (u2Wires cgs y).getD i false) := by
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨hwf, henv, by simp [passFold], by simp [passFold], ?_⟩
    intro x y _ _ hagree i hi
    exact hagree i hi
  | cons g cgs ih =>
    have hsp := evalAndRef_spec (flipRef g.pa (env.getD g.a (Sum.inl false)))
      (flipRef g.pb (env.getD g.b (Sum.inl false))) gs
      ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv g.a))
      ((refWf_flipRef _ _ _).mpr (getD_env_wf env _ henv g.b)) hwf
    rcases hsp with ⟨hwf1, hrf1, hle1, hle2, hev1⟩
    have hst1 : (passStep env gs g).1.length = env.length + 1 := by simp [passStep]
    have hst2_ge : gs.length ≤ (passStep env gs g).2.length := hle1
    have hst2_le : (passStep env gs g).2.length ≤ gs.length + 1 := hle2
    have henv1 : ∀ r ∈ (passStep env gs g).1, refWf (10 + (passStep env gs g).2.length) r := by
      intro r hr
      simp only [passStep, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact refWf_mono (by omega) (henv r hr)
      · exact hrf1
    have ih' := ih (passStep env gs g).1 (passStep env gs g).2 hwf1 henv1
    rcases ih' with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
    refine ⟨hwf2, henv2, ?_, ?_, ?_⟩
    · change (passFold cgs (passStep env gs g).1 (passStep env gs g).2).1.length = env.length + (g :: cgs).length
      simp only [List.length_cons]; omega
    · change (passFold cgs (passStep env gs g).1 (passStep env gs g).2).2.length ≤ gs.length + (g :: cgs).length
      simp only [List.length_cons]; omega
    · intro x y hx hly hagree i hi
      simp only [passFold, List.foldl_cons, u2Wires_cons] at hi ⊢
      apply hev2 x (u2Step y g) hx (by simp [passStep, u2Step, hly])
      · intro k hk
        simp only [passStep, List.length_append, List.length_singleton] at hk
        simp only [passStep, u2Step]
        obtain ⟨hpres, hval⟩ := hev1 x hx
        by_cases hlt : k < env.length
        · rw [getD_snoc_lt _ _ _ k hlt, getD_snoc_lt _ _ _ k (by omega)]
          have hrw := getD_env_wf env _ henv k
          have hsame : refEval (u2Wires (evalAndRef (flipRef g.pa (env.getD g.a (Sum.inl false)))
                (flipRef g.pb (env.getD g.b (Sum.inl false))) gs).2 x)
              (env.getD k (Sum.inl false)) =
              refEval (u2Wires gs x) (env.getD k (Sum.inl false)) := by
            rcases hrk : env.getD k (Sum.inl false) with c | ⟨idx, fl⟩
            · rfl
            · rw [hrk] at hrw
              simp only [refEval]
              rw [hpres idx hrw]
          rw [hsame]
          exact hagree k hlt
        · have heq : k = env.length := by omega
          subst heq
          rw [getD_snoc_eq, hly, getD_snoc_eq, hval, refEval_flipRef, refEval_flipRef]
          rw [getD_env_eval env y (u2Wires gs x) hly hagree g.a,
              getD_env_eval env y (u2Wires gs x) hly hagree g.b]
      · exact hi

-- Delete gate `j` by substituting `repl` (valid at `< 10 + j`) for wire `10 + j`.
def deleteGateAt (D : U2Circuit) (j : ℕ) (repl : WireRef) : U2Circuit :=
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  let env0 : List WireRef := ((List.range (10 + j)).map fun i => Sum.inr (i, false)) ++ [repl]
  let res := passFold post env0 pre
  let out' := match D.out with
    | Sum.inl c => Sum.inl c
    | Sum.inr (w, fl) => flipRef fl (res.1.getD w (Sum.inl false))
  ⟨res.2, out'⟩

lemma deleteGateAt_spec (D : U2Circuit) (hD : U2Wf D) (j : ℕ) (hj : j < D.gates.length)
    (repl : WireRef) (hrepl_wf : refWf (10 + j) repl)
    (hrepl_eq : ∀ x : Fin 10 → Bool,
      refEval (u2Wires (D.gates.take j) (List.ofFn x)) repl = u2Val D.gates x (10 + j)) :
    U2Wf (deleteGateAt D j repl) ∧
    (deleteGateAt D j repl).gates.length ≤ D.gates.length - 1 ∧
    ∀ x : Fin 10 → Bool, u2Eval (deleteGateAt D j repl) x = u2Eval D x := by
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hpost_len : post.length = D.gates.length - (j + 1) := by simp [post]
  have hpre_wf : U2GatesWf pre := by
    intro k hk
    have hk' : k < j := by omega
    have hkl : k < D.gates.length := by omega
    have := hD.1 k hkl
    simpa [pre, List.getElem_take] using this
  let env0 : List WireRef := ((List.range (10 + j)).map fun i => Sum.inr (i, false)) ++ [repl]
  have henv0_wf : ∀ r ∈ env0, refWf (10 + pre.length) r := by
    intro r hr
    simp only [env0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    rcases hr with ⟨i, hi, rfl⟩ | rfl
    · simp only [refWf]; omega
    · rw [hpre_len]; exact hrepl_wf
  have hsp := passFold_spec post env0 pre hpre_wf henv0_wf
  rcases hsp with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
  refine ⟨⟨hwf2, ?_⟩, ?_, ?_⟩
  · dsimp only [deleteGateAt]
    rcases D.out with c | ⟨w, fl⟩
    · trivial
    · exact (refWf_flipRef _ _ _).mpr (getD_env_wf _ _ henv2 w)
  · change (passFold post env0 pre).2.length ≤ D.gates.length - 1; omega
  · intro x
    have hsplit : D.gates = pre ++ D.gates[j] :: post := by
      simp only [pre, post]
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    let y0 := u2Wires (pre ++ [D.gates[j]]) (List.ofFn x)
    have hy0_len : y0.length = 10 + j + 1 := by
      simp only [y0, u2Wires_length, List.length_ofFn, List.length_append, List.length_singleton, hpre_len]
      omega
    have henv0_len : env0.length = y0.length := by
      simp [env0, hy0_len]
    have hagree0 : ∀ i < env0.length,
        refEval (u2Wires pre (List.ofFn x)) (env0.getD i (Sum.inl false)) = y0.getD i false := by
      intro i hi
      simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton] at hi
      by_cases hlt : i < 10 + j
      · have hget : env0.getD i (Sum.inl false) = Sum.inr (i, false) := by
          simp only [env0]
          rw [getD_snoc_lt _ _ _ i (by simp; exact hlt)]
          simp [List.getD_eq_getElem?_getD, hlt]
        rw [hget]
        simp only [refEval, Bool.bne_false, y0, u2Wires_snoc, u2Step]
        rw [getD_snoc_lt _ _ _ i (by rw [u2Wires_length, List.length_ofFn, hpre_len]; exact hlt)]
      · have heq : i = 10 + j := by omega
        subst heq
        have hget : env0.getD (10 + j) (Sum.inl false) = repl := by
          exact getD_snoc_eq' _ repl (Sum.inl false) (10 + j) (by simp)
        rw [hget, hrepl_eq x]
        unfold u2Val
        conv_lhs => rw [hsplit, u2Wires_append, u2Wires_cons]
        rw [u2Wires_getD_lt post _ (10 + j) (by simp only [u2Step, u2Wires_length, List.length_ofFn, hpre_len, List.length_append, List.length_singleton]; omega)]
        simp only [y0, u2Wires_snoc]
    have hfull : u2Wires post y0 = u2Wires D.gates (List.ofFn x) := by
      conv_rhs => rw [hsplit]
      rw [u2Wires_append, u2Wires_cons]
      simp only [y0, u2Wires_snoc]
    have hev_all := hev2 (List.ofFn x) y0 (by simp) henv0_len hagree0
    rw [hfull] at hev_all
    dsimp only [u2Eval, deleteGateAt]
    rcases hout : D.out with c | ⟨w, fl⟩
    · rfl
    · rw [refEval_flipRef]
      have hw : w < 10 + D.gates.length := by
        have := hD.2; rw [hout] at this; exact this
      have hw' : w < (passFold post env0 pre).1.length := by
        rw [hlen2]; simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
      rw [hev_all w hw']
      rfl

-- Delete a dead gate `j` (not read by any gate `k > j` and not `D.out`).
lemma deleteDeadGate (D : U2Circuit) (hD : U2Wf D) (j : ℕ) (hj : j < D.gates.length)
    (hout : ∀ fl, D.out ≠ Sum.inr (10 + j, fl))
    (hdead : ∀ k (hk : k < D.gates.length), j < k → D.gates[k].a ≠ 10 + j ∧ D.gates[k].b ≠ 10 + j) :
    U2Wf (deleteGateAt D j (Sum.inl false)) ∧
    (deleteGateAt D j (Sum.inl false)).gates.length ≤ D.gates.length - 1 ∧
    ∀ x : Fin 10 → Bool, u2Eval (deleteGateAt D j (Sum.inl false)) x = u2Eval D x := by
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hpost_len : post.length = D.gates.length - (j + 1) := by simp [post]
  have hpre_wf : U2GatesWf pre := by
    intro k hk
    have hk' : k < D.gates.length := by omega
    simpa [pre, List.getElem_take] using hD.1 k hk'
  let env0 : List WireRef := ((List.range (10 + j)).map fun i => Sum.inr (i, false)) ++ [Sum.inl false]
  have henv0_wf : ∀ r ∈ env0, refWf (10 + pre.length) r := by
    intro r hr
    simp only [env0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    rcases hr with ⟨i, hi, rfl⟩ | rfl
    · simp only [refWf]; omega
    · trivial
  have hsp := passFold_spec post env0 pre hpre_wf henv0_wf
  rcases hsp with ⟨hwf2, henv2, hlen2, hsize2, hev2⟩
  refine ⟨⟨hwf2, ?_⟩, ?_, ?_⟩
  · dsimp only [deleteGateAt]
    rcases D.out with c | ⟨w, fl⟩
    · trivial
    · exact (refWf_flipRef _ _ _).mpr (getD_env_wf _ _ henv2 w)
  · change (passFold post env0 pre).2.length ≤ D.gates.length - 1; omega
  · intro x
    let wpre := u2Wires pre (List.ofFn x)
    let y1 := wpre ++ [false]
    let y2 := u2Step wpre D.gates[j]
    have hwpre_len : wpre.length = 10 + j := by simp [wpre, u2Wires_length, hpre_len]
    have hsplit : D.gates = pre ++ D.gates[j] :: post := by
      simp only [pre, post]; rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hagree_post : ∀ (gs : List U2Gate) (w₁ w₂ : List Bool),
        w₁.length = w₂.length →
        (∀ g ∈ gs, g.a ≠ 10 + j ∧ g.b ≠ 10 + j) →
        (∀ i, i ≠ 10 + j → w₁.getD i false = w₂.getD i false) →
        ∀ i, i ≠ 10 + j → (u2Wires gs w₁).getD i false = (u2Wires gs w₂).getD i false := by
      intro gs
      induction gs with
      | nil => intro w₁ w₂ _ _ h i hi; exact h i hi
      | cons g gs ih =>
        intro w₁ w₂ hl hno h
        have hg := hno g List.mem_cons_self
        have hstep_eq : ((w₁.getD g.a false != g.pa) && (w₁.getD g.b false != g.pb)) =
            ((w₂.getD g.a false != g.pa) && (w₂.getD g.b false != g.pb)) := by
          rw [h g.a hg.1, h g.b hg.2]
        rw [u2Wires_cons, u2Wires_cons]
        apply ih (u2Step w₁ g) (u2Step w₂ g) (by simp [u2Step, hl])
          (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
        intro i hi
        by_cases hlt : i < w₁.length
        · simp only [u2Step]
          rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
          exact h i hi
        · by_cases heq : i = w₁.length
          · subst heq
            simp only [u2Step]
            rw [getD_snoc_eq, hl, getD_snoc_eq, hstep_eq]
          · simp only [u2Step]
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hno_post : ∀ g ∈ post, g.a ≠ 10 + j ∧ g.b ≠ 10 + j := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
      have hlt : j + 1 + t < D.gates.length := by simp [post] at ht; omega
      have := hdead (j + 1 + t) hlt (by omega)
      simpa [post, List.getElem_drop] using this
    have hy12 : ∀ i, i ≠ 10 + j → (u2Wires post y1).getD i false = (u2Wires post y2).getD i false := by
      apply hagree_post post y1 y2 (by simp [y1, y2, u2Step]) hno_post
      intro i hi
      by_cases hlt : i < wpre.length
      · simp only [y1, y2, u2Step]
        rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i hlt]
      · simp only [y1, y2, u2Step]
        have hgt : wpre.length + 1 ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hagree0 : ∀ i < env0.length,
        refEval wpre (env0.getD i (Sum.inl false)) = y1.getD i false := by
      intro i hi
      simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton] at hi
      by_cases hlt : i < 10 + j
      · have hget : env0.getD i (Sum.inl false) = Sum.inr (i, false) := by
          simp only [env0]; rw [getD_snoc_lt _ _ _ i (by simp; exact hlt)]
          simp [List.getD_eq_getElem?_getD, hlt]
        rw [hget]
        simp only [refEval, Bool.bne_false, y1]
        rw [getD_snoc_lt _ _ _ i (by omega)]
      · have heq : i = 10 + j := by omega
        subst heq
        have hget : env0.getD (10 + j) (Sum.inl false) = Sum.inl false :=
          getD_snoc_eq' _ (Sum.inl false) (Sum.inl false) (10 + j) (by simp)
        rw [hget]
        simp only [refEval, y1]
        exact (getD_snoc_eq' wpre false false (10 + j) hwpre_len.symm).symm
    have hev_all := hev2 (List.ofFn x) y1 (by simp) (by simp [env0, y1, hwpre_len]) hagree0
    have hfull2 : u2Wires post y2 = u2Wires D.gates (List.ofFn x) := by
      conv_rhs => rw [hsplit]
      rw [u2Wires_append, u2Wires_cons]
    dsimp only [u2Eval, deleteGateAt]
    rcases hout_eq : D.out with c | ⟨w, fl⟩
    · rfl
    · rw [refEval_flipRef]
      have hw : w < 10 + D.gates.length := by
        have := hD.2; rw [hout_eq] at this; exact this
      have hw' : w < (passFold post env0 pre).1.length := by
        rw [hlen2]; simp only [env0, List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
      have hwne : w ≠ 10 + j := fun heq => hout fl (by rw [hout_eq, heq])
      rw [hev_all w hw', hy12 w hwne, hfull2]
      rfl

-- Minimality Corollaries

lemma min_has_reader_or_out {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (j : ℕ) (hj : j < D.gates.length) :
    (∃ fl, D.out = Sum.inr (10 + j, fl)) ∨
    ∃ k, ∃ (hk : k < D.gates.length), j < k ∧ (D.gates[k].a = 10 + j ∨ D.gates[k].b = 10 + j) := by
  by_contra hno
  push Not at hno
  obtain ⟨hwf', hlen', hev'⟩ := deleteDeadGate D hmin.1 j hj hno.1 (fun k hk hjk => hno.2 k hk hjk)
  have hbad := hmin.2.2 _ hwf' (fun x => (hev' x).trans (hmin.2.1 x))
  omega

lemma min_no_self {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (j : ℕ) (hj : j < D.gates.length) :
    D.gates[j].a ≠ D.gates[j].b := by
  intro heq
  have ha := (hmin.1.1 j hj).1
  have hb := (hmin.1.1 j hj).2
  by_cases hpol : D.gates[j].pa = D.gates[j].pb
  · let repl : WireRef := Sum.inr (D.gates[j].a, D.gates[j].pa)
    have hsp := deleteGateAt_spec D hmin.1 j hj repl ha (fun x => by
      rw [u2Val_gate D.gates x j hj ha hb, ← heq, ← hpol, Bool.and_self]
      simp only [repl, refEval]
      rw [u2Val_take D.gates x j D.gates[j].a (by omega) ha])
    have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
    omega
  · let repl : WireRef := Sum.inl false
    have hsp := deleteGateAt_spec D hmin.1 j hj repl trivial (fun x => by
      rw [u2Val_gate D.gates x j hj ha hb, ← heq]
      cases u2Val D.gates x D.gates[j].a <;> cases hp1 : D.gates[j].pa <;> cases hp2 : D.gates[j].pb <;>
        simp_all [repl, refEval])
    have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
    omega

-- In-place replacement of gate `j` by an equivalent gate `g'`.
def replaceGateAt (D : U2Circuit) (j : ℕ) (g' : U2Gate) : U2Circuit :=
  ⟨D.gates.set j g', D.out⟩

lemma list_set_split {α : Type*} (l : List α) (j : ℕ) (v : α) (hj : j < l.length) :
    l.set j v = l.take j ++ v :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih j (by simpa using hj)

lemma replaceGateAt_spec (D : U2Circuit) (hD : U2Wf D) (j : ℕ) (hj : j < D.gates.length)
    (g' : U2Gate) (ha' : g'.a < 10 + j) (hb' : g'.b < 10 + j)
    (heq : ∀ x : Fin 10 → Bool,
      ((u2Val D.gates x g'.a != g'.pa) && (u2Val D.gates x g'.b != g'.pb)) = u2Val D.gates x (10 + j)) :
    U2Wf (replaceGateAt D j g') ∧
    (replaceGateAt D j g').gates.length = D.gates.length ∧
    ∀ x : Fin 10 → Bool, u2Eval (replaceGateAt D j g') x = u2Eval D x := by
  have hlen : (D.gates.set j g').length = D.gates.length := List.length_set
  have hwf : U2Wf (replaceGateAt D j g') := by
    refine ⟨?_, ?_⟩
    · intro k hk
      have hk' : k < D.gates.length := by rwa [replaceGateAt, hlen] at hk
      by_cases hkj : k = j
      · subst hkj
        simp [replaceGateAt, U2Circuit.gates, U2Gate.a, U2Gate.b, List.getElem_set_self, ha', hb']
      · simp only [replaceGateAt, U2Circuit.gates, U2Gate.a, U2Gate.b, List.getElem_set_ne (Ne.symm hkj)]
        exact hD.1 k hk'
    · simpa [replaceGateAt, hlen] using hD.2
  refine ⟨hwf, hlen, fun x => ?_⟩
  have hwires : u2Wires (D.gates.set j g') (List.ofFn x) = u2Wires D.gates (List.ofFn x) := by
    have hs1 : D.gates.set j g' = D.gates.take j ++ g' :: D.gates.drop (j + 1) :=
      list_set_split D.gates j g' hj
    have hs2 : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    rw [hs1, u2Wires_append, u2Wires_cons]
    conv_rhs => rw [hs2, u2Wires_append, u2Wires_cons]
    congr 1
    let w0 := u2Wires (D.gates.take j) (List.ofFn x)
    have hpre : ∀ u < 10 + j, w0.getD u false = u2Val D.gates x u :=
      fun u hu => u2Val_take D.gates x j u (by omega) hu
    have hg_eval : ((w0.getD g'.a false != g'.pa) && (w0.getD g'.b false != g'.pb)) =
        ((w0.getD D.gates[j].a false != D.gates[j].pa) && (w0.getD D.gates[j].b false != D.gates[j].pb)) := by
      rw [hpre g'.a ha', hpre g'.b hb', heq x,
          u2Val_gate D.gates x j hj (hD.1 j hj).1 (hD.1 j hj).2,
          hpre D.gates[j].a (hD.1 j hj).1, hpre D.gates[j].b (hD.1 j hj).2]
    simp only [u2Step, w0] at hg_eval ⊢
    rw [hg_eval]
  unfold u2Eval replaceGateAt
  rw [hwires]

-- Helper: gate 0 reads `(v, p0)` and `(u, q0)`, and gate `j1 > 0` reads `(v, p1)` and `(10, q1)`.
lemma min_gate0_interact {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v u : ℕ) (p0 q0 : Bool) (hv : v < 10) (hu : u < 10)
    (hg0 : ∀ x : Fin 10 → Bool, u2Val D.gates x 10 = ((u2Val D.gates x v != p0) && (u2Val D.gates x u != q0)))
    (j1 : ℕ) (hj1 : j1 < D.gates.length) (hj1_pos : 0 < j1)
    (p1 q1 : Bool)
    (hg1 : ∀ x : Fin 10 → Bool, u2Val D.gates x (10 + j1) = ((u2Val D.gates x v != p1) && (u2Val D.gates x 10 != q1))) :
    p1 = p0 ∧ q1 = true ∧
    ((∃ fl, D.out = Sum.inr (10, fl)) ∨
      ∃ k, ∃ (hk : k < D.gates.length), 0 < k ∧ k ≠ j1 ∧ (D.gates[k].a = 10 ∨ D.gates[k].b = 10)) := by
  by_cases hp : p1 = p0
  · subst hp
    cases q1 with
    | false =>
      have hrepl : ∀ x : Fin 10 → Bool,
          refEval (u2Wires (D.gates.take j1) (List.ofFn x)) (Sum.inr (10, false)) = u2Val D.gates x (10 + j1) := by
        intro x
        simp only [refEval, Bool.bne_false]
        rw [u2Val_take D.gates x j1 10 (by omega) (by omega), hg1 x, hg0 x]
        cases (u2Val D.gates x v != p1) <;> cases (u2Val D.gates x u != q0) <;> rfl
      have hsp := deleteGateAt_spec D hmin.1 j1 hj1 (Sum.inr (10, false)) (by simp [refWf]; omega) hrepl
      have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
      omega
    | true =>
      refine ⟨rfl, rfl, ?_⟩
      let g' : U2Gate := ⟨v, u, p1, !q0⟩
      have hrep := replaceGateAt_spec D hmin.1 j1 hj1 g' (by dsimp [g', U2Gate.a, U2Gate.b, U2Gate.pa, U2Gate.pb]; omega) (by dsimp [g', U2Gate.a, U2Gate.b, U2Gate.pa, U2Gate.pb]; omega) (fun x => by
        dsimp [g', U2Gate.a, U2Gate.b, U2Gate.pa, U2Gate.pb]
        rw [hg1 x, hg0 x]
        cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> cases p1 <;> cases q0 <;> rfl)
      have hmin' : IsMinU2 f (replaceGateAt D j1 g') :=
        ⟨hrep.1, fun x => (hrep.2.2 x).trans (hmin.2.1 x),
         fun D' h1 h2 => by rw [hrep.2.1]; exact hmin.2.2 D' h1 h2⟩
      rcases min_has_reader_or_out hmin' 0 (by rw [hrep.2.1]; exact h0) with hout | ⟨k, hk, hk0, hkr⟩
      · exact Or.inl hout
      · have hk' : k < D.gates.length := by rwa [replaceGateAt, List.length_set] at hk
        have hkne : k ≠ j1 := by
          intro heq; subst heq
          simp only [replaceGateAt, U2Circuit.gates, U2Gate.a, U2Gate.b, List.getElem_set_self, g'] at hkr
          omega
        simp only [replaceGateAt, U2Circuit.gates, U2Gate.a, U2Gate.b, List.getElem_set_ne (Ne.symm hkne)] at hkr
        exact Or.inr ⟨k, hk', hk0, hkne, hkr⟩
  · cases q1 with
    | false =>
      have hsp := deleteGateAt_spec D hmin.1 j1 hj1 (Sum.inl false) trivial (fun x => by
        rw [hg1 x, hg0 x]
        cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> cases p0 <;> cases p1 <;>
          simp_all [refEval])
      have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
      omega
    | true =>
      have hrepl : ∀ x : Fin 10 → Bool,
          refEval (u2Wires (D.gates.take j1) (List.ofFn x)) (Sum.inr (v, p1)) = u2Val D.gates x (10 + j1) := by
        intro x
        simp only [refEval]
        rw [u2Val_take D.gates x j1 v (by omega) (by omega), hg1 x, hg0 x]
        cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> cases p0 <;> cases p1 <;> simp_all
      have hsp := deleteGateAt_spec D hmin.1 j1 hj1 (Sum.inr (v, p1)) (by simp [refWf]; omega) hrepl
      have hbad := hmin.2.2 _ hsp.1 (fun x => (hsp.2.2 x).trans (hmin.2.1 x))
      omega

-- Constant-Propagation Restriction and Gate Elimination Bounds

def isConstRef : WireRef → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

lemma isConstRef_flipRef (fl : Bool) (r : WireRef) :
    isConstRef (flipRef fl r) = isConstRef r := by
  rcases r with c | ⟨i, f⟩ <;> rfl

lemma isConstRef_true_iff (r : WireRef) :
    isConstRef r = true ↔ ∃ c, r = Sum.inl c := by
  rcases r with c | ⟨i, f⟩
  · simp [isConstRef]
  · simp [isConstRef]

lemma passFold_getD_lt (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate)
    (i : ℕ) (hi : i < env.length) :
    (passFold cgs env gs).1.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
  induction cgs generalizing env gs with
  | nil => rfl
  | cons g cgs ih =>
    change (passFold cgs (passStep env gs g).1 (passStep env gs g).2).1.getD i (Sum.inl false) = _
    rw [ih _ _ (by simp [passStep]; omega)]
    exact getD_snoc_lt env _ (Sum.inl false) i hi

lemma passFold_count_elim (cgs : List U2Gate) (env : List WireRef) (gs : List U2Gate)
    (hcgs_wf : ∀ j (hj : j < cgs.length), cgs[j].a < env.length + j ∧ cgs[j].b < env.length + j) :
    let E := (passFold cgs env gs).1
    (passFold cgs env gs).2.length +
      ((List.finRange cgs.length).filter fun j =>
        isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
        isConstRef (E.getD cgs[j.val].b (Sum.inl false))).length =
      gs.length + cgs.length ∧
    ∀ j (hj : j < cgs.length),
      let ea := flipRef cgs[j].pa (E.getD cgs[j].a (Sum.inl false))
      let eb := flipRef cgs[j].pb (E.getD cgs[j].b (Sum.inl false))
      ((ea = Sum.inl false ∨ eb = Sum.inl false) → E.getD (env.length + j) (Sum.inl false) = Sum.inl false) ∧
      ((isConstRef ea = true ∧ isConstRef eb = true) → isConstRef (E.getD (env.length + j) (Sum.inl false)) = true) := by
  induction cgs generalizing env gs with
  | nil =>
    refine ⟨by simp [passFold], fun j hj => by simp at hj⟩
  | cons g cgs ih =>
    let st := passStep env gs g
    have hst_len : st.1.length = env.length + 1 := by simp [st, passStep]
    have h0_wf := hcgs_wf 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0_wf
    have hga : g.a < env.length := h0_wf.1
    have hgb : g.b < env.length := h0_wf.2
    have hcgs_wf' : ∀ j (hj : j < cgs.length), cgs[j].a < st.1.length + j ∧ cgs[j].b < st.1.length + j := by
      intro j hj
      have h := hcgs_wf (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at h
      omega
    obtain ⟨ih_cnt, ih_gate⟩ := ih st.1 st.2 hcgs_wf'
    let E := (passFold (g :: cgs) env gs).1
    have hE_eq : E = (passFold cgs st.1 st.2).1 := rfl
    have hEa : E.getD g.a (Sum.inl false) = env.getD g.a (Sum.inl false) := by
      rw [hE_eq, passFold_getD_lt cgs st.1 st.2 g.a (by omega)]
      exact getD_snoc_lt env _ (Sum.inl false) g.a hga
    have hEb : E.getD g.b (Sum.inl false) = env.getD g.b (Sum.inl false) := by
      rw [hE_eq, passFold_getD_lt cgs st.1 st.2 g.b (by omega)]
      exact getD_snoc_lt env _ (Sum.inl false) g.b hgb
    have hE0 : E.getD env.length (Sum.inl false) =
        (evalAndRef (flipRef g.pa (env.getD g.a (Sum.inl false)))
          (flipRef g.pb (env.getD g.b (Sum.inl false))) gs).1 := by
      rw [hE_eq, passFold_getD_lt cgs st.1 st.2 env.length (by omega)]
      exact getD_snoc_eq env _ (Sum.inl false)
    have hstep_cnt :
        st.2.length + (if (isConstRef (E.getD g.a (Sum.inl false)) ||
            isConstRef (E.getD g.b (Sum.inl false))) = true then 1 else 0) = gs.length + 1 := by
      rw [hEa, hEb]
      dsimp only [st, passStep]
      rcases ha : env.getD g.a (Sum.inl false) with ca | ⟨wa, fa⟩ <;>
        rcases hb : env.getD g.b (Sum.inl false) with cb | ⟨wb, fb⟩
      · cases ca <;> cases cb <;> cases g.pa <;> cases g.pb <;>
          simp [isConstRef, flipRef, evalAndRef]
      · cases ca <;> cases g.pa <;> simp [isConstRef, flipRef, evalAndRef]
      · cases cb <;> cases g.pb <;> simp [isConstRef, flipRef, evalAndRef]
      · simp [isConstRef, flipRef, evalAndRef]
    constructor
    · have hfin : ((List.finRange (g :: cgs).length).filter fun j =>
          isConstRef (E.getD (g :: cgs)[j.val].a (Sum.inl false)) ||
          isConstRef (E.getD (g :: cgs)[j.val].b (Sum.inl false))).length =
          (if (isConstRef (E.getD g.a (Sum.inl false)) ||
              isConstRef (E.getD g.b (Sum.inl false))) = true then 1 else 0) +
          ((List.finRange cgs.length).filter fun j =>
            isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
            isConstRef (E.getD cgs[j.val].b (Sum.inl false))).length := by
        have hfr : List.finRange (g :: cgs).length =
            ⟨0, Nat.zero_lt_succ _⟩ :: (List.finRange cgs.length).map Fin.succ := List.finRange_succ
        rw [hfr, List.filter_cons]
        have hmap : ((List.finRange cgs.length).map Fin.succ).filter (fun j : Fin (g :: cgs).length =>
              isConstRef (E.getD (g :: cgs)[j.val].a (Sum.inl false)) ||
              isConstRef (E.getD (g :: cgs)[j.val].b (Sum.inl false))) =
            ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
              isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
              isConstRef (E.getD cgs[j.val].b (Sum.inl false))).map Fin.succ := by
          rw [List.filter_map]
          rfl
        rw [hmap]
        dsimp only
        simp only [List.getElem_cons_zero]
        have hif : ∀ b : Bool,
            (if b = true then
              (⟨0, Nat.zero_lt_succ _⟩ : Fin (g :: cgs).length) ::
                ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
                  isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
                  isConstRef (E.getD cgs[j.val].b (Sum.inl false))).map Fin.succ
            else
              ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
                isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
                isConstRef (E.getD cgs[j.val].b (Sum.inl false))).map Fin.succ).length =
            (if b = true then 1 else 0) +
              ((List.finRange cgs.length).filter fun j : Fin cgs.length =>
                isConstRef (E.getD cgs[j.val].a (Sum.inl false)) ||
                isConstRef (E.getD cgs[j.val].b (Sum.inl false))).length := by
          intro b; cases b
          · simp
          · simp; omega
        exact hif _
      change (passFold cgs st.1 st.2).2.length + _ = gs.length + (g :: cgs).length
      rw [hfin]
      change (passFold cgs st.1 st.2).2.length + ((if (isConstRef ((passFold cgs st.1 st.2).1.getD g.a (Sum.inl false)) ||
          isConstRef ((passFold cgs st.1 st.2).1.getD g.b (Sum.inl false))) = true then 1 else 0) +
          ((List.finRange cgs.length).filter fun j =>
            isConstRef ((passFold cgs st.1 st.2).1.getD cgs[j.val].a (Sum.inl false)) ||
            isConstRef ((passFold cgs st.1 st.2).1.getD cgs[j.val].b (Sum.inl false))).length) =
        gs.length + (g :: cgs).length
      change st.2.length + (if (isConstRef ((passFold cgs st.1 st.2).1.getD g.a (Sum.inl false)) ||
          isConstRef ((passFold cgs st.1 st.2).1.getD g.b (Sum.inl false))) = true then 1 else 0) =
        gs.length + 1 at hstep_cnt
      simp only [List.length_cons]
      omega
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hEa, hEb, hE0]
        constructor
        · intro h
          rcases h with ha | hb
          · rw [ha]; exact evalAndRef_const_left _ _
          · rw [hb]; exact evalAndRef_const_right _ _
        · rintro ⟨ha, hb⟩
          obtain ⟨ca, hca⟩ := (isConstRef_true_iff _).mp ha
          obtain ⟨cb, hcb⟩ := (isConstRef_true_iff _).mp hb
          rw [hca, hcb]
          obtain ⟨c, hc⟩ := evalAndRef_const_both ca cb gs
          rw [hc]; rfl
      | succ j =>
        have hj' : j < cgs.length := by simpa using hj
        have h := ih_gate j hj'
        have hidx : env.length + (j + 1) = st.1.length + j := by omega
        simp only [List.getElem_cons_succ]
        rw [hidx]
        exact h

def restrictEnv (v : Fin 10) (val : Bool) : List WireRef :=
  (List.range 10).map fun i => if i = v.val then Sum.inl val else Sum.inr (i, false)

def restrictRun (gs : List U2Gate) (v : Fin 10) (val : Bool) : List WireRef × List U2Gate :=
  passFold gs (restrictEnv v val) []

def restrictU2 (D : U2Circuit) (v : Fin 10) (val : Bool) : U2Circuit :=
  let res := restrictRun D.gates v val
  let out' := match D.out with
    | Sum.inl c => Sum.inl c
    | Sum.inr (w, fl) => flipRef fl (res.1.getD w (Sum.inl false))
  ⟨res.2, out'⟩

def elimSet (D : U2Circuit) (v : Fin 10) (val : Bool) : Finset (Fin D.gates.length) :=
  let E := (restrictRun D.gates v val).1
  Finset.univ.filter fun j : Fin D.gates.length =>
    isConstRef (E.getD D.gates[j.val].a (Sum.inl false)) = true ∨
    isConstRef (E.getD D.gates[j.val].b (Sum.inl false)) = true

lemma restrictU2_spec (D : U2Circuit) (hD : U2Wf D) (v : Fin 10) (val : Bool) :
    let E := (restrictRun D.gates v val).1
    U2Wf (restrictU2 D v val) ∧
    (∀ x : Fin 10 → Bool, u2Eval (restrictU2 D v val) x = u2Eval D (Function.update x v val)) ∧
    (restrictU2 D v val).gates.length + (elimSet D v val).card = D.gates.length ∧
    E.getD v.val (Sum.inl false) = Sum.inl val ∧
    (∀ j (hj : j < D.gates.length),
      let ea := flipRef D.gates[j].pa (E.getD D.gates[j].a (Sum.inl false))
      let eb := flipRef D.gates[j].pb (E.getD D.gates[j].b (Sum.inl false))
      ((ea = Sum.inl false ∨ eb = Sum.inl false) → E.getD (10 + j) (Sum.inl false) = Sum.inl false) ∧
      ((isConstRef ea = true ∧ isConstRef eb = true) → isConstRef (E.getD (10 + j) (Sum.inl false)) = true)) := by
  have henv_len : (restrictEnv v val).length = 10 := by simp [restrictEnv]
  have henv_wf : ∀ r ∈ restrictEnv v val, refWf (10 + ([] : List U2Gate).length) r := by
    intro r hr
    simp only [restrictEnv, List.mem_map, List.mem_range] at hr
    rcases hr with ⟨i, hi, rfl⟩
    by_cases h : i = v.val
    · simp [h, refWf]
    · simp [h, refWf]; omega
  have hsp := passFold_spec D.gates (restrictEnv v val) [] (fun j hj => by simp at hj) henv_wf
  rcases hsp with ⟨hwf2, henv2, hlen2, _, hev2⟩
  have hcnt := passFold_count_elim D.gates (restrictEnv v val) [] (by
    intro j hj; rw [henv_len]; exact hD.1 j hj)
  rcases hcnt with ⟨hsum, hgate⟩
  refine ⟨⟨hwf2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [restrictU2]
    rcases D.out with c | ⟨w, fl⟩
    · trivial
    · exact (refWf_flipRef _ _ _).mpr (getD_env_wf _ _ henv2 w)
  · intro x
    have hagree0 : ∀ i < (restrictEnv v val).length,
        refEval (u2Wires [] (List.ofFn x)) ((restrictEnv v val).getD i (Sum.inl false)) =
          (List.ofFn (Function.update x v val)).getD i false := by
      intro i hi
      rw [henv_len] at hi
      have hget : (restrictEnv v val).getD i (Sum.inl false) =
          if i = v.val then Sum.inl val else Sum.inr (i, false) := by
        simp [restrictEnv, List.getD_eq_getElem?_getD, hi]
      rw [hget]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
      by_cases h : i = v.val
      · simp only [h, ↓reduceIte, refEval, Function.update_self]
      · have hfin : (⟨i, hi⟩ : Fin 10) ≠ v := fun heq => h (congrArg Fin.val heq)
        simp only [h, ↓reduceIte, refEval, Bool.bne_false, u2Wires, List.foldl_nil,
          Function.update_of_ne hfin]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
    have hev_all := hev2 (List.ofFn x) (List.ofFn (Function.update x v val)) (by simp)
      (by simp [henv_len]) hagree0
    dsimp only [u2Eval, restrictU2]
    rcases hout : D.out with c | ⟨w, fl⟩
    · rfl
    · rw [refEval_flipRef]
      have hw : w < 10 + D.gates.length := by
        have := hD.2; rw [hout] at this; exact this
      have hw' : w < (restrictRun D.gates v val).1.length := by
        change w < (passFold D.gates (restrictEnv v val) []).1.length
        rw [hlen2, henv_len]; exact hw
      unfold restrictRun
      rw [hev_all w hw']
      rfl
  · change (restrictRun D.gates v val).2.length + (elimSet D v val).card = D.gates.length
    have hcard_eq : (elimSet D v val).card =
        ((List.finRange D.gates.length).filter fun j =>
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].a (Sum.inl false)) ||
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].b (Sum.inl false))).length := by
      have hnodup : ((List.finRange D.gates.length).filter fun j =>
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].a (Sum.inl false)) ||
          isConstRef ((restrictRun D.gates v val).1.getD D.gates[j.val].b (Sum.inl false))).Nodup :=
        (List.nodup_finRange _).filter _
      rw [← List.toFinset_card_of_nodup hnodup]
      congr 1
      ext j
      simp [elimSet, Bool.or_eq_true]
    rw [hcard_eq]
    simpa [restrictRun] using hsum
  · unfold restrictRun
    rw [passFold_getD_lt D.gates (restrictEnv v val) [] v.val (by rw [henv_len]; exact v.isLt)]
    simp [restrictEnv, List.getD_eq_getElem?_getD, v.isLt]
  · intro j hj
    have h := hgate j hj
    rw [henv_len] at h
    exact h

lemma not_out_of_isConst {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hD : U2Wf D) (hev : ∀ x, u2Eval D x = f x) (v : Fin 10) (val : Bool)
    (hnc : ∃ x y : Fin 10 → Bool, f (Function.update x v val) ≠ f (Function.update y v val))
    (j : ℕ) (hconst : isConstRef ((restrictRun D.gates v val).1.getD (10 + j) (Sum.inl false)) = true) :
    ∀ fl, D.out ≠ Sum.inr (10 + j, fl) := by
  intro fl hout
  obtain ⟨c, hc⟩ := (isConstRef_true_iff _).mp hconst
  obtain ⟨hwf', hev', _⟩ := restrictU2_spec D hD v val
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev, ← hev, ← hev' x, ← hev' y]
  unfold u2Eval restrictU2
  rw [hout]
  dsimp only
  rw [hc]
  simp [refEval, flipRef]

lemma elim_ge_1 {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 10) (val : Bool)
    (j : ℕ) (hj : j < D.gates.length) (hread : D.gates[j].a = v.val ∨ D.gates[j].b = v.val) :
    ∃ s', s' + 1 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v val)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, _⟩ := restrictU2_spec D hmin.1 v val
  have hjmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hread with ha | hb
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have hcard : 1 ≤ (elimSet D v val).card := Finset.one_le_card.mpr ⟨⟨j, hj⟩, hjmem⟩
  exact ⟨(restrictU2 D v val).gates.length, by omega,
    restrictU2 D v val, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

lemma elim_ge_2_ctrl {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 10) (p : Bool)
    (hnc : ∃ x y : Fin 10 → Bool, f (Function.update x v p) ≠ f (Function.update y v p))
    (j : ℕ) (hj : j < D.gates.length)
    (hread : (D.gates[j].a = v.val ∧ D.gates[j].pa = p) ∨ (D.gates[j].b = v.val ∧ D.gates[j].pb = p)) :
    ∃ s', s' + 2 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v p)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, hgate⟩ := restrictU2_spec D hmin.1 v p
  have hEj : (restrictRun D.gates v p).1.getD (10 + j) (Sum.inl false) = Sum.inl false := by
    apply (hgate j hj).1
    rcases hread with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
    · left; rw [ha, hpa, hEv]; cases p <;> rfl
    · right; rw [hb, hpb, hEv]; cases p <;> rfl
  have hnotout := not_out_of_isConst hmin.1 hmin.2.1 v p hnc j (by rw [hEj]; rfl)
  rcases min_has_reader_or_out hmin j hj with ⟨fl, hout⟩ | ⟨k, hk, hjk, hkr⟩
  · exact (hnotout fl hout).elim
  · have hjmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ elimSet D v p := by
      simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hread with ⟨ha, _⟩ | ⟨hb, _⟩
      · left; rw [ha, hEv]; rfl
      · right; rw [hb, hEv]; rfl
    have hkmem : (⟨k, hk⟩ : Fin D.gates.length) ∈ elimSet D v p := by
      simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hkr with ha | hb
      · left; rw [ha, hEj]; rfl
      · right; rw [hb, hEj]; rfl
    have hne : (⟨j, hj⟩ : Fin D.gates.length) ≠ ⟨k, hk⟩ := fun h => by
      have hjk' : j = k := congrArg Fin.val h
      omega
    have hsub : ({⟨j, hj⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v p := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hcard : 2 ≤ (elimSet D v p).card := by
      calc 2 = ({⟨j, hj⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)).card := by
            rw [Finset.card_pair hne]
        _ ≤ (elimSet D v p).card := Finset.card_le_card hsub
    exact ⟨(restrictU2 D v p).gates.length, by omega,
      restrictU2 D v p, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

lemma elim_ge_2_two {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (v : Fin 10) (val : Bool)
    (j0 j1 : ℕ) (hj0 : j0 < D.gates.length) (hj1 : j1 < D.gates.length) (hne : j0 ≠ j1)
    (hr0 : D.gates[j0].a = v.val ∨ D.gates[j0].b = v.val)
    (hr1 : D.gates[j1].a = v.val ∨ D.gates[j1].b = v.val) :
    ∃ s', s' + 2 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v val)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, _⟩ := restrictU2_spec D hmin.1 v val
  have hmem : ∀ (j : ℕ) (hj : j < D.gates.length),
      (D.gates[j].a = v.val ∨ D.gates[j].b = v.val) →
      (⟨j, hj⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    intro j hj hr
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr with ha | hb
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have hsub : ({⟨j0, hj0⟩, ⟨j1, hj1⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v val := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem j0 hj0 hr0
    · exact hmem j1 hj1 hr1
  have hcard : 2 ≤ (elimSet D v val).card := by
    calc 2 = ({⟨j0, hj0⟩, ⟨j1, hj1⟩} : Finset (Fin D.gates.length)).card := by
          rw [Finset.card_pair (fun h => hne (congrArg Fin.val h))]
      _ ≤ (elimSet D v val).card := Finset.card_le_card hsub
  exact ⟨(restrictU2 D v val).gates.length, by omega,
    restrictU2 D v val, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

-- Helper to extract the canonical form of gate 0 reading `(v, p0)` and `(u, q0)`.
lemma gate0_eval_form {D : U2Circuit} (hD : U2Wf D) (h0 : 0 < D.gates.length)
    (v : ℕ) (p0 : Bool)
    (hr : (D.gates[0].a = v ∧ D.gates[0].pa = p0) ∨ (D.gates[0].b = v ∧ D.gates[0].pb = p0)) :
    ∃ u q0, u < 10 ∧
      ∀ x : Fin 10 → Bool, u2Val D.gates x 10 = ((u2Val D.gates x v != p0) && (u2Val D.gates x u != q0)) := by
  have ha0 := (hD.1 0 h0).1
  have hb0 := (hD.1 0 h0).2
  rcases hr with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
  · refine ⟨D.gates[0].b, D.gates[0].pb, by omega, fun x => ?_⟩
    have h := u2Val_gate D.gates x 0 h0 ha0 hb0
    simpa [ha, hpa] using h
  · refine ⟨D.gates[0].a, D.gates[0].pa, by omega, fun x => ?_⟩
    have h := u2Val_gate D.gates x 0 h0 ha0 hb0
    rw [hb, hpb, Bool.and_comm] at h
    simpa using h

-- Helper to extract the canonical form of gate `j1` reading `(v, p1)` and `(10, q1)`.
lemma gateJ_eval_form {D : U2Circuit} (hD : U2Wf D) (j1 : ℕ) (hj1 : j1 < D.gates.length)
    (v : ℕ) (hv : v < 10) (p1 : Bool)
    (hrv : (D.gates[j1].a = v ∧ D.gates[j1].pa = p1) ∨ (D.gates[j1].b = v ∧ D.gates[j1].pb = p1))
    (hr9 : D.gates[j1].a = 10 ∨ D.gates[j1].b = 10) :
    ∃ q1, ∀ x : Fin 10 → Bool, u2Val D.gates x (10 + j1) = ((u2Val D.gates x v != p1) && (u2Val D.gates x 10 != q1)) := by
  have ha1 := (hD.1 j1 hj1).1
  have hb1 := (hD.1 j1 hj1).2
  rcases hrv with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
  · rcases hr9 with h9 | h9
    · omega
    · refine ⟨D.gates[j1].pb, fun x => ?_⟩
      have h := u2Val_gate D.gates x j1 hj1 ha1 hb1
      simpa [ha, hpa, h9] using h
  · rcases hr9 with h9 | h9
    · refine ⟨D.gates[j1].pa, fun x => ?_⟩
      have h := u2Val_gate D.gates x j1 hj1 ha1 hb1
      rw [hb, hpb, h9, Bool.and_comm] at h
      exact h
    · omega

lemma elim_ge_3_opp {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v : Fin 10) (p0 : Bool)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = p0) ∨ (D.gates[0].b = v.val ∧ D.gates[0].pb = p0))
    (j1 : ℕ) (hj1 : j1 < D.gates.length) (hj1_pos : 0 < j1)
    (hr1 : (D.gates[j1].a = v.val ∧ D.gates[j1].pa = !p0) ∨ (D.gates[j1].b = v.val ∧ D.gates[j1].pb = !p0))
    (val : Bool)
    (hnc : ∃ x y : Fin 10 → Bool, f (Function.update x v val) ≠ f (Function.update y v val)) :
    ∃ s', s' + 3 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v val)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, hgate⟩ := restrictU2_spec D hmin.1 v val
  have h0_mem : (⟨0, h0⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr0 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have h1_mem : (⟨j1, hj1⟩ : Fin D.gates.length) ∈ elimSet D v val := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr1 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  by_cases hvp : val = p0
  · subst hvp
    have hE0 : (restrictRun D.gates v val).1.getD 10 (Sum.inl false) = Sum.inl false := by
      have := (hgate 0 h0).1
      apply this
      rcases hr0 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
      · left; rw [ha, hpa, hEv]; cases val <;> rfl
      · right; rw [hb, hpb, hEv]; cases val <;> rfl
    have hnotout := not_out_of_isConst hmin.1 hmin.2.1 v val hnc 0 (by simp only [Nat.add_zero]; rw [hE0]; rfl)
    rcases min_has_reader_or_out hmin 0 h0 with ⟨fl, hout⟩ | ⟨k, hk, hk0, hkr⟩
    · exact (hnotout fl hout).elim
    · have hkne : k ≠ j1 := by
        intro heq; subst heq
        obtain ⟨u, q0, hu, hg0⟩ := gate0_eval_form hmin.1 h0 v.val val hr0
        obtain ⟨q1, hg1⟩ := gateJ_eval_form hmin.1 k hk v.val v.isLt (!val) hr1 hkr
        have hint := min_gate0_interact hmin h0 v.val u val q0 v.isLt hu hg0 k hk hk0 (!val) q1 hg1
        cases val <;> simp at hint
      have hk_mem : (⟨k, hk⟩ : Fin D.gates.length) ∈ elimSet D v val := by
        simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hkr with ha | hb
        · left; rw [ha, hE0]; rfl
        · right; rw [hb, hE0]; rfl
      have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v val := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard : 3 ≤ (elimSet D v val).card := by
        have h3 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; exact hkne (congrArg Fin.val h).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = k := congrArg Fin.val h; omega⟩
        calc 3 = _ := h3.symm
          _ ≤ (elimSet D v val).card := Finset.card_le_card hsub
      exact ⟨(restrictU2 D v val).gates.length, by omega,
        restrictU2 D v val, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩
  · have hval_eq : val = !p0 := by cases val <;> cases p0 <;> simp_all
    subst hval_eq
    have hE1 : (restrictRun D.gates v (!p0)).1.getD (10 + j1) (Sum.inl false) = Sum.inl false := by
      apply (hgate j1 hj1).1
      rcases hr1 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
      · left; rw [ha, hpa, hEv]; cases p0 <;> rfl
      · right; rw [hb, hpb, hEv]; cases p0 <;> rfl
    have hnotout := not_out_of_isConst hmin.1 hmin.2.1 v (!p0) hnc j1 (by rw [hE1]; rfl)
    rcases min_has_reader_or_out hmin j1 hj1 with ⟨fl, hout⟩ | ⟨k, hk, hk1, hkr⟩
    · exact (hnotout fl hout).elim
    · have hk_mem : (⟨k, hk⟩ : Fin D.gates.length) ∈ elimSet D v (!p0) := by
        simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hkr with ha | hb
        · left; rw [ha, hE1]; rfl
        · right; rw [hb, hE1]; rfl
      have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v (!p0) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard : 3 ≤ (elimSet D v (!p0)).card := by
        have h3 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k, hk⟩} : Finset (Fin D.gates.length)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; have h' : j1 = k := congrArg Fin.val h; omega
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = k := congrArg Fin.val h; omega⟩
        calc 3 = _ := h3.symm
          _ ≤ (elimSet D v (!p0)).card := Finset.card_le_card hsub
      exact ⟨(restrictU2 D v (!p0)).gates.length, by omega,
        restrictU2 D v (!p0), hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

lemma elim_ge_4_same {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v : Fin 10) (p0 : Bool)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = p0) ∨ (D.gates[0].b = v.val ∧ D.gates[0].pb = p0))
    (j1 : ℕ) (hj1 : j1 < D.gates.length) (hj1_pos : 0 < j1)
    (hr1 : (D.gates[j1].a = v.val ∧ D.gates[j1].pa = p0) ∨ (D.gates[j1].b = v.val ∧ D.gates[j1].pb = p0))
    (hnc : ∃ x y : Fin 10 → Bool, f (Function.update x v p0) ≠ f (Function.update y v p0)) :
    ∃ s', s' + 4 ≤ D.gates.length ∧ HasU2Size (fun x => f (Function.update x v p0)) s' := by
  obtain ⟨hwf', hev', hlen', hEv, hgate⟩ := restrictU2_spec D hmin.1 v p0
  have hE0 : (restrictRun D.gates v p0).1.getD 10 (Sum.inl false) = Sum.inl false := by
    apply (hgate 0 h0).1
    rcases hr0 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
    · left; rw [ha, hpa, hEv]; cases p0 <;> rfl
    · right; rw [hb, hpb, hEv]; cases p0 <;> rfl
  have hE1 : (restrictRun D.gates v p0).1.getD (10 + j1) (Sum.inl false) = Sum.inl false := by
    apply (hgate j1 hj1).1
    rcases hr1 with ⟨ha, hpa⟩ | ⟨hb, hpb⟩
    · left; rw [ha, hpa, hEv]; cases p0 <;> rfl
    · right; rw [hb, hpb, hEv]; cases p0 <;> rfl
  have h0_mem : (⟨0, h0⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr0 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have h1_mem : (⟨j1, hj1⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr1 with ⟨ha, _⟩ | ⟨hb, _⟩
    · left; rw [ha, hEv]; rfl
    · right; rw [hb, hEv]; rfl
  have hnotout0 := not_out_of_isConst hmin.1 hmin.2.1 v p0 hnc 0 (by simp only [Nat.add_zero]; rw [hE0]; rfl)
  have hnotout1 := not_out_of_isConst hmin.1 hmin.2.1 v p0 hnc j1 (by rw [hE1]; rfl)
  -- Find reader k1 of j1 (automatically k1 > j1 > 0)
  obtain ⟨k1, hk1, hk1_gt, hk1_r⟩ :
      ∃ k1, ∃ (hk1 : k1 < D.gates.length), j1 < k1 ∧ (D.gates[k1].a = 10 + j1 ∨ D.gates[k1].b = 10 + j1) := by
    rcases min_has_reader_or_out hmin j1 hj1 with ⟨fl, hout⟩ | h
    · exact (hnotout1 fl hout).elim
    · exact h
  -- Find reader k0 ≠ j1 of gate 0
  obtain ⟨k0, hk0, hk0_pos, hk0_ne, hk0_r⟩ :
      ∃ k0, ∃ (hk0 : k0 < D.gates.length), 0 < k0 ∧ k0 ≠ j1 ∧ (D.gates[k0].a = 10 ∨ D.gates[k0].b = 10) := by
    rcases min_has_reader_or_out hmin 0 h0 with ⟨fl, hout⟩ | ⟨k, hk, hk_pos, hkr⟩
    · exact (hnotout0 fl hout).elim
    · by_cases hkj : k = j1
      · subst hkj
        obtain ⟨u, q0, hu, hg0⟩ := gate0_eval_form hmin.1 h0 v.val p0 hr0
        obtain ⟨q1, hg1⟩ := gateJ_eval_form hmin.1 k hk v.val v.isLt p0 hr1 hkr
        have hint := min_gate0_interact hmin h0 v.val u p0 q0 v.isLt hu hg0 k hk hk_pos p0 q1 hg1
        rcases hint.2.2 with ⟨fl, hout⟩ | h2
        · exact (hnotout0 fl hout).elim
        · exact h2
      · exact ⟨k, hk, hk_pos, hkj, hkr⟩
  have hk0_mem : (⟨k0, hk0⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hk0_r with ha | hb
    · left; rw [ha, hE0]; rfl
    · right; rw [hb, hE0]; rfl
  have hk1_mem : (⟨k1, hk1⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hk1_r with ha | hb
    · left; rw [ha, hE1]; rfl
    · right; rw [hb, hE1]; rfl
  have hcard4 : 4 ≤ (elimSet D v p0).card := by
    by_cases hkk : k0 = k1
    · subst hkk
      -- k0 reads BOTH 10 and 10 + j1 (which are distinct since j1 > 0), so both inputs of k0 are const!
      have hboth : isConstRef ((restrictRun D.gates v p0).1.getD D.gates[k0].a (Sum.inl false)) = true ∧
          isConstRef ((restrictRun D.gates v p0).1.getD D.gates[k0].b (Sum.inl false)) = true := by
        rcases hk0_r with ha0 | hb0 <;> rcases hk1_r with ha1 | hb1
        · omega
        · exact ⟨by rw [ha0, hE0]; rfl, by rw [hb1, hE1]; rfl⟩
        · exact ⟨by rw [ha1, hE1]; rfl, by rw [hb0, hE0]; rfl⟩
        · omega
      have hEk0 : isConstRef ((restrictRun D.gates v p0).1.getD (10 + k0) (Sum.inl false)) = true := by
        apply (hgate k0 hk0).2
        rw [isConstRef_flipRef, isConstRef_flipRef]
        exact hboth
      have hnotoutk := not_out_of_isConst hmin.1 hmin.2.1 v p0 hnc k0 hEk0
      rcases min_has_reader_or_out hmin k0 hk0 with ⟨fl, hout⟩ | ⟨r, hr, hr_gt, hrr⟩
      · exact (hnotoutk fl hout).elim
      · have hr_mem : (⟨r, hr⟩ : Fin D.gates.length) ∈ elimSet D v p0 := by
          simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hrr with ha | hb
          · left; rw [ha]; exact hEk0
          · right; rw [hb]; exact hEk0
        have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨r, hr⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v p0 := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨r, hr⟩} : Finset (Fin D.gates.length)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h; have h' : k0 = r := congrArg Fin.val h; omega
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : j1 = k0 := congrArg Fin.val h; omega,
                   fun h => by have h' : j1 = r := congrArg Fin.val h; omega⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = k0 := congrArg Fin.val h; omega,
                   fun h => by have h' : 0 = r := congrArg Fin.val h; omega⟩
        calc 4 = _ := h4.symm
          _ ≤ (elimSet D v p0).card := Finset.card_le_card hsub
    · have hsub : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨k1, hk1⟩} : Finset (Fin D.gates.length)) ⊆ elimSet D v p0 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      have h4 : ({⟨0, h0⟩, ⟨j1, hj1⟩, ⟨k0, hk0⟩, ⟨k1, hk1⟩} : Finset (Fin D.gates.length)).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h; exact hkk (congrArg Fin.val h)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hk0_ne (congrArg Fin.val h).symm,
                 fun h => by have h' : j1 = k1 := congrArg Fin.val h; omega⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => by have h' : 0 = j1 := congrArg Fin.val h; omega,
                 fun h => by have h' : 0 = k0 := congrArg Fin.val h; omega,
                 fun h => by have h' : 0 = k1 := congrArg Fin.val h; omega⟩
      calc 4 = _ := h4.symm
        _ ≤ (elimSet D v p0).card := Finset.card_le_card hsub
  exact ⟨(restrictU2 D v p0).gates.length, by omega,
    restrictU2 D v p0, hwf', Nat.le_refl _, fun x => (hev' x).trans (hmin.2.1 _)⟩

-- Slot-Counting Lower Bound and Single-Fanout First-Gate Lemma

def u2Slots (D : U2Circuit) : List ℕ :=
  (match D.out with | Sum.inl _ => [] | Sum.inr (w, _) => [w]) ++
    D.gates.flatMap fun g => [g.a, g.b]

lemma u2Slots_length (D : U2Circuit) :
    (u2Slots D).length ≤ 2 * D.gates.length + 1 := by
  have hflat : ∀ gs : List U2Gate, (gs.flatMap fun g => [g.a, g.b]).length = 2 * gs.length := by
    intro gs; induction gs with
    | nil => simp
    | cons g gs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
  unfold u2Slots
  rw [List.length_append, hflat]
  rcases D.out with c | ⟨w, fl⟩
  · simp
  · simp; omega

lemma u2Wires_agree_except (gs : List U2Gate) (u : ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hno : ∀ g ∈ gs, g.a ≠ u ∧ g.b ≠ u)
    (hagree : ∀ i, i ≠ u → w₁.getD i false = w₂.getD i false) :
    ∀ i, i ≠ u → (u2Wires gs w₁).getD i false = (u2Wires gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hagree
  | cons g gs ih =>
    have hg := hno g List.mem_cons_self
    have hstep_eq : ((w₁.getD g.a false != g.pa) && (w₁.getD g.b false != g.pb)) =
        ((w₂.getD g.a false != g.pa) && (w₂.getD g.b false != g.pb)) := by
      rw [hagree g.a hg.1, hagree g.b hg.2]
    rw [u2Wires_cons, u2Wires_cons]
    apply ih (u2Step w₁ g) (u2Step w₂ g) (by simp [u2Step, hlen])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    by_cases hlt : i < w₁.length
    · simp only [u2Step]
      rw [getD_snoc_lt _ _ _ i hlt, getD_snoc_lt _ _ _ i (by omega)]
      exact hagree i hi
    · by_cases heq : i = w₁.length
      · subst heq
        simp only [u2Step]
        rw [getD_snoc_eq, hlen, getD_snoc_eq, hstep_eq]
      · simp only [u2Step]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_mem_u2Slots {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hev : ∀ x, u2Eval D x = f x) (v : Fin 10)
    (hess : ∃ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) ∧ f x ≠ f y) :
    v.val ∈ u2Slots D := by
  by_contra hnot
  obtain ⟨x, y, hxy, hne⟩ := hess
  have hout : ∀ fl, D.out ≠ Sum.inr (v.val, fl) := by
    intro fl h
    apply hnot
    simp [u2Slots, h]
  have hno : ∀ g ∈ D.gates, g.a ≠ v.val ∧ g.b ≠ v.val := by
    intro g hg
    constructor <;> intro heq <;> apply hnot
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, hg, by simp [heq]⟩)
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, hg, by simp [heq]⟩)
  have hagree0 : ∀ i, i ≠ v.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i hi
    by_cases hlt : i < 10
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      exact hxy ⟨i, hlt⟩ (fun h => hi (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
  have hagree := u2Wires_agree_except D.gates v.val (List.ofFn x) (List.ofFn y) (by simp) hno hagree0
  apply hne
  rw [← hev x, ← hev y]
  unfold u2Eval
  rcases h : D.out with c | ⟨w, fl⟩
  · rfl
  · simp only [refEval]
    have hw : w ≠ v.val := fun heq => hout fl (by rw [h, heq])
    rw [hagree w hw]

lemma slot_lower_bound {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (S : Finset (Fin 10))
    (hS : ∀ v ∈ S, ∃ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) ∧ f x ≠ f y) :
    S.card - 1 ≤ D.gates.length := by
  let A : Finset ℕ := S.image Fin.val
  let B : Finset ℕ := (Finset.range D.gates.length).image (fun j => 10 + j)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    simp only [A, B, Finset.mem_image, Finset.mem_range] at hwA hwB
    rcases hwA with ⟨v, _, rfl⟩
    rcases hwB with ⟨j, _, hj⟩
    have := v.isLt; omega
  have hA : A.card = S.card := Finset.card_image_of_injective S Fin.val_injective
  have hB : B.card = D.gates.length := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  have hsub : A ∪ B ⊆ (u2Slots D).toFinset := by
    intro w hw
    rw [List.mem_toFinset]
    simp only [Finset.mem_union, A, B, Finset.mem_image, Finset.mem_range] at hw
    rcases hw with ⟨v, hvS, rfl⟩ | ⟨j, hj, rfl⟩
    · exact essential_mem_u2Slots hmin.2.1 v (hS v hvS)
    · rcases min_has_reader_or_out hmin j hj with ⟨fl, hout⟩ | ⟨k, hk, _, hkr⟩
      · simp [u2Slots, hout]
      · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨D.gates[k], List.getElem_mem hk, ?_⟩)
        rcases hkr with ha | hb
        · simp [ha]
        · simp [hb]
  have hle1 : (A ∪ B).card ≤ (u2Slots D).toFinset.card := Finset.card_le_card hsub
  have hle2 : (u2Slots D).toFinset.card ≤ (u2Slots D).length := List.toFinset_card_le _
  have hle3 := u2Slots_length D
  rw [Finset.card_union_of_disjoint hdisj, hA, hB] at hle1
  omega

lemma single_fanout_first_gate {f : (Fin 10 → Bool) → Bool} {D : U2Circuit}
    (hmin : IsMinU2 f D) (h0 : 0 < D.gates.length)
    (v u : Fin 10) (pv pu : Bool) (hvu : v ≠ u)
    (hg0 : ∀ x : Fin 10 → Bool, u2Val D.gates x 10 = ((u2Val D.gates x v.val != pv) && (u2Val D.gates x u.val != pu)))
    (hout : ∀ fl, D.out ≠ Sum.inr (v.val, fl))
    (hno : ∀ k (hk : k < D.gates.length), 0 < k → D.gates[k].a ≠ v.val ∧ D.gates[k].b ≠ v.val) :
    ∀ x : Fin 10 → Bool,
      f (Function.update (Function.update x u pu) v false) =
      f (Function.update (Function.update x u pu) v true) := by
  intro x
  let x0 := Function.update (Function.update x u pu) v false
  let x1 := Function.update (Function.update x u pu) v true
  have hsplit : D.gates = D.gates[0] :: D.gates.drop 1 :=
    List.drop_eq_getElem_cons h0
  have hstep0 : ∀ z : Fin 10 → Bool, z u = pu →
      (u2Step (List.ofFn z) D.gates[0]).getD 10 false = false := by
    intro z hzu
    have h1 := hg0 z
    have hu_val : u2Val D.gates z u.val = pu := by rw [u2Val_input _ _ u.val u.isLt]; exact hzu
    rw [hu_val] at h1
    have hfalse : u2Val D.gates z 10 = false := by
      rw [h1]; cases (u2Val D.gates z v.val != pv) <;> cases pu <;> rfl
    unfold u2Val at hfalse
    rw [hsplit, u2Wires_cons] at hfalse
    rw [u2Wires_getD_lt _ _ 10 (by simp only [u2Step, List.length_append, List.length_ofFn, List.length_singleton]; omega)] at hfalse
    exact hfalse
  have hno_drop : ∀ g ∈ D.gates.drop 1, g.a ≠ v.val ∧ g.b ≠ v.val := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    have hlt : 1 + t < D.gates.length := by simp at ht; omega
    have h := hno (1 + t) hlt (by omega)
    simpa [List.getElem_drop, Nat.add_comm] using h
  have hstep_agree : ∀ i, i ≠ v.val →
      (u2Step (List.ofFn x0) D.gates[0]).getD i false = (u2Step (List.ofFn x1) D.gates[0]).getD i false := by
    intro i hi
    by_cases hlt : i < 10
    · simp only [u2Step]
      rw [getD_snoc_lt _ _ _ i (by rw [List.length_ofFn]; exact hlt),
          getD_snoc_lt _ _ _ i (by rw [List.length_ofFn]; exact hlt),
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have hne : (⟨i, hlt⟩ : Fin 10) ≠ v := fun h => hi (congrArg Fin.val h)
      simp [x0, x1, Function.update_of_ne hne]
    · by_cases heq : i = 10
      · subst heq
        rw [hstep0 x0 (by simp [x0, Function.update_of_ne hvu.symm]),
            hstep0 x1 (by simp [x1, Function.update_of_ne hvu.symm])]
      · simp only [u2Step]
        rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
  have hfinal := u2Wires_agree_except (D.gates.drop 1) v.val
    (u2Step (List.ofFn x0) D.gates[0]) (u2Step (List.ofFn x1) D.gates[0])
    (by simp [u2Step]) hno_drop hstep_agree
  rw [← hmin.2.1 x0, ← hmin.2.1 x1]
  unfold u2Eval
  rcases h : D.out with c | ⟨w, fl⟩
  · rfl
  · simp only [refEval]
    have hw : w ≠ v.val := fun heq => hout fl (by rw [h, heq])
    rw [hsplit, u2Wires_cons, u2Wires_cons, hfinal w hw]


end PEqualNP.Outside.L_meta_2592.Signed


namespace PEqualNP.Outside.L_meta_2592_aux.PairSeparation

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def pairInput (a b w : Fin 10) (u v : Bool) : Fin 10 → Bool :=
  fun i => if i = a then u else if i = b then v else decide (i = w)

set_option maxHeartbeats 1000000 in
lemma firstProjection : ∀ a b : Fin 10, a ≠ b →
    ∃ w : Fin 10, ∀ u v : Bool, pet (pairInput a b w u v) = u := by
  decide +kernel

lemma pairInput_swap (a b w : Fin 10) (hne : a ≠ b) (u v : Bool) :
    pairInput b a w v u = pairInput a b w u v := by
  funext i
  by_cases ha : i = a
  · subst i
    simp [pairInput, hne]
  · by_cases hb : i = b
    · subst i
      simp [pairInput, hne.symm]
    · simp [pairInput, ha, hb]

lemma secondProjection (a b : Fin 10) (hne : a ≠ b) :
    ∃ w : Fin 10, ∀ u v : Bool, pet (pairInput a b w u v) = v := by
  obtain ⟨w, hw⟩ := firstProjection b a hne.symm
  refine ⟨w, ?_⟩
  intro u v
  rw [← pairInput_swap a b w hne u v]
  exact hw v u

lemma noPairFactor (a b : Fin 10) (hne : a ≠ b) (q : Bool → Bool → Bool)
    (factor : ∀ w : Fin 10, ∃ r : Bool → Bool,
      ∀ u v : Bool, pet (pairInput a b w u v) = r (q u v)) : False := by
  obtain ⟨wa, ha⟩ := firstProjection a b hne
  obtain ⟨wb, hb⟩ := secondProjection a b hne
  obtain ⟨ra, hra⟩ := factor wa
  obtain ⟨rb, hrb⟩ := factor wb
  have left (u v : Bool) : ra (q u v) = u := (hra u v).symm.trans (ha u v)
  have right (u v : Bool) : rb (q u v) = v := (hrb u v).symm.trans (hb u v)
  have ne01 : q false false ≠ q false true := by
    intro h
    have hh := congrArg rb h
    rw [right false false, right false true] at hh
    cases hh
  have ne10 : q false false ≠ q true false := by
    intro h
    have hh := congrArg ra h
    rw [left false false, left true false] at hh
    cases hh
  have ne12 : q false true ≠ q true false := by
    intro h
    have hh := congrArg ra h
    rw [left false true, left true false] at hh
    cases hh
  cases h0 : q false false <;> cases h1 : q false true <;>
    cases h2 : q true false <;> simp_all

set_option maxHeartbeats 1000000 in
lemma cofactorWitness : ∀ v u : Fin 10, v ≠ u → ∀ val : Bool,
    ∃ w : Fin 10,
      pet (Function.update (Function.update (fun i => decide (i = w)) u val) v false) ≠
      pet (Function.update (Function.update (fun i => decide (i = w)) u val) v true) := by
  decide +kernel

lemma cofactorKeepsOtherInput (v u : Fin 10) (hne : v ≠ u) (val : Bool) :
    ∃ x : Fin 10 → Bool,
      pet (Function.update (Function.update x u val) v false) ≠
      pet (Function.update (Function.update x u val) v true) := by
  obtain ⟨w, hw⟩ := cofactorWitness v u hne val
  exact ⟨fun i => decide (i = w), hw⟩

def vertexPerm (v : Fin 10) : Fin 10 → Fin 10 :=
  (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2]]) v

lemma vertexPerm_bijective : ∀ v : Fin 10, Function.Bijective (vertexPerm v) := by
  decide +kernel

lemma vertexPerm_zero : ∀ v : Fin 10, vertexPerm v 0 = v := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
lemma pet_vertexPerm : ∀ (v : Fin 10) (x : Fin 10 → Bool),
    pet (x ∘ vertexPerm v) = pet x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.PairSeparation
namespace PEqualNP.Outside.L_meta_2592_aux.FirstGate

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation

lemma output_not_input (D : U2Circuit) (hmin : IsMinU2 pet D) (v : Fin 10) (fl : Bool) :
    D.out ≠ Sum.inr (v.val, fl) := by
  intro hout
  obtain ⟨u, hu⟩ : ∃ u : Fin 10, u ≠ v := by
    by_cases hv : v = 0
    · exact ⟨1, by simp [hv]⟩
    · exact ⟨0, Ne.symm hv⟩
  have proj (x : Fin 10 → Bool) : pet x = (x v != fl) := by
    rw [← hmin.2.1 x]
    unfold u2Eval
    rw [hout]
    change (u2Val D.gates x v.val != fl) = _
    rw [u2Val_input D.gates x v.val v.isLt]
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput u v hu false
  rw [proj, proj] at hx
  simp [Function.update_of_ne hu.symm] at hx

lemma gates_pos (D : U2Circuit) (hmin : IsMinU2 pet D) : 0 < D.gates.length := by
  by_contra hn
  have hnil : D.gates = [] := by
    cases hg : D.gates with
    | nil => rfl
    | cons g gs => simp [hg] at hn
  rcases ho : D.out with c | ⟨w, fl⟩
  · have hz := hmin.2.1 (fun _ => false)
    have ht := hmin.2.1 (fun _ => true)
    simp [u2Eval, ho, refEval, pet] at hz ht
    exact Bool.noConfusion (hz.symm.trans ht)
  · have hw : w < 10 := by
      have h := hmin.1.2
      simpa [refWf, ho, hnil] using h
    exact output_not_input D hmin ⟨w, hw⟩ fl ho

lemma first_input_second_reader (D : U2Circuit) (hmin : IsMinU2 pet D)
    (h0 : 0 < D.gates.length) :
    ∃ k, ∃ hk : k < D.gates.length, 0 < k ∧
      (D.gates[k].a = D.gates[0].a ∨ D.gates[k].b = D.gates[0].a) := by
  classical
  let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
  let u : Fin 10 := ⟨D.gates[0].b, by have := (hmin.1.1 0 h0).2; omega⟩
  have hvu : v ≠ u := by
    intro he
    have hv := congrArg Fin.val he
    exact min_no_self hmin 0 h0 hv
  have hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 =
        ((u2Val D.gates x v.val != D.gates[0].pa) &&
         (u2Val D.gates x u.val != D.gates[0].pb)) := by
    intro x
    have h := u2Val_gate D.gates x 0 h0 (hmin.1.1 0 h0).1 (hmin.1.1 0 h0).2
    simpa [v, u] using h
  by_contra hn
  have hno : ∀ k (hk : k < D.gates.length), 0 < k →
      D.gates[k].a ≠ v.val ∧ D.gates[k].b ≠ v.val := by
    intro k hk hpos
    constructor
    · intro he
      exact hn ⟨k, hk, hpos, Or.inl he⟩
    · intro he
      exact hn ⟨k, hk, hpos, Or.inr he⟩
  have hc := single_fanout_first_gate hmin h0 v u D.gates[0].pa D.gates[0].pb
    hvu hg0 (output_not_input D hmin v) hno
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput v u hvu D.gates[0].pb
  exact hx (hc x)

lemma zero_restriction_saves_two (D : U2Circuit) (hmin : IsMinU2 pet D) :
    ∃ (v : Fin 10) (s : ℕ), s + 2 ≤ D.gates.length ∧
      HasU2Size (fun x => pet (Function.update x v false)) s := by
  have h0 := gates_pos D hmin
  obtain ⟨k, hk, hkpos, hread⟩ := first_input_second_reader D hmin h0
  let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
  obtain ⟨s, hs, hsize⟩ := elim_ge_2_two hmin v false 0 k h0 hk (by omega)
    (Or.inl rfl) hread
  exact ⟨v, s, hs, hsize⟩

end PEqualNP.Outside.L_meta_2592_aux.FirstGate

namespace PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGate

lemma zero_cofactor_nonconstant (v : Fin 10) :
    ∃ x y : Fin 10 → Bool, pet (Function.update x v false) ≠
      pet (Function.update y v false) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin 10, u ≠ v := by
    by_cases hv : v = 0
    · exact ⟨1, by simp [hv]⟩
    · exact ⟨0, Ne.symm hv⟩
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput u v hu false
  let x0 := Function.update (Function.update x v false) u false
  let x1 := Function.update (Function.update x v false) u true
  have h0 : Function.update x0 v false = x0 := by
    funext i
    by_cases hi : i = v
    · subst i
      simp [x0, hu.symm]
    · simp [hi]
  have h1 : Function.update x1 v false = x1 := by
    funext i
    by_cases hi : i = v
    · subst i
      simp [x1, hu.symm]
    · simp [hi]
  exact ⟨x0, x1, by simpa [h0, h1, x0, x1] using hx⟩

lemma source_second_reader (D : U2Circuit) (hmin : IsMinU2 pet D)
    (h0 : 0 < D.gates.length) (v u : Fin 10) (pv pu : Bool) (hne : v ≠ u)
    (hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v.val != pv) &&
        (u2Val D.gates x u.val != pu))) :
    ∃ k, ∃ hk : k < D.gates.length, 0 < k ∧
      (D.gates[k].a = v.val ∨ D.gates[k].b = v.val) := by
  classical
  by_contra hn
  have hno : ∀ k (hk : k < D.gates.length), 0 < k →
      D.gates[k].a ≠ v.val ∧ D.gates[k].b ≠ v.val := by
    intro k hk hpos
    constructor
    · intro he
      exact hn ⟨k, hk, hpos, Or.inl he⟩
    · intro he
      exact hn ⟨k, hk, hpos, Or.inr he⟩
  have hc := single_fanout_first_gate hmin h0 v u pv pu hne hg0
    (output_not_input D hmin v) hno
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput v u hne pu
  exact hx (hc x)

def ZeroFloor : Prop :=
  ∀ (v : Fin 10) (s : ℕ), HasU2Size (fun x => pet (Function.update x v false)) s → 15 ≤ s

lemma opposite_impossible (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) (v : Fin 10) (p : Bool)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = p) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = p))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j)
    (hr1 : (D.gates[j].a = v.val ∧ D.gates[j].pa = !p) ∨
      (D.gates[j].b = v.val ∧ D.gates[j].pb = !p)) : False := by
  obtain ⟨s, hs, hc⟩ := elim_ge_3_opp hmin h0 v p hr0 j hj hpos hr1 false
    (zero_cofactor_nonconstant v)
  have hf := floor v s hc
  omega

lemma same_positive_impossible (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 17)
    (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = false) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = false))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j)
    (hr1 : (D.gates[j].a = v.val ∧ D.gates[j].pa = false) ∨
      (D.gates[j].b = v.val ∧ D.gates[j].pb = false)) : False := by
  obtain ⟨s, hs, hc⟩ := elim_ge_4_same hmin h0 v false hr0 j hj hpos hr1
    (zero_cofactor_nonconstant v)
  have hf := floor v s hc
  omega

lemma source_negative (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length)
    (v u : Fin 10) (pv pu : Bool) (hne : v ≠ u)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = pv) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = pv))
    (hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v.val != pv) &&
        (u2Val D.gates x u.val != pu))) : pv = true := by
  cases pv
  · obtain ⟨j, hj, hpos, hr⟩ := source_second_reader D hmin h0 v u false pu hne hg0
    exfalso
    rcases hr with ha | hb
    · cases hp : D.gates[j].pa
      · exact same_positive_impossible floor D hmin small h0 v hr0 j hj hpos
          (Or.inl ⟨ha, hp⟩)
      · exact opposite_impossible floor D hmin small h0 v false hr0 j hj hpos
          (Or.inl ⟨ha, hp⟩)
    · cases hp : D.gates[j].pb
      · exact same_positive_impossible floor D hmin small h0 v hr0 j hj hpos
          (Or.inr ⟨hb, hp⟩)
      · exact opposite_impossible floor D hmin small h0 v false hr0 j hj hpos
          (Or.inr ⟨hb, hp⟩)
  · rfl

lemma first_gate_negative (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true := by
  let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
  let u : Fin 10 := ⟨D.gates[0].b, by have := (hmin.1.1 0 h0).2; omega⟩
  have hne : v ≠ u := by
    intro he
    exact min_no_self hmin 0 h0 (congrArg Fin.val he)
  have hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v.val != D.gates[0].pa) &&
        (u2Val D.gates x u.val != D.gates[0].pb)) := by
    intro x
    have h := u2Val_gate D.gates x 0 h0 (hmin.1.1 0 h0).1 (hmin.1.1 0 h0).2
    simpa [v, u] using h
  constructor
  · exact source_negative floor D hmin small h0 v u D.gates[0].pa D.gates[0].pb hne
      (Or.inl ⟨rfl, rfl⟩) hg0
  · apply source_negative floor D hmin small h0 u v D.gates[0].pb D.gates[0].pa hne.symm
      (Or.inr ⟨rfl, rfl⟩)
    intro x
    rw [hg0 x, Bool.and_comm]

lemma later_source_negative (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = true) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = true))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j) :
    (D.gates[j].a = v.val → D.gates[j].pa = true) ∧
    (D.gates[j].b = v.val → D.gates[j].pb = true) := by
  constructor
  · intro ha
    cases hp : D.gates[j].pa
    · exact False.elim (opposite_impossible floor D hmin small h0 v true hr0 j hj hpos
        (Or.inl ⟨ha, hp⟩))
    · rfl
  · intro hb
    cases hp : D.gates[j].pb
    · exact False.elim (opposite_impossible floor D hmin small h0 v true hr0 j hj hpos
        (Or.inr ⟨hb, hp⟩))
    · rfl

lemma first_sources_negative_everywhere (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true ∧
    ∀ j (hj : j < D.gates.length),
      (D.gates[j].a = D.gates[0].a → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].a → D.gates[j].pb = true) ∧
      (D.gates[j].a = D.gates[0].b → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].b → D.gates[j].pb = true) := by
  obtain ⟨ha, hb⟩ := first_gate_negative floor D hmin small h0
  refine ⟨ha, hb, ?_⟩
  intro j hj
  by_cases hz : j = 0
  · subst j
    exact ⟨fun _ => ha, fun _ => hb, fun _ => ha, fun _ => hb⟩
  · let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
    let u : Fin 10 := ⟨D.gates[0].b, by have := (hmin.1.1 0 h0).2; omega⟩
    have hv := later_source_negative floor D hmin small h0 v (Or.inl ⟨rfl, ha⟩) j hj
      (by omega)
    have hu := later_source_negative floor D hmin small h0 u (Or.inr ⟨rfl, hb⟩) j hj
      (by omega)
    exact ⟨hv.1, hv.2, hu.1, hu.2⟩

end PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

namespace PEqualNP.Outside.L_meta_2592_aux.ReadBudget

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

def readers (D : U2Circuit) (v : Fin 10) : Finset (Fin D.gates.length) :=
  Finset.univ.filter fun j => D.gates[j.val].a = v.val ∨ D.gates[j.val].b = v.val

lemma reader_bound (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (v : Fin 10) : (readers D v).card + 15 ≤ D.gates.length := by
  obtain ⟨hwf, hev, hlen, hEv, _⟩ := restrictU2_spec D hmin.1 v false
  have hc : HasU2Size (fun x => pet (Function.update x v false))
      (restrictU2 D v false).gates.length :=
    ⟨restrictU2 D v false, hwf, le_rfl, fun x => (hev x).trans (hmin.2.1 _)⟩
  have hf := floor v _ hc
  have hs : readers D v ⊆ elimSet D v false := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with ha | hb
    · left
      rw [ha, hEv]
      rfl
    · right
      rw [hb, hEv]
      rfl
  have hcard := Finset.card_le_card hs
  omega

lemma at_most_two_readers (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (v : Fin 10) : (readers D v).card ≤ 2 := by
  have h := reader_bound floor D hmin v
  omega

lemma at_most_three_readers (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 18) (v : Fin 10) : (readers D v).card ≤ 3 := by
  have h := reader_bound floor D hmin v
  omega

lemma repeated_positive_impossible (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 18)
    (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = false) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = false))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j)
    (hr1 : (D.gates[j].a = v.val ∧ D.gates[j].pa = false) ∨
      (D.gates[j].b = v.val ∧ D.gates[j].pb = false)) : False := by
  obtain ⟨s, hs, hc⟩ := elim_ge_4_same hmin h0 v false hr0 j hj hpos hr1
    (zero_cofactor_nonconstant v)
  have hf := floor v s hc
  omega

lemma positive_first_later_negative (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 18)
    (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = false) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = false))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j) :
    (D.gates[j].a = v.val → D.gates[j].pa = true) ∧
    (D.gates[j].b = v.val → D.gates[j].pb = true) := by
  constructor
  · intro ha
    cases hp : D.gates[j].pa
    · exact False.elim (repeated_positive_impossible floor D hmin small h0 v hr0 j hj hpos
        (Or.inl ⟨ha, hp⟩))
    · rfl
  · intro hb
    cases hp : D.gates[j].pb
    · exact False.elim (repeated_positive_impossible floor D hmin small h0 v hr0 j hj hpos
        (Or.inr ⟨hb, hp⟩))
    · rfl

end PEqualNP.Outside.L_meta_2592_aux.ReadBudget

namespace PEqualNP.Outside.L_meta_2592_aux.ReadBudget

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

lemma reader_bound_of_compute (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (v : Fin 10) :
    (readers D v).card + 15 ≤ D.gates.length := by
  obtain ⟨hwf', hev, hlen, hEv, _⟩ := restrictU2_spec D hwf v false
  have hc : HasU2Size (fun x => pet (Function.update x v false))
      (restrictU2 D v false).gates.length :=
    ⟨restrictU2 D v false, hwf', le_rfl, fun x => (hev x).trans (computes _)⟩
  have hf := floor v _ hc
  have hs : readers D v ⊆ elimSet D v false := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with ha | hb
    · left
      rw [ha, hEv]
      rfl
    · right
      rw [hb, hEv]
      rfl
  have hcard := Finset.card_le_card hs
  omega

lemma at_most_two_readers_of_compute (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (small : D.gates.length ≤ 17) (v : Fin 10) :
    (readers D v).card ≤ 2 := by
  have h := reader_bound_of_compute floor D hwf computes v
  omega

end PEqualNP.Outside.L_meta_2592_aux.ReadBudget

namespace PEqualNP.Outside.L_meta_2592_aux.Promotion

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGate
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

lemma binary_floor_of_compute (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) : 17 ≤ D.gates.length := by
  have hsize : HasU2Size pet D.gates.length := ⟨D, hwf, le_rfl, computes⟩
  obtain ⟨M, hm, hle⟩ := exists_minU2 hsize
  obtain ⟨v, s, hs, hc⟩ := zero_restriction_saves_two M hm
  have hf := floor v s hc
  omega

lemma minimal_of_cap17 (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (small : D.gates.length ≤ 17) :
    IsMinU2 pet D := by
  refine ⟨hwf, computes, ?_⟩
  intro M hm hc
  have hf := binary_floor_of_compute floor M hm hc
  omega

lemma first_sources_negative_any (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (small : D.gates.length ≤ 17)
    (h0 : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true ∧
    ∀ j (hj : j < D.gates.length),
      (D.gates[j].a = D.gates[0].a → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].a → D.gates[j].pb = true) ∧
      (D.gates[j].a = D.gates[0].b → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].b → D.gates[j].pb = true) :=
  first_sources_negative_everywhere floor D (minimal_of_cap17 floor D hwf computes small)
    small h0

end PEqualNP.Outside.L_meta_2592_aux.Promotion
